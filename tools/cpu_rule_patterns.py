#!/usr/bin/env python3
"""Executable applicability checks (PATTERNS) of the reuse rule library framework/rule-library.json.

Every rule of the library names one function `p_<name>` of this module.  A pattern gets a `Ctx` (the imported AST of the design,
its signal table / frontend report / Verilator XML, and the design manifest WITHOUT its `route` section) and returns
  None                         the rule does not apply, or
  dict(evidence=..., **bind)   the rule applies; `bind` are the values the driver needs to instantiate it (option values,
                               ids, variant).  `evidence` is a short human-readable reason.
Patterns never read the hand-written `route` section of the manifest (Ctx.man has it removed), so that the matcher
(tools/cpu_rule_match.py, `cpu_tmpl_route.py --match-rules`) RE-DERIVES the route instead of copying it.
Patterns are untrusted heuristics: a wrong match can only produce a module that Coq then rejects.
proof_author: LLM-generated: Claude Code (claude-opus-5-5); external_llm_api_calls=0.
"""
import json
import os
import re
import xml.etree.ElementTree as ET
from functools import cached_property
from pathlib import Path

import cpu_ast_sim as sim

ROOT = Path(__file__).resolve().parent.parent
PROFILE = ROOT / 'framework' / 'auto-contract-profiles'
AUTHOR = 'LLM-generated: Claude Code (claude-opus-5-5)'
# frontend report / Verilator XML of each design's imported AST (the AST file itself comes from the manifest)
GENERATED = {
    'bzeeno': 'experiments/framework/generated/bzeeno-load-use-jal',
    'darkriscv': 'experiments/framework/generated/dark38-derived',
    'steel': 'experiments/framework/generated/steel',
    'srv32': 'experiments/framework/generated/srv32',
    'nerv': 'experiments/framework/generated/nerv-lit',
    'angelo5fix': 'experiments/framework/generated/angelo5-fixed',
}
# the phase-A import whose XML the frontend rules look at (NERV: the literal-index AST is derived from the plain import)
XML_DIR = dict(GENERATED, nerv='experiments/framework/generated/nerv')


# ------------------------------------------------------------------ AST helpers (tuple form of cpu_ast_sim.parse_ast_file)
def stmts(s):
    """all statements of a statement tree (pre-order)"""
    yield s
    k = s[0]
    if k == 'SSeq':
        for c in s[1]:
            yield from stmts(c)
    elif k == 'SIf':
        yield from stmts(s[2])
        yield from stmts(s[3])
    elif k == 'SCase':
        for _, b in s[2]:
            yield from stmts(b)


def exprs(e):
    yield e
    k = e[0]
    if k in ('EConst', 'EVar'):
        return
    if k in ('ESel', 'EConcat'):
        yield from exprs(e[2]); yield from exprs(e[3])
    elif k in ('EReplicate', 'EExtend', 'EUnary'):
        yield from exprs(e[3])
    elif k == 'EBinary':
        yield from exprs(e[3]); yield from exprs(e[4])
    elif k == 'ECond':
        yield from exprs(e[2]); yield from exprs(e[3]); yield from exprs(e[4])


def evar_ids(e):
    return {x[2] for x in exprs(e) if x[0] == 'EVar'}


def lv_root(lv):
    while lv[0] == 'LSel':
        lv = lv[2]
    return lv[2]


def lv_indices(lv):
    out = []
    while lv[0] == 'LSel':
        out.append(lv[3])
        lv = lv[2]
    return out


def stmt_exprs(s):
    """expressions read directly by statement s (not its children)"""
    k = s[0]
    if k == 'SAssign':
        return [s[2]] + lv_indices(s[3])
    if k == 'SIf':
        return [s[1]]
    if k == 'SCase':
        return [s[1]] + [key for key, _ in s[2] if key is not None]
    return []


def assigns(body):
    return [s for s in stmts(body) if s[0] == 'SAssign']


def is_rebased_index(e):
    """(x - 1) * 32 with x a non-constant (Verilator rebasing of a [31:1] bank), possibly inside an ESel/extend"""
    for x in exprs(e):
        if x[0] == 'EBinary' and x[2] == 'BMul' and x[4][0] == 'EConst' and x[4][2] == 32:
            a = x[3]
            if a[0] == 'EBinary' and a[2] == 'BSub' and a[4][0] == 'EConst' and a[4][2] == 1:
                return True
    return False


def top_ifs(body):
    """the statement list below the process wrapper SSeq [SSeq [...]] (or SSeq [...])"""
    b = body
    while b[0] == 'SSeq' and len(b[1]) == 1 and b[1][0][0] == 'SSeq':
        b = b[1][0]
    return b[1] if b[0] == 'SSeq' else [b]


class Ctx:
    """Everything a pattern may look at for one design (read-only)."""

    def __init__(self, design):
        self.design = design
        full = json.loads((PROFILE / f'{design}.json').read_text())
        self.man = {k: v for k, v in full.items() if k != 'route'}     # the route is what we re-derive
        self.pr = self.man.get('pipeline_roles', {})
        self.tr = self.man.get('template_roles', {})
        ast = self.pr['ast']
        self.ast_file = ROOT / ast['file']
        self.ast_module = ast['module']
        self.prog = sim.parse_ast_file(str(self.ast_file))
        self.procs = self.prog['processes']
        self.nsig = self.prog['signal_count']
        gdir = ROOT / GENERATED.get(design, Path(ast['signal_table']).parent)
        rep = gdir / 'report.json'
        self.report = json.loads(rep.read_text()) if rep.exists() else {}
        st = ROOT / ast.get('signal_table', str(rep))
        self.sigtab = {r['id']: r for r in json.loads(st.read_text()).get('signal_table', [])} if st.exists() else {}
        xd = ROOT / XML_DIR.get(design, gdir)
        xs = sorted(xd.glob('elaborated.xml')) + sorted(xd.glob('*/elaborated.xml'))
        self.xml_file = xs[0] if xs else None

    # ---------------------------------------------------------------- derived views
    @cached_property
    def seq(self):
        return [i for i, p in enumerate(self.procs) if p['kind'] == 'Sequential']

    @cached_property
    def comb(self):
        return [i for i, p in enumerate(self.procs) if p['kind'] == 'Combinational']

    @cached_property
    def comb_assign(self):
        """root -> list of (process, rhs) of single-assignment combinational processes (copy-chain tracing)"""
        out = {}
        for i in self.comb:
            b = self.procs[i]['body']
            if b[0] == 'SAssign' and b[3][0] == 'LVar':
                out.setdefault(b[3][2], []).append((i, b[2]))
        return out

    @cached_property
    def writers(self):
        """root -> set of process indices writing it"""
        out = {}
        for i, p in enumerate(self.procs):
            for s in assigns(p['body']):
                out.setdefault(lv_root(s[3]), set()).add(i)
        return out

    @cached_property
    def seq_regs(self):
        return {r for r, ps in self.writers.items() if any(self.procs[i]['kind'] == 'Sequential' for i in ps)}

    def events_of(self, i):
        return self.procs[i].get('events', [])

    @cached_property
    def primary(self):
        ev = self.pr.get('events') or self.tr.get('events') or {}
        return ev.get('clock', {}).get('id'), ev.get('reset', {}).get('id')

    def trace(self, s, limit=64):
        """follow single-assignment copy / not chains back to a source: (source, inverted) or (s, 0) if not a chain"""
        inv = 0
        for _ in range(limit):
            if s in self.primary:
                return s, inv
            c = self.comb_assign.get(s)
            if not c or len(c) != 1:
                return s, inv
            r = c[0][1]
            if r[0] == 'EVar':
                s = r[2]
            elif r[0] == 'EUnary' and r[2] == 'UNot' and r[3][0] == 'EVar' and r[1] == 1:
                inv ^= 1; s = r[3][2]
            else:
                return s, inv
        return s, inv

    @cached_property
    def comb_deps(self):
        """root -> set of signals read by its combinational writers (all statements of the writing processes)"""
        out = {}
        for i in self.comb:
            body = self.procs[i]['body']
            rd = set()
            for s in stmts(body):
                for e in stmt_exprs(s):
                    rd |= evar_ids(e)
            for s in assigns(body):
                out.setdefault(lv_root(s[3]), set()).update(rd)
        return out

    def cone_of(self, roots):
        """signals combinationally reachable FROM roots (forward cone)"""
        fwd = {}
        for r, ds in self.comb_deps.items():
            for d in ds:
                fwd.setdefault(d, set()).add(r)
        seen, todo = set(roots), list(roots)
        while todo:
            x = todo.pop()
            for y in fwd.get(x, ()):
                if y not in seen:
                    seen.add(y); todo.append(y)
        return seen

    @cached_property
    def instruction_word(self):
        for path in (('template_roles', 'instruction_word', 'word', 'id'), ('pipeline_roles', 'fetch_slot', 'word', 'id'),
                     ('template_roles', 'decoder', 'word', 'id'), ('template_roles', 'fetch_slot', 'word', 'id')):
            v = self.man
            try:
                for k in path:
                    v = v[k]
                return v
            except (KeyError, TypeError):
                continue
        return None

    @cached_property
    def decode_cone(self):
        w = self.instruction_word
        return self.cone_of([w]) if w is not None else set()

    @cached_property
    def xml(self):
        return ET.parse(self.xml_file).getroot() if self.xml_file else None

    def expected_fire(self, edge_new_clk, rst_level):
        """sequential processes firing on a primary-clock edge with the primary reset at rst_level (same rule as cpu_tmpl_edge.expected)"""
        clk0, rst0 = self.primary
        out = []
        for i in self.seq:
            fire = False
            for kind, sig in self.events_of(i):
                src, inv = self.trace(sig)
                if src != clk0:
                    continue
                old, new = (1 - edge_new_clk) ^ inv, edge_new_clk ^ inv
                if (kind == 'Posedge' and old == 0 and new == 1) or (kind == 'Negedge' and old == 1 and new == 0):
                    fire = True
            out.append(i) if fire else None
        return out


# ------------------------------------------------------------------ reset polarity (shared by several patterns)
def reset_polarity(ctx):
    """('high'|'low', evidence).  Rule: a reset input that appears as a Negedge event of a sequential process (through copy
    chains) is active-low; otherwise look at the first if-test of the sequential processes that depends on the primary
    reset only through copies / OR with a reset flop: if its then-branch assigns only constants the reset is active when the
    test is 1 (active-high if the test equals the input, active-low if it is the inverted input)."""
    clk0, rst0 = ctx.primary
    for i in ctx.seq:
        for kind, sig in ctx.events_of(i):
            src, inv = ctx.trace(sig)
            if src == rst0:
                lvl = 'low' if (kind == 'Negedge') ^ inv else 'high'
                return lvl, f'reset input {rst0} is an asynchronous {kind} event of process_{i} (inverted {inv})'

    def pol(sig, depth=0):
        """polarity of a 1-bit signal w.r.t. the primary reset: +1 (follows it), -1 (inverted), None"""
        if sig == rst0:
            return 1
        if depth > 32:
            return None
        c = ctx.comb_assign.get(sig)
        if not c or len(c) != 1:
            return None
        return pol_e(c[0][1], depth + 1)

    def pol_e(e, depth):
        k = e[0]
        if k == 'EVar':
            return pol(e[2], depth)
        if k == 'EUnary' and e[2] == 'UNot':
            p = pol_e(e[3], depth)
            return -p if p else None
        if k == 'EBinary' and e[2] in ('BOr', 'BAnd'):
            a, b = pol_e(e[3], depth), pol_e(e[4], depth)
            return a or b
        if k == 'EBinary' and e[2] in ('BEq', 'BNeq') and e[4][0] == 'EConst':
            p = pol_e(e[3], depth)
            if p is None:
                return None
            flip = (e[2] == 'BEq') == (e[4][2] == 0)
            return -p if flip else p
        return None

    def const_only(s):
        return all(a[2][0] == 'EConst' for a in assigns(s)) and any(True for _ in assigns(s))

    votes = []
    for i in ctx.seq:
        for s in stmts(ctx.procs[i]['body']):
            if s[0] != 'SIf':
                continue
            p = pol_e(s[1], 0)
            if p is None:
                continue
            if const_only(s[2]):
                votes.append(('high' if p > 0 else 'low', i))
            elif const_only(s[3]):
                votes.append(('low' if p > 0 else 'high', i))
            break
    if not votes:
        return None, 'no reset test found'
    hi = sum(1 for v, _ in votes if v == 'high')
    lvl = 'high' if hi * 2 > len(votes) else 'low'
    return lvl, f'{len(votes)} synchronous reset tests ({hi} active-high), e.g. process_{votes[0][1]}'


# ================================================================== patterns: frontend normalizations
def p_fe_rebased_bank(ctx):
    """register file is a 31-lane bank `[31:1]` indexed `addr-1`: every bank access is (x-1)*32 (rebased, padded to 32 lanes)"""
    banks = {}
    for i, p in enumerate(ctx.procs):
        for s in stmts(p['body']):
            if s[0] == 'SAssign' and s[3][0] == 'LSel' and s[3][1] == 32 and any(is_rebased_index(x) for x in lv_indices(s[3])):
                banks.setdefault(lv_root(s[3]), set()).add(('w', i))
            for e in stmt_exprs(s):
                for x in exprs(e):
                    if x[0] == 'ESel' and x[1] == 32 and x[2][0] == 'EVar' and x[2][1] >= 1024 and is_rebased_index(x[3]):
                        banks.setdefault(x[2][2], set()).add(('r', i))
    banks = {b: v for b, v in banks.items() if any(k == 'w' for k, _ in v) and any(k == 'r' for k, _ in v)}
    if not banks:
        return None
    return dict(evidence=f'bank(s) {sorted(banks)} written and read at (x-1)*32', banks=sorted(banks), rebase=1, padded_lanes=32)


def _xml_count(ctx, pred):
    if ctx.xml is None:
        return 0
    return sum(1 for n in ctx.xml.iter() if pred(n))


def p_fe_while_unroll(ctx):
    """Verilator left a constant-trip `while` loop (e.g. `for (i=1;i<32;i++) regs[i] <= 0`) in --xml-only output"""
    n = _xml_count(ctx, lambda n: n.tag == 'while')
    rep = ctx.report.get('unrolled_loops') or ctx.report.get('loops_unrolled')
    if not n and not rep:
        return None
    return dict(evidence=f'{n} <while> in the XML; frontend report unrolled {rep}', loops=n)


def p_fe_x_to_zero(ctx):
    """x literals (don't-care constants such as 32'hx) in the elaborated design"""
    rx = re.compile(r"^\d+'[bh][0-9a-fA-F_]*x[0-9a-fA-Fx_]*$")
    n = _xml_count(ctx, lambda n: n.tag == 'const' and rx.match(n.get('name', '') or ''))
    if not n:
        return None
    return dict(evidence=f'{n} x constants in the XML (frontend rewrites them to 0; every use must be guarded)', constants=n)


def p_fe_casez(ctx):
    """casez items with z (wildcard) bits"""
    rx = re.compile(r"^\d+'b[01xz?]*[z?][01xz?]*$")
    n = _xml_count(ctx, lambda n: n.tag == 'const' and rx.match(n.get('name', '') or ''))
    if not n:
        return None
    return dict(evidence=f'{n} wildcard constants (casez items) in the XML', items=n)


def p_fe_generate_instances(ctx):
    """module instances nested inside generate blocks (missed by Element.findall('instance'))"""
    if ctx.xml is None:
        return None
    nested = 0
    for m in ctx.xml.iter('module'):
        direct = len(m.findall('instance'))
        nested += len(list(m.iter('instance'))) - direct
    if not nested:
        return None
    return dict(evidence=f'{nested} instance(s) below a generate block', nested=nested)


def p_fe_literal_index(ctx):
    """unrolled loops whose body writes a packed part-select at an offset depending on the loop counter (lv_static needs literals)"""
    if ctx.xml is None:
        return None
    hits = 0
    for w in ctx.xml.iter('while'):
        for a in w.iter():
            if a.tag in ('assign', 'assigndly'):
                kids = list(a)
                if len(kids) == 2 and kids[1].tag == 'sel' and any(x.tag == 'varref' for x in list(kids[1])[1:2] for x in x.iter()):
                    hits += 1
    rep = ctx.report.get('counter_reads_replaced_by_literals')
    if not hits and not rep:
        return None
    return dict(evidence=f'{hits} variable-offset packed writes inside while loops; report counter reads replaced {rep}', writes=hits)


# ================================================================== patterns: LFP / edge / reset / stage layers
def _comb_nba(ctx):
    return [i for i in ctx.comb if any(s[1] for s in assigns(ctx.procs[i]['body']))]


def _wide_cases(ctx, limit=16):
    """case statements whose scrutinee is wider than `limit` bits: ExtendedSVBitStability.exhaustive enumerates 2^w values
    under vm_compute (andb/orb are strict), even when a default arm exists"""
    return [(i, s[1][1]) for i in ctx.comb for s in stmts(ctx.procs[i]['body']) if s[0] == 'SCase' and s[1][1] > limit]


def p_lfp_nolatch_cert(ctx):
    """combinational processes are blocking-only: all-states bit-mask certificate (ExtendedSVBitStabilityNoLatch) with N = lfp_fuel"""
    if _comb_nba(ctx):
        return None
    n = ctx.prog['lfp_fuel']
    lazy = bool(_wide_cases(ctx))
    return dict(evidence=f'{len(ctx.comb)} blocking-only comb processes, lfp_fuel {n}', rounds=n,
                extra_args=(['--rounds', str(n)] if n != 1 else []), generator=('tools/cpu_tmpl_lfpnl_lazy.py' if lazy else 'tools/cpu_tmpl_lfpnl.py'))


def p_lfp_lazy_exhaustive(ctx):
    """a comb `case` on a scrutinee wider than 16 bits (unrolled `for` loops): the strict `exhaustive` would enumerate 2^w"""
    w = _wide_cases(ctx)
    if not w or _comb_nba(ctx):
        return None
    return dict(evidence=f'{len(w)} wide case scrutinees, e.g. process_{w[0][0]} width {w[0][1]}', cases=len(w))


def p_edge_derived_clock(ctx):
    """every sequential event signal is a copy / inversion chain of the primary clock or reset input"""
    clk0, rst0 = ctx.primary
    if clk0 is None or not ctx.seq:
        return None
    bad = [(i, s) for i in ctx.seq for _, s in ctx.events_of(i) if ctx.trace(s)[0] not in (clk0, rst0)]
    if bad:
        return None
    derived = sorted({s for i in ctx.seq for _, s in ctx.events_of(i) if s not in (clk0, rst0)})
    return dict(evidence=f'{len(ctx.seq)} sequential processes; event nets {derived or "primary only"} trace to inputs {clk0}/{rst0}',
                derived_nets=derived, sequential=len(ctx.seq))


EDGE_FILTER_COST = 3000   # n_seq * n_processes above which `cbn [filter]` in the sel_* lemmas is slow (calibrated, see rule)


def p_edge_fast_filter(ctx):
    """the sel_* selection lemmas filter the whole process list once per sequential process: cost ~ n_seq * n_processes"""
    cost = len(ctx.seq) * len(ctx.procs)
    if cost < EDGE_FILTER_COST:
        return None
    return dict(evidence=f'{len(ctx.seq)} sequential x {len(ctx.procs)} processes = {cost} >= {EDGE_FILTER_COST}', cost=cost)


def p_reset_level(ctx):
    """primary reset polarity -> level of the reset input in operation (route field rst_idle / env TMPL_RST_IDLE)"""
    lvl, ev = reset_polarity(ctx)
    if lvl is None:
        return None
    return dict(evidence=f'active-{lvl} reset: {ev}', polarity=lvl, rst_idle=(0 if lvl == 'high' else 1))


def p_reset_events_layer(ctx):
    """the reset input is an event of sequential processes (asynchronous reset): the boot needs selection lemmas for the
    reset edges and for clock edges at the asserted reset level (cpu_tmpl_edge.py --reset-events)"""
    clk0, rst0 = ctx.primary
    asy = sorted({i for i in ctx.seq for _, s in ctx.events_of(i) if ctx.trace(s)[0] == rst0})
    if not asy:
        return None
    return dict(evidence=f'{len(asy)} sequential processes have the reset input as an event (async reset)', processes=asy)


def _inner(ctx, i):
    b = ctx.procs[i]['body']
    flat = not (b[0] == 'SSeq' and len(b[1]) == 1 and b[1][0][0] == 'SSeq')
    return flat, (b[1] if flat else b[1][0][1])


def p_stage_seqtree(ctx):
    """some sequential process firing on the rise is ONE decision tree with NBA leaves (ExtendedSVSeqTree.conv)"""
    import cpu_tmpl_stage as S
    rise = ctx.expected_fire(1, _rst_idle(ctx))
    conv = [i for i in rise if len(_inner(ctx, i)[1]) == 1 and S.convertible(_inner(ctx, i)[1][0])]
    if not conv:
        return None
    return dict(evidence=f'{len(conv)} of {len(rise)} rising processes are single decision trees', convertible=conv,
                not_convertible=[i for i in rise if i not in conv])


def p_seqtree_flat(ctx):
    """a sequential process body is SSeq [t] (no inner SSeq wrapper): ExtendedSVSeqTreeFlat"""
    fl = [i for i in ctx.seq if _inner(ctx, i)[0]]
    return dict(evidence=f'flat bodies: processes {fl}', processes=fl) if fl else None


def _multi_tree(ctx, i):
    flat, inner = _inner(ctx, i)
    if len(inner) != 1 or inner[0][0] != 'SIf':
        return None
    for br in (inner[0][2], inner[0][3]):
        if br[0] == 'SSeq' and len(br[1]) > 1 and any(x[0] == 'SIf' for x in br[1]):
            return len(br[1])
    return None


def p_seqtree2(ctx):
    """process has several decision trees below the reset test (ExtendedSVSeqTree2, ordered multi-writer semantics)"""
    pr = [i for i in ctx.seq if _multi_tree(ctx, i)]
    if not pr:
        return None
    sl = [i for i in pr if any(a[3][0] == 'LSel' for a in assigns(ctx.procs[i]['body']))]
    return dict(evidence=f'multi-tree processes {pr} (part-select writers {sl})', processes=pr, slice_processes=sl)


def p_seqtree2_slice(ctx):
    """a multi-tree process writes part-selects (bit slices) of a register: ExtendedSVSeqTree2Slice (lastws)"""
    m = p_seqtree2(ctx)
    return dict(evidence=f'part-select writers in multi-tree processes {m["slice_processes"]}', processes=m['slice_processes']) if m and m['slice_processes'] else None


def p_nb_override(ctx):
    """sequential body with several statements next to each other (`x <= y; if (r) x <= 0`, guarded lane writes):
    the NBA symbolic executor ExtendedSVSymExecNb"""
    pr = []
    for i in ctx.seq:
        flat, inner = _inner(ctx, i)
        if len(inner) > 1 and any(x[0] == 'SIf' for x in inner):
            pr.append(i)
    return dict(evidence=f'multi-statement sequential bodies with ifs: {pr}', processes=pr) if pr else None


def p_frame_fall_hold(ctx):
    """some registers are written by no process firing on the falling clock edge: frame lemmas over the fall phase"""
    fall = ctx.expected_fire(0, _rst_idle(ctx))
    return dict(evidence=f'{len(fall)} sequential processes fire on the fall', fall=fall)


def _rst_idle(ctx):
    r = p_reset_level(ctx)
    return r['rst_idle'] if r else 1


# ================================================================== patterns: register file
def rf_info(ctx):
    """(bank id, write process index) from the manifest roles"""
    for path in (('pipeline_roles', 'rf_write'), ('template_roles', 'register_file'), ('template_roles', 'rf')):
        v = ctx.man
        try:
            for k in path:
                v = v[k]
        except (KeyError, TypeError):
            continue
        bank = v.get('bank', {}).get('id') if isinstance(v.get('bank'), dict) else None
        proc = v.get('process') or v.get('write_process')
        if bank is not None and isinstance(proc, str):
            return bank, int(proc.split('_')[1])
    return None, None


def rf_shape(ctx):
    bank, pi = rf_info(ctx)
    if bank is None:
        return None
    flat, inner = _inner(ctx, pi)
    lane_writes = [a for a in assigns(ctx.procs[pi]['body']) if lv_root(a[3]) == bank and a[3][0] == 'LSel']
    rebased = any(is_rebased_index(x) for a in lane_writes for x in lv_indices(a[3]))
    shape = None
    if len(inner) == 2 and all(x[0] == 'SIf' for x in inner) and any(lv_root(a[3]) == bank for a in assigns(inner[0][2])):
        shape = 'rf2_guard_first'            # SSeq [SIf g {bank[..] <= e}; SIf c2 {other NBAs}]
    elif len(inner) == 1 and inner[0][0] == 'SIf':
        th, el = inner[0][2], inner[0][3]
        th_bank = [a for a in assigns(th) if lv_root(a[3]) == bank]
        if th_bank and all(a[2][0] == 'EConst' for a in th_bank) and len(th_bank) >= 16:
            shape = 'reset_first'            # if reset {constant lane writes} else if we {bank[..] <= wb}
        elif th[0] == 'SIf' and any(lv_root(a[3]) == bank for a in assigns(th[2])):
            shape = 'blk1'                   # if resetn {if guard {bank[..] <= e}} else {reset}
    elif all(x[0] == 'SAssign' for x in inner) and any(lv_root(x[3]) == bank for x in inner):
        shape = 'unconditional_lane'         # Dark: bank[idx*32] <= v among other NBAs
    elif len(inner) > 1:
        shape = 'multi_statement'
    return dict(bank=bank, process=pi, rebased=rebased, shape=shape, lane_writes=len(lane_writes))


def p_rf_plain_bank(ctx):
    """zero-based register bank (lane = idx), written at idx*32 / idx<<5 (ExtendedSVBankWriteStep / BankOperand)"""
    r = rf_shape(ctx)
    if not r or r['rebased'] or r['shape'] not in ('unconditional_lane', 'blk1'):
        return None
    return dict(evidence=f"bank {r['bank']} written by process_{r['process']} ({r['shape']}, zero-based)", **r)


def p_rf_rebased_bank(ctx):
    """register file is a 31-lane bank indexed `addr-1` (lane j = x(j+1), pad lane 31): ExtendedSVBankRebase RFRelR"""
    r = rf_shape(ctx)
    if not r or not r['rebased']:
        return None
    return dict(evidence=f"bank {r['bank']} rebased, write shape {r['shape']} (process_{r['process']})", variant=r['shape'], **r)


def p_bank_write_blk(ctx):
    """bank slice write wrapped in a block under reset/guard (`if resetn {if guard {bank[..] <= e}}`): ExtendedSVBankWriteBlk"""
    r = rf_shape(ctx)
    return dict(evidence=f"bank {r['bank']} blk1 write (process_{r['process']})", **r) if r and r['shape'] == 'blk1' else None


def p_rebased_operand_ports(ctx):
    """forwarded zero-muxed read port of a rebased bank: `rs == 0 ? 0 : (FWD ? X : bank[(rs-1)*32 +: 32])`; derives the
    route field operands = {bank, ports: [{dst, rs}]} (operand_clause_rebased in register-relation shape)"""
    r = rf_shape(ctx)
    if not r or not r['rebased']:
        return None
    ports = []
    for root, ws in sorted(ctx.comb_assign.items()):
        if len(ws) != 1:
            continue
        e = ws[0][1]
        if not (e[0] == 'ECond' and e[1] == 32 and e[3][0] == 'EConst' and e[3][2] == 0 and e[4][0] == 'ECond'):
            continue
        c = e[2]
        if not (c[0] == 'EBinary' and c[2] == 'BEq' and c[3][0] == 'EConst' and c[3][2] == 0 and c[4][0] == 'EVar' and c[4][1] == 5):
            continue
        bank_arm = e[4][4]
        if bank_arm[0] == 'ESel' and bank_arm[2][0] == 'EVar' and bank_arm[2][2] == r['bank'] and is_rebased_index(bank_arm[3]):
            ports.append(dict(dst=root, rs=c[4][2]))
    if not ports:
        return None
    return dict(evidence=f"forwarded zero-muxed rebased ports {[p['dst'] for p in ports]} of bank {r['bank']}", operands=dict(bank=r['bank'], ports=ports))


def p_rf_rebased_reset_first(ctx):
    """rebased bank written `if reset {31 constant lane writes} else if we {bank[(rd-1)*32 +: 32] <= wb}` (reset-first shape)"""
    r = rf_shape(ctx)
    return dict(evidence=f"bank {r['bank']} rebased reset-first write (process_{r['process']})", **r) if r and r['rebased'] and r['shape'] == 'reset_first' else None


def p_ram_hold_role(ctx):
    """the manifest has a RAM role (array written only by a guarded store process): ram frame by cpu_tmpl_stage.py --ram"""
    ram = ctx.pr.get('ram')
    return dict(evidence=f'pipeline_roles.ram = {json.dumps(ram)[:80]}', ram=ram) if ram else None


# ================================================================== patterns: symbolic engines of the control/datapath layers
def p_engine_symexec_chain(ctx):
    """comb control facts per class by forward fact propagation (ExtendedSVSymExec + ExtendedSVFactChain.chain_outs_tab)"""
    if ctx.instruction_word is None:
        return None
    return dict(evidence=f'instruction word {ctx.instruction_word}, decode cone {len(ctx.decode_cone)} signals', cone=len(ctx.decode_cone))


def _mixed_shortcircuit(ctx):
    cone, n = ctx.decode_cone, 0
    for i in ctx.comb:
        for a in assigns(ctx.procs[i]['body']):
            for x in exprs(a[2]):
                if x[0] == 'EBinary' and x[1] == 1 and x[2] in ('BAnd', 'BOr'):
                    l, r = evar_ids(x[3]), evar_ids(x[4])
                    if l and r and ((l <= cone and not (r & cone)) or (r <= cone and not (l & cone))):
                        n += 1
    return n


def p_engine_fast4(ctx):
    """1-bit and/or with one side decided by the class facts and the other undecided (short-circuit): ExtendedSVFast4"""
    n = _mixed_shortcircuit(ctx)
    return dict(evidence=f'{n} and/or nodes mixing decode-cone and other operands', nodes=n) if n else None


def _self_read(ctx):
    out = []
    for i in ctx.comb:
        written, hit = set(), False
        for s in stmts(ctx.procs[i]['body']):
            if s[0] == 'SAssign':
                if evar_ids(s[2]) & written:
                    hit = True
                written.add(lv_root(s[3]))
        if hit:
            out.append(i)
    return out


def p_engine_overlay(ctx):
    """comb process reads its own earlier assignments (`t = a + b; t = !t[0]`): pex refuses; overlay executor ExtendedSVSymExecOverlay"""
    sr = _self_read(ctx)
    return dict(evidence=f'self-reading comb processes {sr[:8]}', processes=sr) if sr else None


def _undecidable(ctx):
    cone, seqr, out = ctx.decode_cone, ctx.seq_regs, []
    for i in ctx.comb:
        body = ctx.procs[i]['body']
        roots = {lv_root(a[3]) for a in assigns(body)}
        if len(roots) < 8 or not (roots & cone):
            continue
        und = [s for s in stmts(body) if s[0] in ('SIf', 'SCase')
               and any(x in seqr and x not in cone for e in stmt_exprs(s) for x in evar_ids(e))]
        if und:
            out.append((i, len(roots), len(und)))
    return out


def p_engine_havoc(ctx):
    """process contains code undecidable from the class facts (CSR/counter state in case/if tests) next to the control
    outputs: havoc executor ExtendedSVSymExecHavoc (undecided statements -> width-0 havoc entries of their static writers)"""
    u = _undecidable(ctx)
    return dict(evidence=f'comb processes (index, roots, undecided tests) {u}', processes=[x[0] for x in u]) if u else None


def p_engine_overlay4(ctx):
    """overlay executor with the xeval4 guard evaluator (needed under the havoc executor)"""
    return p_engine_havoc(ctx) and p_engine_overlay(ctx) and dict(evidence='havoc + self-reading processes')


def p_engine_symalias_nba(ctx):
    """combinational blocks whose assignments are non-blocking (ExtendedSVSymAliasNba.eqchain2_out)"""
    n = _comb_nba(ctx)
    return dict(evidence=f'comb processes with NBAs {n[:6]}', processes=n) if n else None


def p_slice_root_fact(ctx):
    """a root written by several combinational slice processes (covering bit slices -> full-root fact)"""
    sl = {r: sorted(ps) for r, ps in ctx.writers.items() if len(ps) >= 2 and all(ctx.procs[i]['kind'] == 'Combinational' for i in ps)
          and all(any(a[3][0] == 'LSel' for a in assigns(ctx.procs[i]['body']) if lv_root(a[3]) == r) for i in ps)}
    return dict(evidence=f'slice-written roots {dict(list((r, len(p)) for r, p in sl.items())[:6])}', roots=sorted(sl)) if sl else None


def p_comparison_atoms(ctx):
    """forwarding / hazard logic is an if-chain whose guards compare two signals (register-address tags): expression-keyed
    facts (atoms) decide the guards (FactsHold over any Expr)"""
    hits = []
    for i in ctx.comb:
        n = 0
        for s in stmts(ctx.procs[i]['body']):
            if s[0] == 'SIf' and any(x[0] == 'EBinary' and x[2] in ('BEq', 'BNeq') and x[3][0] == 'EVar' and x[4][0] == 'EVar' and x[3][1] == 5
                                     for x in exprs(s[1])):
                n += 1
        if n >= 2:
            hits.append((i, n))
    return dict(evidence=f'if-chains with register-tag comparisons (process, guards) {hits[:4]}', processes=[h[0] for h in hits]) if hits else None


def p_case_mux(ctx):
    """comb `case sel k: out = in_k` (ExtendedSVCaseMux.checked_case_mux)"""
    mux = []
    for i in ctx.comb:
        for s in stmts(ctx.procs[i]['body']):
            if s[0] == 'SCase':
                arms = [b for k, b in s[2] if k is not None]
                if len(arms) >= 3 and all(b[0] == 'SAssign' and b[2][0] == 'EVar' for b in arms):
                    mux.append(i)
    return dict(evidence=f'case muxes {mux[:6]}', processes=mux) if mux else None


def p_subsign33(ctx):
    """33-bit sign/zero-extended subtraction whose sign bit is the compare result (CPUSubSign33)"""
    n = sum(1 for i in ctx.comb for a in assigns(ctx.procs[i]['body']) for x in exprs(a[2]) if x[0] == 'EBinary' and x[2] == 'BSub' and x[1] == 33)
    return dict(evidence=f'{n} 33-bit subtractions', nodes=n) if n else None


def p_copy_chains(ctx):
    """stage-enable / stall / flush / address registers that are plain copies of other registers or wires (cpu_tmpl_bzcopy.py)"""
    cc = ctx.tr.get('control_chain') or ctx.pr.get('controller')
    return dict(evidence='manifest control chain roles present', roles=list(cc)[:6]) if cc and ctx.pr.get('stages') else None


def p_fetch_mux_wire(ctx):
    """instruction word = flush ? NOP : hold ? previous : read_data (fetch wires by checked assignment binding)"""
    fm = ctx.tr.get('fetch_mux')
    return dict(evidence='template_roles.fetch_mux present', fetch_mux=fm) if fm else None


def p_role_param_cores(ctx):
    """Dark-like core role ids present (template_roles.core_ids): role-parameterised hand-written cycle/fetch/cursor cores"""
    return dict(evidence='template_roles.core_ids present') if ctx.tr.get('core_ids') else None


def p_class_table(ctx):
    """the design implements the RV32I jump-family classes decoded from one instruction word (class table bridge/inverse)"""
    return dict(evidence=f'instruction word {ctx.instruction_word}') if ctx.instruction_word is not None else None


def p_immediate_shapes(ctx):
    """immediates assembled from slices / replicated sign bits of the instruction word (CPUImmediateShapes / RtlShapes)"""
    w = ctx.instruction_word
    if w is None:
        return None
    cone = ctx.decode_cone
    n = sum(1 for i in ctx.comb for a in assigns(ctx.procs[i]['body']) for x in exprs(a[2])
            if (x[0] == 'EReplicate' or (x[0] == 'EExtend' and x[2]) or (x[0] == 'EConcat' and x[3][0] == 'ESel'))
            and any(y[0] == 'EVar' and (y[2] in cone or y[2] == w) for y in exprs(x)))
    return dict(evidence=f'{n} sign-replicate / sign-extend / concat-of-slices nodes over the instruction word cone', nodes=n) if n else None


# ================================================================== patterns: closure shapes and lift builders
def closure_shape(ctx):
    fs = ctx.pr.get('fetch_slot', {})
    if fs.get('validity', {}).get('kind') == 'kill_counter':
        return 'counter', f"fetch validity is a kill counter (reg {fs['validity']['counter']['id']}): commit iff counter = 0"
    com = ctx.tr.get('commit', {})
    if isinstance(com, dict) and com.get('valid_flush'):
        vf = com['valid_flush']['id']
        rhs = ctx.comb_assign.get(vf)
        if rhs and all(x in ctx.seq_regs for x in evar_ids(rhs[0][1])):
            return 'pulse', f'commit valid = not ex_flush {vf}, an OR of shift-register pulse bits {sorted(evar_ids(rhs[0][1]))}'
    if ctx.tr.get('fsm') or (ctx.tr.get('reset_reg') and ctx.tr.get('commit') and not ctx.pr.get('stages')):
        return 'state_inv', 'single-issue core, commit decided on the RTL state (FSM / reset register), Runtime = State'
    if ctx.pr.get('stages') and ctx.pr.get('observer', {}).get('commit_valid'):
        return 'staged', f"stage list with stored valid bits, observer valid {ctx.pr['observer']['commit_valid']['id']}"
    return None, 'no closure shape recognised'


def _shape_pattern(name):
    def f(ctx):
        s, ev = closure_shape(ctx)
        return dict(evidence=ev, shape=s) if s == name else None
    f.__doc__ = f'closure shape `{name}` recognised from the manifest roles'
    return f


p_closure_counter = _shape_pattern('counter')
p_closure_staged = _shape_pattern('staged')
p_closure_state_inv = _shape_pattern('state_inv')
p_closure_pulse = _shape_pattern('pulse')


def lift_kind(ctx):
    """the lift builder follows the engine of the control/datapath provider layer"""
    if p_engine_havoc(ctx):
        return 'expr_provider'
    if p_engine_overlay(ctx):
        return 'overlay_provider'
    com = ctx.tr.get('commit', {})
    if p_engine_symalias_nba(ctx):
        return 'wire_provider'
    if isinstance(com, dict) and com.get('stage') == 'EX':
        return 'ex_provider'
    if p_engine_fast4(ctx) and ctx.tr.get('fsm'):
        return 'ctl_provider'
    return None


def _lift_pattern(name):
    def f(ctx):
        k = lift_kind(ctx)
        return dict(evidence=f'provider engine -> lift builder {k}', kind=k) if k == name else None
    f.__doc__ = f'lift builder `{name}`'
    return f


p_lift_isa = lambda ctx: dict(evidence='design-independent ISA lemmas (TmplLiftIsa)') if ctx.instruction_word is not None else None
p_lift_isa.__doc__ = 'design-independent ISA lift module (always applicable to an RV32I jump-family core)'
p_lift_wire_provider = _lift_pattern('wire_provider')
p_lift_ctl_provider = _lift_pattern('ctl_provider')
p_lift_ex_provider = _lift_pattern('ex_provider')
p_lift_overlay_provider = _lift_pattern('overlay_provider')
p_lift_expr_provider = _lift_pattern('expr_provider')


def run_all(design, names):
    """{rule name: match dict or None (or {'error': ...})} for the given pattern names"""
    ctx = Ctx(design)
    out = {}
    for n in names:
        f = globals().get(n)
        if f is None:
            out[n] = dict(error=f'no pattern function {n}')
            continue
        try:
            out[n] = f(ctx)
        except Exception as e:      # a pattern bug must not stop the matcher; it is reported
            out[n] = dict(error=repr(e)[:300])
    return ctx, out


# ================================================================== patterns added for the Bzeeno-route layer variants
def p_rf_fall_glue(ctx):
    """the register-file write process fires on the FALLING edge of the primary clock: RF-at-fall glue between the edge and RF layers"""
    bank, pi = rf_info(ctx)
    if pi is None or pi not in ctx.expected_fire(0, _rst_idle(ctx)):
        return None
    return dict(evidence=f'RF write process_{pi} fires on the falling edge', process=pi)


def p_reset_phase_layers(ctx):
    """async reset (reset-events layer applies): stage / frame / ram steps at the asserted reset level for the boot phases"""
    m = p_reset_events_layer(ctx)
    if not m:
        return None
    return dict(evidence=m['evidence'] + ('; ram role present' if ctx.pr.get('ram') else ''), ram=bool(ctx.pr.get('ram')))


# ---- angelo5fix closure (Continuation 11, 2026-11-04; additive) ----
def _single_assign_comb(ctx):
    out = []
    for i in ctx.comb:
        a = list(assigns(ctx.procs[i]['body']))
        if len(a) == 1 and len(list(stmts(ctx.procs[i]['body']))) <= 2:
            out.append(i)
    return out


def p_comb_resolution(ctx):
    """many combinational processes are a single assignment: resolve next-state / wire expressions through their bindings
    (ExtendedSVExprResolve.esub_sound / esub_sound2) instead of a per-register formula"""
    sa = _single_assign_comb(ctx)
    return dict(evidence=f'{len(sa)} single-assignment comb processes', processes=sa) if len(sa) >= 20 else None


def p_partial_eval(ctx):
    """resolved expressions contain conditionals / and-or chains decided by control registers: partial evaluation
    under concrete control facts (ExtendedSVPartialEval.pe_sound, mfold_sound)"""
    m = p_comb_resolution(ctx)
    if not m:
        return None
    conds = [i for i in m['processes'] if any(x[0] == 'ECond' for a in assigns(ctx.procs[i]['body']) for x in _subexprs(a))]
    return dict(evidence=f'{len(conds)} resolved wires with conditionals', processes=conds) if conds else None


def _subexprs(a):
    out, st = [], [x for x in a if isinstance(x, (list, tuple))]
    while st:
        e = st.pop()
        if isinstance(e, (list, tuple)) and e and isinstance(e[0], str):
            out.append(e)
            st.extend(x for x in e[1:] if isinstance(x, (list, tuple)))
        elif isinstance(e, (list, tuple)):
            st.extend(x for x in e if isinstance(x, (list, tuple)))
    return out


def p_seqtree2_one(ctx):
    """sequential process without a reset test whose body is SSeq [SSeq l] with several statements
    (ExtendedSVSeqTree2One: the inner sequence itself is the converted statement)"""
    pr = [i for i in ctx.seq if not _inner(ctx, i)[0] and len(_inner(ctx, i)[1]) > 1]
    return dict(evidence=f'processes {pr}', processes=pr) if pr else None
