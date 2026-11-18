#!/usr/bin/env python3
"""Bzeeno EX/ID datapath facts per ISA class (template route, goal 3b).

For the 29 classes of the class table (cpu_isa_classes / cpu_class_table) generate, on the configured Bzeeno AST,
  alu     <C>_ex_result   EX result wire (exe_data_mux.selected_out 259) from the ID/EX registers and the control values
  cmp     <C>_cmp         ID compare unit (compare_eq / compare_lt wires) from the forwarded operands
  imm     <C>_imm         ID immediate decoder output imm_val (30) from the IF/ID word
  tgt     <C>_target      branch / JAL / JALR target adders (jal_pc 40, jalr_branch_pc 42)
  gen     class independent: next-pc mux, p4 adder, operand forwarding mux, instruction field links
Method: the control values are constant hypotheses (the values of the accepted controller facts r-tmpl-bz-ctl-20261103-a2,
parsed from that module); ExtendedSVFactChain derives the constants on the wires downstream of them, then
ExtendedSVSymAliasNba.eqchain2 (path execution of the data multiplexers under those constants) gives one equation per
data wire; the generated proof rewrites along the equations.  The planner below is an untrusted Python mirror; Coq
re-checks every equation by computation.
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.
"""
import argparse
import json
import re
import sys
from pathlib import Path
import cpu_tmpl_ast as T
import cpu_tmpl_roles as roles
import cpu_tmpl_edge as E
import cpu_tmpl_symexec as X
import cpu_isa_classes as isa
import cpu_class_table as ct

CTL_V = 'results/r-tmpl-bz-ctl-20261103-a2/BzTmplCtl.v'
FUEL = 512


class NoPlan(Exception):
    pass


def zl(v):
    return f'({v})' if v < 0 else str(v)


def ctl_values(path=CTL_V):
    """class -> {root: (width, value)} of the controller outputs that are independent of the scenario
    (checked identical in all scenarios of the accepted module)."""
    t = Path(path).read_text()
    per = {}
    for m in re.finditer(r'Definition outs_(\w+):list\(\(signal\*nat\)\*Z\):=\[(.*?)\]\.\n', t):
        d = {}
        for r, w, z in re.findall(r'\(\((\d+)%nat,(\d+)%nat\),(-?\d+)\)', m.group(2)):
            d[int(r)] = (int(w), int(z))
        per.setdefault(m.group(1).split('_')[0], []).append(d)
    out = {}
    for c, ds in per.items():
        com = {}
        for r in ds[0]:
            if all(r in d and d[r] == ds[0][r] for d in ds):
                com[r] = ds[0][r]
        out[c] = com
    return out


def taken_tables(path=CTL_V, report='results/r-tmpl-bz-ctl-20261103-a2/report.json'):
    """branch class -> (bit root, {bit value: (pcsrc, flush)}), verified identical in all 64 scenarios of the accepted module."""
    t = Path(path).read_text()
    rep = json.loads(Path(report).read_text())['per_class']
    outs = {}
    for m in re.finditer(r'Definition outs_(\w+):list\(\(signal\*nat\)\*Z\):=\[(.*?)\]\.\n', t):
        outs[m.group(1)] = {int(r): int(z) for r, w, z in re.findall(r'\(\((\d+)%nat,(\d+)%nat\),(-?\d+)\)', m.group(2))}
    res = {}
    for c in ('Beq', 'Bne', 'Blt', 'Bge', 'Bltu', 'Bgeu'):
        tab, root = {}, None
        for n, d in outs.items():
            if n.split('_')[0] != c:
                continue
            info = rep[n]
            bits = [(r, v) for r, v in zip(info['cmp'], info['cmpvals']) if r in (148, 149)]
            assert len(bits) == 1, (n, bits)
            root = bits[0][0]
            val = (d[159], d[157])
            assert tab.setdefault(bits[0][1], val) == val, (n, tab)
        res[c] = (root, tab)
    return res


class Planner:
    def __init__(self, design='bzeeno'):
        self.ast, self.pr, self.tr = roles.load_all(design)
        a = self.ast
        self.writers = {}
        for k, i in enumerate(a.comb_ids):
            for r in E.assigned_roots(a.procs[i]['body']):
                self.writers.setdefault(r, []).append(k)
        self.nsig = max(a.sig) + 1

    def body(self, k):
        return self.ast.procs[self.ast.comb_ids[k]]['body']

    def width_of(self, r):
        return self.ast.sig[r]['width']


class Spec:
    """One theorem.  consts: [(root, value)]; datas: [(root, varname)] (hypothesis norm w (read d root) = var);
    extra_vars: variable names without a root hypothesis; targets: [(root, coq_rhs)]  (conclusion norm w (read d root) = rhs)."""

    def __init__(self, name, consts, datas, targets, closer='', extra_hyps=(), lemmas=(), vars_=(), kind='', stops=(),
                 derived=(), pre=(), nocbn=(), custom=None, force=()):
        self.name, self.consts, self.datas, self.targets = name, consts, datas, targets
        self.closer, self.extra_hyps, self.lemmas, self.vars_, self.kind = closer, list(extra_hyps), list(lemmas), list(vars_), kind
        self.stops, self.derived, self.pre, self.nocbn, self.custom = set(stops), list(derived), list(pre), set(nocbn), custom
        self.force = list(force)


class Session:
    """Plan for one Spec: constants (phase A), equations (phase B), rewrite order."""

    def __init__(self, P, spec):
        self.P, self.spec = P, spec
        self.F = {}                 # Expr -> value
        self.fl = []                # leaf facts (Expr, value) in order
        for r, v in spec.consts:
            e = ('EVar', P.width_of(r), r)
            self.F[e] = v
            self.fl.append((e, v))
        for e, v in spec.derived:
            self.F[e] = v
            self.fl.append((e, v))
        self.data_roots = {r for r, _ in spec.datas} | set(spec.stops)
        self.ksC, self.outsC = [], []
        self.eq = {}                # (w, r) -> simp rhs
        self.proc_eqs = {}          # k -> {root: (w, rhs)}
        self.order = []             # post-order of equation roots
        self.leaves = []            # (w, r) of inputs that are not equations
        self.opaque = []            # (w, r) read only by undecided ECond guards and not plannable (opaque; proof case-splits)
        self.opaque_why = {}

    # ---- constants ----
    def cev(self, e, strict=False):
        for _ in range(200):
            try:
                return X.Exec(list(self.F.items())).ev({}, e)
            except X.Stuck as s:
                x = s.expr
                if x is not None and x[0] == 'EVar' and x[2] not in self.data_roots:
                    try:
                        self.ensure_const(x[2], x[1])
                        continue
                    except NoPlan:
                        pass
                if strict:
                    raise NoPlan(f'undecided {x}')
                return None
        raise NoPlan('loop')

    def ensure_const(self, root, width):
        e = ('EVar', width, root)
        if e in self.F:
            return self.F[e]
        ks = self.P.writers.get(root, [])
        if len(ks) != 1:
            raise NoPlan(f'no unique writer for {root}')
        k = ks[0]
        for _ in range(200):
            try:
                ov = X.Exec(list(self.F.items())).run(self.P.body(k), {}, FUEL)
                break
            except X.Stuck as s:
                x = s.expr
                if x is not None and x[0] == 'EVar' and x[2] not in self.data_roots:
                    self.ensure_const(x[2], x[1])
                    continue
                raise NoPlan(f'const {root}: stuck on {x}')
        else:
            raise NoPlan('loop')
        for r, (w, z) in ov.items():
            if all(j <= k for j in self.P.writers.get(r, [])):
                ee = ('EVar', w, r)
                if ee not in self.F:
                    self.F[ee] = z
                    self.outsC.append((r, w, z))
        if k not in self.ksC:
            self.ksC.append(k)
        if e not in self.F:
            raise NoPlan(f'root {root} not constant')
        return self.F[e]

    # ---- simp / pex (mirror of ExtendedSVSymAlias.simp / pex, ExtendedSVSymAliasNba.pexn) ----
    def simp(self, e):
        k = e[0]
        if k in ('EConst', 'EVar'):
            return e
        if k in ('ESel', 'EConcat'):
            return (k, e[1], self.simp(e[2]), self.simp(e[3]))
        if k == 'EReplicate':
            return (k, e[1], e[2], self.simp(e[3]))
        if k in ('EExtend', 'EUnary'):
            return (k, e[1], e[2], self.simp(e[3]))
        if k == 'EBinary':
            return (k, e[1], e[2], self.simp(e[3]), self.simp(e[4]))
        if k == 'ECond':
            z = self.cev(e[2])
            if z is not None:
                c = self.simp(e[4] if z == 0 else e[3])
                return c if c[1] == e[1] else ('EExtend', e[1], False, c)
            return (k, e[1], self.simp(e[2]), self.simp(e[3]), self.simp(e[4]))
        raise ValueError(k)

    def clean(self, written, e):
        return all(x not in written for _, x in X.inputs(e))

    def pex(self, st, written, acc, nbmode, fuel=FUEL):
        if fuel == 0:
            return written, acc
        k = st[0]
        if k == 'SSkip':
            return written, acc
        if k == 'SAssign':
            if st[3][0] != 'LVar':
                raise NoPlan('partial write')
            if nbmode:
                if not st[1]:
                    raise NoPlan('blocking in nba mode')
                w, r = st[3][1], st[3][2]
                acc = dict(acc)
                acc.pop(r, None)
                acc[r] = (w, self.simp(st[2]))
                return written, acc
            if st[1]:
                raise NoPlan('nested nba')
            if not self.clean(written, st[2]):
                raise NoPlan('rhs reads written')
            w, r = st[3][1], st[3][2]
            acc = dict(acc)
            acc.pop(r, None)
            acc[r] = (w, self.simp(st[2]))
            return written | {r}, acc
        if k == 'SSeq':
            for c in st[1]:
                written, acc = self.pex(c, written, acc, nbmode, fuel - 1)
            return written, acc
        if k == 'SIf':
            if not self.clean(written, st[1]):
                raise NoPlan('guard reads written')
            z = self.cev(st[1], True)
            return self.pex(st[3] if z == 0 else st[2], written, acc, nbmode, fuel - 1)
        if k == 'SCase':
            if not self.clean(written, st[1]):
                raise NoPlan('scrutinee reads written')
            v = self.cev(st[1], True)
            d, chosen = ('SSkip',), None
            for key, body in st[2]:
                if key is None:
                    d = body
                else:
                    if not self.clean(written, key):
                        raise NoPlan('key reads written')
                    if v == self.cev(key, True):
                        chosen = body
                        break
            return self.pex(d if chosen is None else chosen, written, acc, nbmode, fuel - 1)
        raise ValueError(k)

    def proc_equations(self, k):
        if k in self.proc_eqs:
            return self.proc_eqs[k]
        body = self.P.body(k)
        b0 = body
        if b0[0] == 'SAssign' and b0[1]:
            b0 = ('SAssign', False) + tuple(b0[2:])
        err = None
        for st, nb in ((b0, False), (body, True)):
            try:
                _, acc = self.pex(st, frozenset(), {}, nb)
                self.proc_eqs[k] = acc
                return acc
            except NoPlan as ex:
                err = ex
        raise NoPlan(f'process comb#{k}: {err}')

    # ---- equation graph ----
    def need(self, w, r):
        if (w, r) in self.eq:
            return
        if r in self.data_roots:
            if (w, r) not in self.leaves:
                self.leaves.append((w, r))
            return
        if ('EVar', w, r) in self.F:
            if (w, r) not in self.leaves:
                self.leaves.append((w, r))
            return
        ks = self.P.writers.get(r, [])
        if len(ks) != 1:
            raise NoPlan(f'root {r} (w{w}) is not a hypothesis and has writers {ks}')
        acc = self.proc_equations(ks[0])
        if r not in acc:
            raise NoPlan(f'process of {r} does not assign it on the chosen path')
        w2, rhs = acc[r]
        if w2 != w:
            raise NoPlan(f'width mismatch at {r}: {w} vs {w2}')
        self.eq[(w, r)] = rhs
        gonly = guard_only_inputs(rhs) if OPAQUE_GUARDS else set()
        uonly = opaque_branch_only_inputs(rhs, None) if OPAQUE_GUARDS else set()
        pending = []
        for (wi, x) in dict.fromkeys(X.inputs(rhs)):      # same order as before: identical plans when nothing is opaque
            if (wi, x) in gonly:
                self.need_guard(wi, x)
            elif (wi, x) in uonly:
                err = self.need_guard(wi, x, tentative=True)
                if err is not None:
                    pending.append(((wi, x), err))
            else:
                self.need(wi, x)
        if pending:
            # an unplannable input read only inside the branches of an ECond is opaque only when that ECond's guard is
            # opaque (the conclusion must then hold for both branches whatever the input is); otherwise refuse as before
            bonly = opaque_branch_only_inputs(rhs, {x for _, x in self.opaque})
            for (wx, err) in pending:
                if wx not in bonly:
                    raise err
                self.opaque.append(wx)
                self.opaque_why[wx[1]] = 'branch of an opaque-guard ECond: ' + str(err)
        self.order.append((w, r))

    # ---- opaque ECond guards (2026-11-11, tmpl-econd-casesplit) ----
    _SNAP = ('F', 'fl', 'ksC', 'outsC', 'eq', 'proc_eqs', 'order', 'leaves')

    def need_guard(self, w, r, tentative=False):
        """input read only inside the guard of an ECond that the facts leave undecided: plan it if possible; when the planner
        cannot (a register outside the role closure, an unconstrained counter, a wire whose process cannot be path-executed),
        undo the partial plan and keep the root as an OPAQUE leaf.  The equation keeps the ECond, the generated proof
        case-splits on the guard and must prove the conclusion in both branches (nothing is assumed about the guard)."""
        if (w, r) in self.opaque:
            return None
        snap = {k: (dict(v) if isinstance(v, dict) else list(v)) for k, v in ((k, getattr(self, k)) for k in self._SNAP)}
        try:
            self.need(w, r)
        except NoPlan as ex:
            for k, v in snap.items():
                setattr(self, k, v)
            if tentative:
                return ex
            self.opaque.append((w, r))
            self.opaque_why[r] = str(ex)
        return None

    def plan(self):
        for (w, r) in self.spec.force:
            self.ensure_const(r, w)
        for r, _ in self.spec.targets:
            self.need(self.P.width_of(r), r)
        self.order.reverse()          # target first, dependencies after
        self.ksE = sorted({self.P.writers[r][0] for (w, r) in self.eq})


OPAQUE_GUARDS = __import__('os').environ.get('TMPL_OPAQUE_GUARDS', '1') != '0'


def guard_only_inputs(e):
    """(w, r) inputs of `e` that occur only inside ECond guards (never in a data position)."""
    data, guard = set(), set()

    def go(x, in_guard):
        k = x[0]
        if k == 'EConst':
            return
        if k == 'EVar':
            (guard if in_guard else data).add((x[1], x[2]))
            return
        if k == 'ECond':
            go(x[2], True)
            go(x[3], in_guard)
            go(x[4], in_guard)
            return
        for c in x[1:]:
            if isinstance(c, tuple) and c and isinstance(c[0], str) and c[0].startswith('E'):
                go(c, in_guard)
    go(e, False)
    return guard - data


def opaque_branch_only_inputs(e, opaque_roots):
    """(w, r) inputs of `e` that occur only inside the branches (or guard) of an ECond whose guard reads an opaque root
    (opaque_roots=None: of any ECond)."""
    inside, outside = set(), set()

    def go(x, under):
        k = x[0]
        if k == 'EConst':
            return
        if k == 'EVar':
            (inside if under else outside).add((x[1], x[2]))
            return
        if k == 'ECond':
            og = under or opaque_roots is None or any(r in opaque_roots for _, r in X.inputs(x[2]))
            go(x[2], under or og)
            go(x[3], og)
            go(x[4], og)
            return
        for c in x[1:]:
            if isinstance(c, tuple) and c and isinstance(c[0], str) and c[0].startswith('E'):
                go(c, under)
    go(e, False)
    return inside - outside


COMMS = {'BAdd': ('?x + ?y', 'Z.add_comm'), 'BAnd': ('Z.land ?x ?y', 'Z.land_comm'), 'BOr': ('Z.lor ?x ?y', 'Z.lor_comm'),
         'BXor': ('Z.lxor ?x ?y', 'Z.lxor_comm'), 'BMul': ('?x * ?y', 'Z.mul_comm')}


def commuted_ops(exprs, datas):
    """commutative operators whose operands are written in the other order than the spec's first two data operands
    (datas[0] = first ISA operand, datas[1] = second); [] when the spec has fewer than two data operands"""
    if len(datas) < 2:
        return []
    A, Bq = {datas[0][0]}, {datas[1][0]}
    out = []

    def go(e):
        if e[0] == 'EBinary' and e[2] in COMMS:
            l, r = {x for _, x in X.inputs(e[3])}, {x for _, x in X.inputs(e[4])}
            if l & Bq and r & A and not l & A and e[2] not in out:
                out.append(e[2])
        for c in e[1:]:
            if isinstance(c, tuple) and c and isinstance(c[0], str) and c[0].startswith('E'):
                go(c)
    for e in exprs:
        go(e)
    return out


def opaque_split(roots, state='d'):
    """Ltac (one tactic, no final period): destruct every guard test `Z.eqb g 0` that reads an opaque root, then reduce the
    selected branch.  Both branches remain as goals."""
    alts = ' | '.join(f'context [read_signal {state} {r}%nat] => idtac' for r in roots)
    return (f'(repeat match goal with |- context [Z.eqb ?g 0] => match g with {alts} end; destruct (Z.eqb g 0) end); cbv iota')


def sentences_to_tactic(text):
    """Join a proof-script fragment (Coq sentences, written for ONE goal) into one tactic that runs on every goal of a case
    split: `s1. s2. all: (s3).` -> `s1; s2; (s3)`; `1: (s).` -> `[ s | idtac .. ]`.  Raises NoPlan on a construct it does
    not translate (bullets, braces, other goal selectors)."""
    out, cur, depth, i, n = [], '', 0, 0, len(text)
    while i < n:
        ch = text[i]
        if ch in '([':
            depth += 1
        elif ch in ')]':
            depth -= 1
        if ch == '.' and depth == 0 and (i + 1 == n or text[i + 1].isspace()):
            out.append(cur.strip()); cur = ''
        else:
            cur += ch
        i += 1
    if cur.strip():
        raise NoPlan(f'unterminated sentence {cur.strip()[:60]!r}')
    tacs = []
    for s in out:
        if not s:
            continue
        m = re.match(r'^(all|\d+)\s*:\s*(.*)$', s, flags=re.S)
        if m and m.group(1) == 'all':
            tacs.append(f'({m.group(2)})')
        elif m and m.group(1) == '1':
            tacs.append(f'[ ({m.group(2)}) | idtac .. ]')
        elif m or s[0] in '{}-+*':
            raise NoPlan(f'goal structure {s[:40]!r} not translatable')
        else:
            tacs.append(f'({s})')
    return '(' + '; '.join(tacs) + ')'     # parenthesised: `split; (chain)` runs the whole chain on each branch separately


def coq_eqn(w, r, e):
    return f'({w}%nat,{r}%nat,{T.coq(e)})'


def idx_list(n):
    return ';'.join(f'{i}%nat' for i in range(n))


def emit(P, spec, S):
    """Coq text of one theorem and its definitions."""
    n = spec.name
    nF = len(S.fl) + len(S.outsC)
    L = []
    L.append(f'Definition fl_{n}:Facts:=[' + '; '.join(f'({T.coq(e)},{zl(z)})' for e, z in S.fl) + '].')
    ks = lambda lst: '[' + '; '.join(f'({k}%nat,[{idx_list(nF)}])' for k in lst) + ']'
    L.append(f'Definition ksC_{n}:list(nat*list nat):={ks(S.ksC)}.')
    L.append(f'Definition outsC_{n}:list((signal*nat)*Z):=[' + '; '.join(f'(({r}%nat,{w}%nat),{zl(z)})' for r, w, z in S.outsC) + '].')
    L.append(f'Definition ksE_{n}:list(nat*list nat):={ks(S.ksE)}.')
    L.append(f'Definition eqs_{n}:list Eqn:=[' + '; '.join(coq_eqn(w, r, S.eq[(w, r)]) for (w, r) in S.order) + '].')
    binders = ' '.join(f'({v}:Z)' for v in [v for _, v in spec.datas] + spec.vars_)
    hyps = [f'norm {P.width_of(r)} (read_signal d {r}%nat) = {zl(v)}' for r, v in spec.consts]
    hyps += [f'norm {P.width_of(r)} (read_signal d {r}%nat) = {v}' for r, v in spec.datas]
    hyps += spec.extra_hyps
    concl = ' /\\ '.join(f'norm {P.width_of(r)} (read_signal d {r}%nat) = {rhs}' for r, rhs in spec.targets)
    L.append(f'Theorem {n} seed d {binders} : CombLFP P seed d -> ' + ''.join(f'{h} -> ' for h in hyps) + concl + '.')
    names = [f'hc{i}' for i in range(len(spec.consts))] + [f'hd{i}' for i in range(len(spec.datas))] + [f'hx{i}' for i in range(len(spec.extra_hyps))]
    pf = [' '.join(['Proof. intros HL'] + names) + '.']
    pf += [' ' + x for x in spec.pre]
    pf.append(f' assert (HF : FactsHold d fl_{n}) by (intros e z HI; cbn in HI; repeat (destruct HI as [HI|HI]; [inversion HI; subst; first [assumption|(cbn [eval_expr]; assumption)]|]); contradiction).')
    pf.append(f' pose proof (chain_outs_tab P comb_ps wtab ksC_{n} fl_{n} outsC_{n} seed d eq_refl wtab_ok HF HL (ltac:(vm_compute;reflexivity))) as HC.')
    pf.append(f' pose proof (facts_app d _ _ HF (decout_facts d _ HC)) as HF2.')
    pf.append(f' destruct (eqchain2_out P comb_ps wtab ksE_{n} (fl_{n} ++ outs_facts outsC_{n}) [] eqs_{n} seed d eq_refl wtab_ok HF2 HL (ltac:(vm_compute;reflexivity))) as [_ HE].')
    for (w, r) in S.order:
        cb = '' if r in spec.nocbn else f'; cbn [eval_expr expr_width] in E{r}'
        pf.append(f' pose proof (HE {w}%nat {r}%nat _ ltac:(pick_in)) as E{r}{cb}.')
    cs = [(r, w, z) for (r, w, z) in S.outsC if (w, r) in S.leaves]
    for r, w, z in cs:
        pf.append(f' pose proof (HC (({r}%nat,{w}%nat),{zl(z)}) ltac:(pick_in)) as C{r}; cbn [fst snd] in C{r}.')
    hn = []
    for i, (r, v) in enumerate(spec.datas):
        W = P.width_of(r)
        pf.append(f' assert (Hn{i} : norm {W} {v} = {v}) by (rewrite <- hd{i}; apply norm_idempotent).')
        pf.append(f' assert (Hm{i} : norm {W + 1} {v} = {v}) by (rewrite <- hd{i}; rewrite norm_wide by lia; reflexivity).')
        hn += [f'rewrite Hn{i}', f'rewrite Hm{i}']
    for lm in spec.lemmas:
        pf.append(' ' + lm)
    HN = ' | '.join(hn + ['rewrite norm_lo by lia', 'rewrite norm_wide by lia', 'rewrite Z.add_0_r', 'rewrite Z.shiftr_0_r', 'rewrite Z.gtb_ltb', 'rewrite norm_one_boolz'])
    dleaves = [f'hd{i}' for i, (r, v) in enumerate(spec.datas) if (P.width_of(r), r) in S.leaves]
    if spec.custom:
        tail = spec.custom(S, cs, dleaves, HN)
        if S.opaque:
            # split after the last `rewrite` line of the custom script, run the rest as one tactic on every branch
            k = max([i for i, x in enumerate(tail) if x.lstrip().startswith('rewrite ')] or [-1])
            tail = tail[:k + 1] + [' ' + opaque_split([r for _, r in S.opaque]) + '; ' + sentences_to_tactic('\n'.join(tail[k + 1:])) + '.']
        pf += tail
    else:
        rw = [f'E{r}' for (w, r) in S.order] + [f'C{r}' for r, w, z in cs] + dleaves
        pf.append(' ' + ('rewrite ' + ', '.join(rw) + '.' if rw else ''))
        cl = (spec.closer or 'cnorm. repeat (apply conj).\n all: (cnorm; repeat first [{HN} | reflexivity]).').replace('{HN}', HN)
        cm = commuted_ops([S.eq[k] for k in S.order], spec.datas) if not spec.closer else []
        if cm:   # operands of a commutative operator in the other order than the spec's operands: retry after commutativity
            cl += '\n all: first [ ' + ' | '.join(f'(match goal with |- context [{COMMS[o][0]}] => rewrite ({COMMS[o][1]} x y); solve [cnorm; repeat first [{HN} | reflexivity]] end)' for o in cm) + ' ].'
        if S.opaque:
            cl = opaque_split([r for _, r in S.opaque]) + '; ' + sentences_to_tactic(cl) + '.'
        pf.append(' ' + cl)
    pf.append('Qed.')
    return '\n'.join(L + pf)


PREAMBLE = '''From Coq Require Import ZArith List Bool Lia.
Require Import coqutil.Z.BitOps Lang.ExtendedSV Lang.ExtendedSVSymExec Lang.ExtendedSVFactChain Lang.ExtendedSVSymAlias
 Lang.ExtendedSVSymAliasNba Lang.ExtendedSVAssignment Lang.ExtendedSVWordInvariant Ex.External.CPUImmediateShapes Ex.External.CPUImmediateRtlShapes
 Ex.External.CPUDatapathFacts @AST@.
Import ListNotations ExtendedSV ExtendedSVSymExec ExtendedSVFactChain ExtendedSVSymAlias ExtendedSVSymAliasNba ExtendedSVAssignment ExtendedSVWordInvariant
 CPUImmediateShapes CPUImmediateRtlShapes CPUDatapathFacts @ASTNS@.
Local Open Scope Z_scope.
Definition P:=@PROG@.
Ltac pick_in := repeat first [apply in_eq | apply in_cons].
Ltac cnorm := repeat match goal with
 | |- context [norm ?w (Zpos ?p)] => let v := eval cbv in (norm w (Zpos p)) in change (norm w (Zpos p)) with v
 | |- context [norm ?w Z0] => let v := eval cbv in (norm w Z0) in change (norm w Z0) with v end.
'''


def module_text(P, specs, module, extra_defs='', author=T.PROOF_AUTHOR, extra_exports=()):
    pr = P.pr
    pre = (PREAMBLE.replace('@AST@', pr['ast']['module']).replace('@ASTNS@', pr['ast']['program'].split('.')[0])
           .replace('@PROG@', pr['ast']['program'].split('.')[-1]))
    wt = [[] for _ in range(P.nsig)]
    for r, ks in P.writers.items():
        wt[r] = ks
    wtab = 'Definition wtab:list(list nat):=[' + '; '.join('[' + ';'.join(f'{x}%nat' for x in w) + ']' for w in wt) + '].'
    body = [wtab, 'Definition comb_ps:=filter is_comb (processes P).',
            'Lemma wtab_ok:TabC comb_ps wtab.', 'Proof. apply tab_okb_sound. vm_compute;reflexivity. Qed.']
    if extra_defs:
        body.append(extra_defs)
    info, exports = {}, list(extra_exports)
    for spec in specs:
        S = Session(P, spec)
        S.plan()
        body.append(emit(P, spec, S))
        exports.append(f'{module}.{spec.name}')
        info[spec.name] = dict(kind=spec.kind, consts=len(spec.consts), datas=len(spec.datas), constant_wires=len(S.outsC),
                               equations=len(S.eq), const_steps=len(S.ksC), eq_steps=len(S.ksE))
    text = (f'(** {pr["ast"]["module"]}: EX/ID datapath facts (tools/cpu_tmpl_bzex.py). proof_author: {author}; external_llm_api_calls=0. *)\n'
            + pre + f'Module {module}.\n' + '\n'.join(body) + f'\nEnd {module}.\n' + ''.join(f'Print Assumptions {e}.\n' for e in exports))
    return text, exports, info


# ------------------------------------------------------------------ specs
EX = dict(a=246, b=247, imm=248, pc=245, p4=249, lt=243, res=259,
          aluc=242, auipc=237, aluimm=234, slt=235, jal=241)
SUBST = {'a': 'a', 'b': 'b', 'pc': 'pc', 'link': 'link'}


def zformula(c):
    """Z expression of the class value on the variables a, b, pc, link."""
    return c['value']


def ex_specs(P, cv):
    out = []
    for c in isa.classes():
        if c['kind'] == 'branch':
            continue
        n = c['name']
        v = cv[n]
        consts = [(EX['aluc'], v[158][1]), (EX['auipc'], v[169][1]), (EX['aluimm'], v[165][1]),
                  (EX['slt'], v[173][1]), (EX['jal'], v[166][1])]
        # the exe_* registers hold the controller's values (transport is the stage layer's job)
        if n in ('Slt', 'Sltu', 'Slti', 'Sltiu'):
            spec = Spec(f'{n}_ex_result', consts, [(EX['lt'], 'l')], [(EX['res'], 'norm 32 l')], kind='alu')
        elif c['kind'] in ('jal', 'jalr'):
            spec = Spec(f'{n}_ex_result', consts, [(EX['p4'], 'link')], [(EX['res'], 'norm 32 link')], kind='alu')
        else:
            datas = []
            if n == 'Lui':
                datas = [(EX['imm'], 'b')]
            elif n == 'Auipc':
                datas = [(EX['pc'], 'pc'), (EX['imm'], 'b')]
            elif c['operand_b'] == 'rs2':
                datas = [(EX['a'], 'a'), (EX['b'], 'b')]
            else:
                datas = [(EX['a'], 'a'), (EX['imm'], 'b')]
            val = c['value']
            spec = Spec(f'{n}_ex_result', consts, datas, [(EX['res'], f'norm 32 ({val})')], kind='alu')
        out.append(spec)
    return out


def cmp_specs(P, cv):
    out = []
    for c in isa.classes():
        n = c['name']
        slt = n in ('Slt', 'Sltu', 'Slti', 'Sltiu')
        if c['kind'] != 'branch' and not slt:
            continue
        v = cv[n]
        s, im = v[174][1], v[175][1]
        bv = 'imm' if im else 'b'
        datas = [(204, 'a')] + ([(30, 'imm')] if im else [(210, 'b')])
        lt = f'boolz (Z.ltb (signed_value 32 a) (signed_value 32 {bv}))' if s else f'boolz (Z.ltb a {bv})'
        eq = f'boolz (Z.eqb a {bv})'
        tg = [(64, lt), (148, lt)] + ([(224, lt)] if slt else [(65, eq), (149, eq)])
        out.append(Spec(f'{n}_cmp', [(174, s), (175, im)], datas, tg, kind='cmp'))
    return out


def tgt_specs(P, cv):
    out = []
    for c in isa.classes():
        n, k = c['name'], c['kind']
        v = cv[n]
        if k == 'jal':
            out.append(Spec(f'{n}_target', [], [(30, 'imm'), (139, 'pc')], [(40, 'norm 32 (Z.add pc imm)')], kind='tgt',
                            closer='cnorm. repeat first [{HN}]. rewrite (Z.add_comm imm pc). reflexivity.'))
        elif k in ('jalr', 'branch'):
            jr = v[167][1]
            base = ('a', 204) if jr else ('pc', 139)
            out.append(Spec(f'{n}_target', [(167, jr)], [(30, 'imm'), (base[1], base[0])],
                            [(42, f'norm 32 (Z.shiftl (Z.shiftr (norm 32 (Z.add {base[0]} imm)) 1) 1)')], kind='tgt',
                            closer=f'cnorm. repeat first [{{HN}}]. rewrite (Z.add_comm imm {base[0]}). rewrite rtl_clear0. reflexivity.'))
    return out


IMM_TYPE = {'OPIMM': 'I', 'JALR': 'I', 'LUI': 'U', 'AUIPC': 'U', 'JAL': 'J', 'BRANCH': 'B'}


def imm_specs(P, cv):
    out = []
    f3e = ('ESel', 3, ('EVar', 32, 183), ('EConst', 5, 12))
    for c in isa.classes():
        n, g = c['name'], c['group']
        if g not in IMM_TYPE:
            continue
        v = cv[n]
        typ = IMM_TYPE[g]
        shift = n in ct.SHIFT_IMM
        opc = c['opcode']
        f3 = c['funct3']
        consts = [(168, v[168][1])]
        derived = [(('EVar', 7, 184), opc)]
        hyps = [f'bitSlice w 0 7 = {opc}']
        pre = [f'assert (H184 : norm 7 (read_signal d 184%nat) = {opc}) by (rewrite (word184 seed d w HL hd0); rewrite (slice_val w 0 7%nat ltac:(lia)); exact hx0).']
        if g == 'OPIMM':
            derived.append((f3e, f3))
            hyps.append(f'bitSlice w 12 15 = {f3}')
            pre.append('assert (H183 : norm 32 (read_signal d 183%nat) = w) by exact (word183 seed d w HL hd0).')
            pre.append(f'assert (Hf3 : eval_expr d (ESel 3 (EVar 32 183%nat) (EConst 5 12)) = {f3}) by (cbn [eval_expr]; rewrite H183; '
                       f'change (norm 5 12) with 12; rewrite (slice_val w 12 3%nat ltac:(lia)); exact hx1).')
        if shift:
            hyps.append('bitSlice w 25 26 = 0')
            out.append(Spec(f'{n}_imm', consts, [(140, 'w')], [(30, 'bitSlice w 20 26')], extra_hyps=hyps, derived=derived, pre=pre, kind='imm',
                            closer='cnorm. repeat first [{HN}]. change (norm 5 20) with 20. rewrite (shamt5 w hx2). reflexivity.'))
            continue
        X = 'B2' if typ == 'B' else typ
        tgt = f'norm 32 (isa_imm_{typ} w)'

        def custom(S, cs, dleaves, HN, X=X, typ=typ):
            rest = [f'E{r}' for (w, r) in S.order if r not in (30, 186)]
            rhs = T.coq(S.eq[(32, 186)])
            L = []
            if typ == 'U':
                shape = 'imm_U (EVar 32 183%nat)'
                L.append(f' rewrite E30, E186.')
                L.append(f' change (eval_expr d {rhs}) with (eval_expr d ({shape})).')
                L.append(' rewrite eval_imm_U.')
            else:
                L.append(' assert (Hs185 : eval_expr d (EVar 1 185%nat) = 1) by (cbn [eval_expr]; exact C185).')
                L.append(' rewrite E30, E186.')
                L.append(f' change (eval_expr d {rhs}) with (eval_expr d (rsx_{X} (EVar 32 183%nat) (EVar 1 185%nat))).')
                L.append(f' rewrite (eval_rsx_{X} d (EVar 32 183%nat) (EVar 1 185%nat) Hs185), eval_rimm_{X}.')
            L.append(' cbn [eval_expr].')
            L.append(' rewrite ' + ', '.join(rest + dleaves) + '.')
            L.append(f' repeat first [{HN} | reflexivity].')
            return L
        out.append(Spec(f'{n}_imm', consts, [(140, 'w')], [(30, tgt)], extra_hyps=hyps, derived=derived, pre=pre, kind='imm',
                        nocbn={186}, custom=custom, force=([] if typ == 'U' else [(1, 185)])))
    return out


def gen_specs(P, cv):
    out = []
    for k, term in ((0, 27), (1, 42), (2, 40)):
        out.append(Spec(f'pcnext_{k}', [(159, k)], [], [(130, f'norm 32 (read_signal d {term}%nat)'), (25, f'norm 32 (read_signal d {term}%nat)')],
                        stops=[term], kind='gen'))
    out.append(Spec('if_p4', [], [(119, 'pcv')], [(27, 'norm 32 (Z.add pcv 4)')], kind='gen'))
    for sel, mux, regs in (('a', 204, (317, 259, 284, 293)), ('b', 210, (318, 259, 284, 293))):
        for k, term in enumerate(regs):
            out.append(Spec(f'fwd{sel}_sel{k}', [(160 if sel == 'a' else 161, k)], [],
                            [(mux, f'norm 32 (read_signal d {term}%nat)')], stops=[term], kind='gen'))
    out.append(Spec('word183', [], [(140, 'w')], [(183, 'w')], kind='genw'))
    out.append(Spec('word184', [], [(140, 'w')], [(184, 'norm 7 (Z.shiftr w 0)')], kind='genw'))
    return out


def taken_text(P, cv, module):
    """Z-level lemmas: pcsrc / flush of the controller (table from the accepted controller facts) at the compare-unit output
    equals the ISA branch condition (class table)."""
    tt = taken_tables()
    L, ex = [], []
    for c in isa.classes():
        if c['kind'] != 'branch':
            continue
        n = c['name']
        root, tab = tt[n]
        assert set(tab) == {0, 1} and all(p == f for p, f in tab.values())
        eq = n in ('Beq', 'Bne')
        s = cv[n][174][1]
        base = 'Z.eqb a b' if eq else (f'Z.ltb (signed_value 32 a) (signed_value 32 b)' if s else 'Z.ltb a b')
        e = f'boolz ({base})'
        cond = c['cond']
        L.append(f'Definition {n}_pcsrc (e:Z) : Z := if Z.eqb e 0 then {tab[0][0]} else {tab[1][0]}.')
        L.append(f'Definition {n}_flush (e:Z) : Z := if Z.eqb e 0 then {tab[0][1]} else {tab[1][1]}.')
        L.append(f'Theorem {n}_taken (a b:Z) : {n}_pcsrc ({e}) = boolz ({cond}) /\\ {n}_flush ({e}) = boolz ({cond}).')
        L.append(f'Proof. unfold {n}_pcsrc, {n}_flush. destruct ({base}); cbn; split; reflexivity. Qed.')
        ex.append(f'{module}.{n}_taken')
    return '\n'.join(L), ex


IFACE_PRE = '''From Coq Require Import ZArith List Bool Lia.
Require Import coqutil.Z.BitOps Lang.ExtendedSV Lang.ExtendedSVWordInvariant Ex.External.CPUImmediateShapes Ex.External.CPUDatapathFacts
 Ex.External.CV32E40PReq41Instruction Ex.External.CV32E40PReq40StateRel Ex.External.CV32E40PDataOpExecution Ex.External.CV32E40PISAWordInterpretation Ex.External.CPUClassValueBridge
 Ex.External.CV32E40PBranchISACondition Ex.RvCore.FormalSpec Ex.RvCore.Machine coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth
 coqutil.Map.Interface coqutil.Byte riscv.Utility.Utility riscv.Utility.MkMachineWidth
 @AST@ @PROVIDERS@.
Import ListNotations ExtendedSV ExtendedSVWordInvariant CPUImmediateShapes CPUDatapathFacts CV32E40PReq40StateRel CV32E40PDataOpExecution CV32E40PISAWordInterpretation CV32E40PBranchISACondition @ASTNS@.
Local Open Scope Z_scope.
Definition P:=@PROG@.
Module BzA := TmplBzExAlu.BzTmplExAlu.BzTmplExAlu.
Module BzC := TmplBzExCmp.BzTmplExCmp.BzTmplExCmp.
Module BzG := TmplBzExTgt.BzTmplExTgt.BzTmplExTgt.
Module BzI := TmplBzExImm.BzTmplExImm.BzTmplExImm.
Module BzN := TmplBzExGen.BzTmplExGen.BzTmplExGen.
'''


def iface_text(P, cv, module):
    pr = P.pr
    pre = (IFACE_PRE.replace('@AST@', pr['ast']['module']).replace('@ASTNS@', pr['ast']['program'].split('.')[0])
           .replace('@PROG@', pr['ast']['program'].split('.')[-1])
           .replace('@PROVIDERS@', 'TmplBzExAlu.BzTmplExAlu TmplBzExCmp.BzTmplExCmp TmplBzExTgt.BzTmplExTgt TmplBzExImm.BzTmplExImm TmplBzExGen.BzTmplExGen'))
    L, ex = [], []
    rd = lambda r: f'(read_signal d {r}%nat)'
    for c in isa.classes():
        n, k = c['name'], c['kind']
        v = cv[n]
        if k == 'branch':
            continue
        consts = [(EX['aluc'], v[158][1]), (EX['auipc'], v[169][1]), (EX['aluimm'], v[165][1]), (EX['slt'], v[173][1]), (EX['jal'], v[166][1])]
        conj = ' /\\ '.join(f'norm {P.width_of(r)} {rd(r)} = {z}' for r, z in consts)
        L.append(f'Definition ExPrem_{n} (d:State) : Prop := {conj}.')
        sub = lambda r: f'(norm 32 {rd(r)})'
        if n in ('Slt', 'Sltu', 'Slti', 'Sltiu'):
            rhs, nd = f'norm 32 (norm 1 {rd(243)})', 1
        elif k in ('jal', 'jalr'):
            rhs, nd = f'norm 32 {sub(249)}', 1
        else:
            val = c['value']
            if n == 'Lui':
                mp, nd = {'b': sub(248)}, 1
            elif n == 'Auipc':
                mp, nd = {'pc': sub(245), 'b': sub(248)}, 2
            elif c['operand_b'] == 'rs2':
                mp, nd = {'a': sub(246), 'b': sub(247)}, 2
            else:
                mp, nd = {'a': sub(246), 'b': sub(248)}, 2
            rhs = f'norm 32 ({re.sub(r"[ab]|pc", lambda m: mp[m.group(0)] if re.fullmatch(r"[ab]|pc", m.group(0)) else m.group(0), val)})' if False else None
            val2 = re.sub(r'\b(pc|a|b)\b', lambda m: mp.get(m.group(1), m.group(1)), val)
            rhs = f'norm 32 ({val2})'
        L.append(f'Theorem {n}_ex seed d : CombLFP P seed d -> ExPrem_{n} d -> norm 32 {rd(259)} = {rhs}.')
        L.append(f'Proof. intros HL [h0 [h1 [h2 [h3 h4]]]]. exact (BzA.{n}_ex_result seed d {"_ " * nd}HL h0 h1 h2 h3 h4{" eq_refl" * nd}). Qed.')
        ex.append(f'{module}.{n}_ex')
    # E3
    for c in isa.classes():
        n, k = c['name'], c['kind']
        if k == 'jal':
            L.append(f'Theorem {n}_e3 seed d w : CombLFP P seed d -> norm 2 {rd(159)} = 2 -> norm 32 {rd(140)} = w -> bitSlice w 0 7 = {c["opcode"]} -> norm 1 {rd(168)} = 1 ->\n'
                     f' norm 32 {rd(130)} = norm 32 (Z.add (norm 32 {rd(139)}) (isa_imm_J w)).')
            L.append(f'Proof. intros HL hp hw ho hs. rewrite (proj1 (BzN.pcnext_2 seed d HL hp)). rewrite (BzG.{n}_target seed d _ _ HL (BzI.{n}_imm seed d w HL hs hw ho) eq_refl).\n rewrite norm_add_r. reflexivity. Qed.')
            ex.append(f'{module}.{n}_e3')
        elif k == 'jalr':
            L.append(f'Theorem {n}_e3 seed d w : CombLFP P seed d -> norm 2 {rd(159)} = 1 -> norm 1 {rd(167)} = 1 -> norm 32 {rd(140)} = w -> bitSlice w 0 7 = {c["opcode"]} -> norm 1 {rd(168)} = 1 ->\n'
                     f' norm 32 {rd(130)} = norm 32 (Z.land (Z.add (norm 32 {rd(204)}) (isa_imm_I w)) (Z.lnot 1)).')
            L.append(f'Proof. intros HL hp hj hw ho hs. rewrite (proj1 (BzN.pcnext_1 seed d HL hp)). rewrite (BzG.{n}_target seed d _ _ HL hj (BzI.{n}_imm seed d w HL hs hw ho) eq_refl).\n rewrite norm_add_r, clear0_land. reflexivity. Qed.')
            ex.append(f'{module}.{n}_e3')
        elif k == 'branch':
            L.append(f'Theorem {n}_e3 seed d w : CombLFP P seed d -> norm 2 {rd(159)} = 1 -> norm 1 {rd(167)} = 0 -> norm 32 {rd(140)} = w -> bitSlice w 0 7 = {c["opcode"]} -> norm 1 {rd(168)} = 1 ->\n'
                     f' Z.testbit (norm 32 {rd(139)}) 0 = false -> norm 32 {rd(130)} = norm 32 (Z.add (norm 32 {rd(139)}) (isa_imm_B w)).')
            L.append(f'Proof. intros HL hp hj hw ho hs hpc. rewrite (proj1 (BzN.pcnext_1 seed d HL hp)). rewrite (BzG.{n}_target seed d _ _ HL hj (BzI.{n}_imm seed d w HL hs hw ho) eq_refl).\n rewrite norm_add_r. apply clear0_even. apply bit0_add_even; [exact hpc|apply isa_imm_B_even]. Qed.')
            ex.append(f'{module}.{n}_e3')
    L.append(f'Theorem ntaken_e3 seed d : CombLFP P seed d -> norm 2 {rd(159)} = 0 -> norm 32 {rd(130)} = norm 32 (Z.add (norm 32 {rd(119)}) 4).')
    L.append(f'Proof. intros HL hp. rewrite (proj1 (BzN.pcnext_0 seed d HL hp)). exact (BzN.if_p4 seed d _ HL eq_refl). Qed.')
    ex.append(f'{module}.ntaken_e3')
    # ISA bridge section
    L.append('Section ISA.\nContext {word : Interface.word 32} {BW : Bitwidth 32}.\nContext {Registers : map.map Decode.Register word} {Mem : map.map word byte}.\n'
             'Context {word_ok : word.ok word} {registers_ok : map.ok Registers} {mem_ok : map.ok Mem}.\nLocal Notation uw := word.unsigned.\n'
             'Let reg (s:FormalSpec.State) r := formal_register_word s r.')
    for c in isa.classes():
        n, k, g = c['name'], c['kind'], c['group']
        v = cv[n]
        if k == 'branch':
            eq = n in ('Beq', 'Bne')
            which = '[_ [_ [_ H]]]' if eq else '[_ [H _]]'
            root = 149 if eq else 148
            L.append(f'Theorem {n}_isa seed d (x y:word) rs1 rs2 imm : CombLFP P seed d -> norm 1 {rd(174)} = {v[174][1]} -> norm 1 {rd(175)} = 0 -> norm 32 {rd(204)} = uw x -> norm 32 {rd(210)} = uw y ->\n'
                     f' BzC.{n}_pcsrc (norm 1 {rd(root)}) = boolz (isa_branch_guard (Decode.{n} rs1 rs2 imm) x y) /\\ BzC.{n}_flush (norm 1 {rd(root)}) = boolz (isa_branch_guard (Decode.{n} rs1 rs2 imm) x y).')
            L.append(f'Proof. intros HL h174 h175 ha hb. destruct (BzC.{n}_cmp seed d _ _ HL h174 h175 ha hb) as {which}. rewrite H. rewrite <- (CPUClassValueBridge.bridge_{n} x y rs1 rs2 imm). exact (BzC.{n}_taken (uw x) (uw y)). Qed.')
            ex.append(f'{module}.{n}_isa')
            continue
        if k in ('jal', 'jalr'):
            L.append(f'Theorem {n}_ex_isa seed d s : CombLFP P seed d -> ExPrem_{n} d -> norm 32 {rd(249)} = uw (word.add (getPc s) (word.of_Z 4 : word)) -> norm 32 {rd(259)} = uw (word.add (getPc s) (word.of_Z 4 : word)).')
            L.append(f'Proof. intros HL HP hl. rewrite ({n}_ex seed d HL HP). rewrite hl. apply CPUClassValueBridge.norm_uw. Qed.')
            ex.append(f'{module}.{n}_ex_isa')
            continue
        # data classes
        sl = n in ('Slt', 'Sltu', 'Slti', 'Sltiu')
        sh = n in ct.SHIFT_IMM
        if g == 'OP':
            args, extra = f'rd rs1 rs2', ''
            hy = f'norm 32 {rd(246)} = uw (reg s rs1) -> norm 32 {rd(247)} = uw (reg s rs2)'
            names, rw = 'ha hb', 'rewrite ha, hb.'
            binders = 'rd rs1 rs2'
        elif n == 'Lui':
            args, binders = 'rd imm', 'rd imm'
            hy = f'norm 32 {rd(248)} = norm 32 imm'; names, rw = 'hb', 'rewrite hb.'
        elif n == 'Auipc':
            args, binders = 'rd imm', 'rd imm'
            hy = f'norm 32 {rd(245)} = uw (getPc s) -> norm 32 {rd(248)} = norm 32 imm'; names, rw = 'ha hb', 'rewrite ha, hb.'
        elif sh:
            args, binders = 'rd rs sh', 'rd rs sh b'
            hy = f'norm 32 {rd(246)} = uw (reg s rs) -> norm 32 {rd(248)} = b -> 0 <= sh < 32 -> norm 5 b = sh'; names, rw = 'ha hb h1 h2', 'rewrite ha, hb.'
        else:
            args, binders = 'rd rs imm', 'rd rs imm'
            hy = f'norm 32 {rd(246)} = uw (reg s rs) -> norm 32 {rd(248)} = norm 32 imm'; names, rw = 'ha hb', 'rewrite ha, hb.'
        if sl:
            # the result of the set-less-than family is the registered compare bit
            reg1 = '(uw (reg s rs1))' if g == 'OP' else '(uw (reg s rs))'
            b2 = '(uw (reg s rs2))' if g == 'OP' else '(norm 32 imm)'
            val = re.sub(r'\b(a|b)\b', lambda m: reg1 if m.group(1) == 'a' else b2, c['value'])
            hy = f'norm 1 {rd(243)} = {val}'; names, rw = 'hl', 'rewrite hl.'
        pc_note = ''
        concl = f'norm 32 {rd(259)} = uw (result_word s (Decode.{n} {args}))'
        stmt = f'Theorem {n}_ex_isa seed d s {binders} : CombLFP P seed d -> ExPrem_{n} d -> {hy} -> {concl}.'
        L.append(stmt)
        br = f'CPUClassValueBridge.bridge_{n} s {args}' + (' b h1 h2' if sh else '')
        if g in ('OPIMM',) and not sh and not sl:
            pass
        L.append(f'Proof. intros HL HP {names}. rewrite (BzE_{n} seed d HL HP). {rw} exact ({br}). Qed.'.replace(f'BzE_{n}', f'{n}_ex'))
        ex.append(f'{module}.{n}_ex_isa')
    L.append('End ISA.')
    text = (f'(** {pr["ast"]["module"]}: EX-datapath interface E1/E3 of the Bzeeno template agent (tools/cpu_tmpl_bzex.py --kinds iface). '
            f'proof_author: {T.PROOF_AUTHOR}; external_llm_api_calls=0. *)\n' + pre + f'Module {module}.\n' + '\n'.join(L) + f'\nEnd {module}.\n'
            + ''.join(f'Print Assumptions {e}.\n' for e in ex))
    return text, ex


def run(design, names, kinds, module, ctl=CTL_V):
    P = Planner(design)
    cv = ctl_values(ctl)
    if kinds == ['iface']:
        t_, ex_ = iface_text(P, cv, module)
        return t_, ex_, {}
    allspecs = ex_specs(P, cv) + cmp_specs(P, cv) + tgt_specs(P, cv) + gen_specs(P, cv) + imm_specs(P, cv)
    specs = [s for s in allspecs if s.kind in kinds]
    if names != 'all':
        keep = set(names.split(','))
        specs = [s for s in specs if s.name.split('_')[0] in keep]
    xd, xe = '', []
    if 'cmp' in kinds:
        xd, xe = taken_text(P, cv, module)
    return module_text(P, specs, module, extra_defs=xd, extra_exports=xe)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--design', default='bzeeno')
    ap.add_argument('--classes', default='all')
    ap.add_argument('--kinds', default='alu')
    ap.add_argument('--module', default='BzTmplEx')
    ap.add_argument('--namespace')
    ap.add_argument('--out', required=True)
    ap.add_argument('--accept', action='store_true')
    ap.add_argument('--providers', default='', help='ns=dir,ns=dir')
    a = ap.parse_args()
    text, exports, info = run(a.design, a.classes, a.kinds.split(','), a.module)
    if not a.accept:
        Path(a.out).write_text(text)
        print(a.out, len(text.splitlines()), json.dumps(info)[:600])
        sys.exit(0)
    import cpu_tmpl_accept as acc
    prof = json.loads(Path(f'framework/auto-contract-profiles/{a.design}.json').read_text())
    lp = [(prof['pipeline_roles']['ast']['file'].rsplit('/', 1)[0], prof['pipeline_roles']['ast']['module'].split('.')[0])]
    prov = [dict(namespace=x.split('=')[0], directory=x.split('=')[1]) for x in a.providers.split(',') if x]
    r = acc.accept(a.out, a.namespace, a.module, text, exports, lp, providers=prov, extra=dict(generator='tools/cpu_tmpl_bzex.py', design=a.design, per_class=info))
    print(json.dumps({k: r[k] for k in r if k != 'per_class'}, indent=1))
    sys.exit(0 if r['accepted'] else 1)
