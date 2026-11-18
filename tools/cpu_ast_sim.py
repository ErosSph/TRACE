#!/usr/bin/env python3
"""Executable Python model of the ExtendedSV semantics (src/Lang/ExtendedSV.v).

It runs the imported design AST (the `Definition process_N : Process := ...` lines)
exactly as the Coq definitions do:

  eval_expr      norm widths, signed ops, ESel/EConcat/EReplicate/EExtend/...
  exec_stmt      blocking vs nonblocking, fuel (statement_fuel), SCase default rule
  run_process    comb / initial processes: blocking state + pending NBAs applied at the end
  process_updates / apply_updates   sequential processes: every emitted update (blocking and NBA)
                 is computed against the same settled "driven" state, then applied in order
  comb_round / comb_iter / lfp_candidate   combinational least fixed point, `lfp_fuel` rounds
  PhaseSemantics phase_driven_state -> select processes on (pre, driven) -> execute -> lfp

Early exit in the LFP loop is faithful: comb_round is a function of the state only, so once a
round does not change the state every remaining round is the identity.

Design harnesses (Bzeeno, DarkRISCV) mirror the boot/environment of the final theorems, and
independent tiny RV32I ISA references plus Python re-implementations of the Coq program-domain
checkers are used to validate the simulator (see `validate` sub-command).  This tool proves
nothing; it only labels behaviour.
"""
import argparse
import json
import random
import re
import sys
import time
from pathlib import Path

# ----------------------------------------------------------------------------------------
# Parser for the Coq term syntax used by the frontends
# ----------------------------------------------------------------------------------------
TOK = re.compile(r"\{\||\|\}|:=|[()\[\];,]|-?\d+|[A-Za-z_][\w']*")
PROC_LINE = re.compile(r'(?m)^Definition (process_\d+) : Process := (.*)$')


class Parser:
    def __init__(self, text):
        self.t = TOK.findall(text)
        self.i = 0

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else None

    def next(self):
        tok = self.t[self.i]
        self.i += 1
        return tok

    def expect(self, tok):
        got = self.next()
        if got != tok:
            raise ValueError(f'expected {tok!r}, got {got!r} at token {self.i}')

    def lst(self, item):
        self.expect('[')
        out = []
        if self.peek() == ']':
            self.next()
            return out
        while True:
            out.append(item())
            sep = self.next()
            if sep == ']':
                return out
            if sep != ';':
                raise ValueError(f'bad list separator {sep!r}')

    def expr(self):
        self.expect('(')
        if self.peek() == '(':
            e = self.expr()
            self.expect(')')
            return e
        head = self.next()
        if head == 'EConst':
            e = ('EConst', int(self.next()), int(self.next()))
        elif head == 'EVar':
            e = ('EVar', int(self.next()), int(self.next()))
        elif head == 'ESel':
            w = int(self.next())
            e = ('ESel', w, self.expr(), self.expr())
        elif head == 'EConcat':
            w = int(self.next())
            e = ('EConcat', w, self.expr(), self.expr())
        elif head == 'EReplicate':
            w = int(self.next())
            c = int(self.next())
            e = ('EReplicate', w, c, self.expr())
        elif head == 'EExtend':
            w = int(self.next())
            sg = self.next() == 'true'
            e = ('EExtend', w, sg, self.expr())
        elif head == 'EUnary':
            w = int(self.next())
            op = self.next()
            e = ('EUnary', w, op, self.expr())
        elif head == 'EBinary':
            w = int(self.next())
            op = self.next()
            e = ('EBinary', w, op, self.expr(), self.expr())
        elif head == 'ECond':
            w = int(self.next())
            e = ('ECond', w, self.expr(), self.expr(), self.expr())
        else:
            raise ValueError(f'unknown expression head {head!r}')
        self.expect(')')
        return e

    def lval(self):
        self.expect('(')
        head = self.next()
        if head == 'LVar':
            lv = ('LVar', int(self.next()), int(self.next()))
        elif head == 'LSel':
            w = int(self.next())
            base = self.lval()
            lv = ('LSel', w, base, self.expr())
        else:
            raise ValueError(f'unknown lvalue head {head!r}')
        self.expect(')')
        return lv

    def stmt(self):
        t = self.next()
        if t == '(':
            s = self.stmt()
            self.expect(')')
            return s
        if t == 'SSkip':
            return ('SSkip',)
        if t == 'SAssign':
            nba = self.next() == 'true'
            rhs = self.expr()
            return ('SAssign', nba, rhs, self.lval())
        if t == 'SSeq':
            return ('SSeq', self.lst(self.stmt))
        if t == 'SIf':
            g = self.expr()
            y = self.stmt()
            return ('SIf', g, y, self.stmt())
        if t == 'SCase':
            sc = self.expr()
            return ('SCase', sc, self.lst(self.arm))
        raise ValueError(f'unknown statement head {t!r}')

    def arm(self):
        self.expect('(')
        k = self.next()
        key = None
        if k == 'Some':
            key = self.expr()
        elif k != 'None':
            raise ValueError('bad case arm')
        self.expect(',')
        s = self.stmt()
        self.expect(')')
        return (key, s)

    def event(self):
        self.expect('{|')
        self.expect('event_edge'); self.expect(':=')
        edge = self.next()
        self.expect(';')
        self.expect('event_signal'); self.expect(':=')
        sig = int(self.next())
        self.expect('|}')
        return (edge, sig)

    def process(self):
        self.expect('{|')
        self.expect('process_kind'); self.expect(':=')
        kind = self.next()
        self.expect(';')
        self.expect('process_events'); self.expect(':=')
        events = self.lst(self.event)
        self.expect(';')
        self.expect('process_body'); self.expect(':=')
        body = self.stmt()
        self.expect(';')
        self.expect('process_source_line'); self.expect(':=')
        line = int(self.next())
        self.expect('|}')
        return dict(kind=kind, events=events, body=body, line=line)


def parse_ast_text(text):
    """Return dict(signal_count, statement_fuel, lfp_fuel, processes=[...]) in program order."""
    procs = {}
    for m in PROC_LINE.finditer(text):
        body = m.group(2).rstrip()
        assert body.endswith('.')
        p = Parser(body[:-1])
        procs[m.group(1)] = p.process()
        assert p.i == len(p.t), f'trailing tokens in {m.group(1)}'
    order = re.search(r'Definition \w+_processes : list Process := \[([^\]]*)\]', text)
    names = [n.strip() for n in order.group(1).split(';')]
    prog = re.search(r'signal_count := (\d+);\s*processes := \w+;\s*statement_fuel := (\d+); lfp_fuel := (\d+)', text)
    return dict(signal_count=int(prog.group(1)), statement_fuel=int(prog.group(2)),
                lfp_fuel=int(prog.group(3)), processes=[procs[n] for n in names],
                names=names)


def parse_ast_file(path):
    return parse_ast_text(Path(path).read_text())


# ----------------------------------------------------------------------------------------
# Runtime helpers (mirror ExtendedSV.v)
# ----------------------------------------------------------------------------------------
class HugeShift(Exception):
    """A slice offset beyond what Coq itself could represent in memory (bits)."""


HUGE = 1 << 22


def mask(w):
    return (1 << w) - 1


def norm(w, v):
    return v & mask(w)


def signed_value(w, v):
    v2 = v & mask(w)
    if w == 0:
        return 0
    return v2 - (1 << w) if (v2 >> (w - 1)) & 1 else v2


def replicate_bits(count, bw, v):
    acc = 0
    m = mask(bw)
    for _ in range(count):
        acc = (acc << bw) | (v & m)
    return acc


def shl(l, r, w):
    # Z.shiftl l r then norm w; l >= 0 so r >= w gives 0 (avoids a gigantic temporary)
    return (l << r) & mask(w) if r < w else 0


def write_slice(old, lsb, width, value):
    if lsb > HUGE:
        raise HugeShift(lsb)
    fm = ((1 << width) - 1) << lsb
    return (old & ~fm) | ((value << lsb) & fm)


def apply_update(b, u):
    i, off, w, val = u
    while i >= len(b):
        b.append(0)
    b[i] = write_slice(b[i], off, w, val)


def edge_fires(edge, old, new):
    if edge == 'AnyChange':
        return old != new
    if edge == 'Posedge':
        return old == 0 and new != 0
    return old != 0 and new == 0  # Negedge


# ----------------------------------------------------------------------------------------
# Code generation: AST -> Python source
# ----------------------------------------------------------------------------------------
def ewidth(e):
    return e[1]


class Gen:
    def __init__(self, statement_fuel):
        self.lines = []
        self.ntmp = 0
        self.fuel = statement_fuel
        self.max_depth = 0

    def emit(self, ind, text):
        self.lines.append('    ' * ind + text)

    def tmp(self):
        self.ntmp += 1
        return f'_t{self.ntmp}'

    # expression -> (python expr string, nesting depth)
    def ex(self, e, ind):
        s, d = self._ex(e, ind)
        return s

    def _ex(self, e, ind):
        k = e[0]
        if k == 'EConst':
            return str(norm(e[1], e[2])), 0
        if k == 'EVar':
            if e[1] == 0:
                return '0', 0
            return f'(b[{e[2]}]&{mask(e[1])})', 1
        kids = []
        if k == 'ESel':
            L, d1 = self._ex(e[2], ind)
            R, d2 = self._ex(e[3], ind)
            s = f'(({L}>>{R})&{mask(e[1])})'
            d = max(d1, d2)
        elif k == 'EConcat':
            H, d1 = self._ex(e[2], ind)
            Lo, d2 = self._ex(e[3], ind)
            s = f'((({H}<<{ewidth(e[3])})|{Lo})&{mask(e[1])})'
            d = max(d1, d2)
        elif k == 'EReplicate':
            B, d = self._ex(e[3], ind)
            s = f'(_rep({e[2]},{ewidth(e[3])},{B})&{mask(e[1])})'
        elif k == 'EExtend':
            B, d = self._ex(e[3], ind)
            if e[2]:
                s = f'(_sv({ewidth(e[3])},{B})&{mask(e[1])})'
            else:
                s = f'({B}&{mask(e[1])})'
        elif k == 'EUnary':
            B, d = self._ex(e[3], ind)
            m = mask(e[1])
            if e[2] == 'UNot':
                s = f'((~{B})&{m})'
            elif e[2] == 'UNegate':
                s = f'((-{B})&{m})'
            elif e[2] == 'URedOr':
                s = f'((1 if {B} else 0)&{m})'
            else:
                raise ValueError(e[2])
        elif k == 'EBinary':
            w, op = e[1], e[2]
            L, d1 = self._ex(e[3], ind)
            R, d2 = self._ex(e[4], ind)
            d = max(d1, d2)
            m = mask(w)
            if op in ('BAnd', 'BOr', 'BXor', 'BAdd', 'BSub', 'BMul'):
                sym = dict(BAnd='&', BOr='|', BXor='^', BAdd='+', BSub='-', BMul='*')[op]
                s = f'(({L}{sym}{R})&{m})'
            elif op in ('BEq', 'BNeq', 'BLtU', 'BGtU'):
                sym = dict(BEq='==', BNeq='!=', BLtU='<', BGtU='>')[op]
                s = f'((1 if {L}{sym}{R} else 0)&{m})'
            elif op == 'BGtS':
                s = f'((1 if _sv({ewidth(e[3])},{L})>_sv({ewidth(e[4])},{R}) else 0)&{m})'
            elif op == 'BShiftL':
                if e[4][0] == 'EConst':
                    r = norm(e[4][1], e[4][2])
                    s = f'(({L}<<{r})&{m})' if r < w else '0'
                else:
                    s = f'_shl({L},{R},{w})'
            elif op == 'BShiftR':
                s = f'(({L}>>{R})&{m})'
            elif op == 'BShiftRS':
                s = f'((_sv({ewidth(e[3])},{L})>>{R})&{m})'
            else:
                raise ValueError(op)
        elif k == 'ECond':
            G, d1 = self._ex(e[2], ind)
            Y, d2 = self._ex(e[3], ind)
            N, d3 = self._ex(e[4], ind)
            s = f'(({Y} if {G} else {N})&{mask(e[1])})'
            d = max(d1, d2, d3)
        else:
            raise ValueError(k)
        d += 1
        if d >= 18:
            t = self.tmp()
            self.emit(ind, f'{t} = {s}')
            return t, 0
        return s, d

    def resolve(self, lv, ind):
        """(root id, offset expr string or int, width) like resolve_lvalue."""
        if lv[0] == 'LVar':
            return lv[2], 0, lv[1]
        rid, boff, _ = self.resolve(lv[2], ind)
        o = self.ex(lv[3], ind)
        if boff == 0:
            return rid, o, lv[1]
        return rid, f'({boff}+{o})', lv[1]

    def stmt(self, st, ind, depth, kind):
        """kind: 'comb' (in-place blocking, NBA applied at the end) or 'seq' (emit list)."""
        self.max_depth = max(self.max_depth, depth)
        if depth >= self.fuel:
            return  # exec_stmt with fuel 0 returns the state unchanged
        k = st[0]
        if k == 'SSkip':
            self.emit(ind, 'pass')
        elif k == 'SAssign':
            nba, rhs, lhs = st[1], st[2], st[3]
            v = self.ex(rhs, ind)
            rid, off, w = self.resolve(lhs, ind)
            tv = self.tmp()
            self.emit(ind, f'{tv} = {v}&{mask(w)}')
            if off == 0:
                to = '0'
            else:
                to = self.tmp()
                self.emit(ind, f'{to} = {off}')
            if nba:
                if kind == 'comb':
                    self.emit(ind, f'pend.append(({rid},{to},{w},{tv}))')
                if kind == 'seq':
                    self.emit(ind, f'emit.append(({rid},{to},{w},{tv}))')
            else:
                if off == 0:
                    self.emit(ind, f'b[{rid}] = (b[{rid}]&{~mask(w)})|{tv}')
                else:
                    # inlined write_slice (same arithmetic; offsets above HUGE are refused)
                    tf = self.tmp()
                    self.emit(ind, f'if {to} > {HUGE}: raise _HS({to})')
                    self.emit(ind, f'{tf} = {mask(w)} << {to}')
                    self.emit(ind, f'b[{rid}] = (b[{rid}]&~{tf})|(({tv}<<{to})&{tf})')
                if kind == 'seq':
                    self.emit(ind, f'emit.append(({rid},{to},{w},{tv}))')
        elif k == 'SSeq':
            if not st[1]:
                self.emit(ind, 'pass')
            for sub in st[1]:
                self.stmt(sub, ind, depth + 1, kind)
        elif k == 'SIf':
            g = self.ex(st[1], ind)
            self.emit(ind, f'if {g}:')
            n0 = len(self.lines)
            self.stmt(st[2], ind + 1, depth + 1, kind)
            if len(self.lines) == n0 or depth + 1 >= self.fuel:
                self.emit(ind + 1, 'pass')
            self.emit(ind, 'else:')
            n0 = len(self.lines)
            self.stmt(st[3], ind + 1, depth + 1, kind)
            if len(self.lines) == n0 or depth + 1 >= self.fuel:
                self.emit(ind + 1, 'pass')
        elif k == 'SCase':
            sc = self.ex(st[1], ind)
            tc = self.tmp()
            self.emit(ind, f'{tc} = {sc}')
            default = None
            keys = []
            for key, body in st[2]:
                if key is None:
                    default = body  # a later (None, _) arm overrides an earlier one
                else:
                    keys.append((self.ex(key, ind), body))
            first = True
            for ks, body in keys:
                self.emit(ind, f'{"if" if first else "elif"} {tc} == {ks}:')
                first = False
                n0 = len(self.lines)
                self.stmt(body, ind + 1, depth + 1, kind)
                if len(self.lines) == n0 or depth + 1 >= self.fuel:
                    self.emit(ind + 1, 'pass')
            if default is not None:
                if first:
                    self.emit(ind, 'if True:')
                else:
                    self.emit(ind, 'else:')
                n0 = len(self.lines)
                self.stmt(default, ind + 1, depth + 1, kind)
                if len(self.lines) == n0 or depth + 1 >= self.fuel:
                    self.emit(ind + 1, 'pass')
            elif first:
                self.emit(ind, 'pass')
        else:
            raise ValueError(k)


def stmt_has_blocking(st):
    k = st[0]
    if k == 'SAssign':
        return not st[1]
    if k == 'SSeq':
        return any(stmt_has_blocking(s) for s in st[1])
    if k == 'SIf':
        return stmt_has_blocking(st[2]) or stmt_has_blocking(st[3])
    if k == 'SCase':
        return any(stmt_has_blocking(s) for _, s in st[2])
    return False


class Sim:
    """Compiled program.  States are python lists of ints (unbounded, like Z)."""

    def __init__(self, ast, shadows=None):
        """`shadows` (optional): {process position: [(mutant id, mutated process dict)]}.  The compiled
        program then also evaluates every mutated process on the very state the original process sees
        and records the mutant ids whose result differs in `self.div` (see `ShadowRun`); the
        original behaviour is not changed."""
        self.ast = ast
        self.n = ast['signal_count']
        self.fuel = ast['lfp_fuel']
        procs = ast['processes']
        shadows = shadows or {}
        self.div = set()
        g = Gen(ast['statement_fuel'])
        self.seq = []       # (index, events, func name)
        self.init_idx = []
        self.seq_shadow = {}     # position -> [(mid, func name)]
        self.init_shadow = {}
        # one function per process keeps code simple; comb round is generated as one function
        g.emit(0, 'def comb_round(b):')
        g.emit(1, 'pend = []')
        for idx, p in enumerate(procs):
            if p['kind'] == 'Combinational':
                g.emit(1, f'# process {idx}')
                sh = shadows.get(idx, [])
                for j, (mid, mp) in enumerate(sh):
                    g.emit(1, f'_sb{j} = b[:]')
                    g.emit(1, 'try:')
                    g.emit(2, f'shc_{mid}(_sb{j})')
                    g.emit(1, 'except Exception:')
                    g.emit(2, f'_sb{j} = None')
                g.stmt(p['body'], 1, 0, 'comb')
                g.emit(1, 'if pend:')
                g.emit(2, 'for _u in pend: _apu(b,_u)')
                g.emit(2, 'pend = []')
                for j, (mid, mp) in enumerate(sh):
                    g.emit(1, f'if _sb{j} != b: _div.add({mid!r})')
        g.emit(1, 'return b')
        for idx, p in enumerate(procs):
            if p['kind'] == 'Sequential':
                self._seq_def(g, f'seq_{idx}', p)
                self.seq.append((idx, p['events'], f'seq_{idx}'))
            elif p['kind'] == 'Initial':
                self._init_def(g, f'init_{idx}', p)
                self.init_idx.append((idx, f'init_{idx}'))
        for idx, sh in shadows.items():
            for mid, mp in sh:
                kind = procs[idx]['kind']
                assert mp['kind'] == kind and mp['events'] == procs[idx]['events']
                if kind == 'Combinational':
                    g.emit(0, f'def shc_{mid}(b):')
                    g.emit(1, 'pend = []')
                    g.stmt(mp['body'], 1, 0, 'comb')
                    g.emit(1, 'for _u in pend: _apu(b,_u)')
                    g.emit(1, 'return b')
                elif kind == 'Sequential':
                    self._seq_def(g, f'shs_{mid}', mp)
                    self.seq_shadow.setdefault(idx, []).append((mid, f'shs_{mid}'))
                else:
                    self._init_def(g, f'shi_{mid}', mp)
                    self.init_shadow.setdefault(idx, []).append((mid, f'shi_{mid}'))
        self.max_depth = g.max_depth
        self.src = '\n'.join(g.lines)
        ns = dict(_HS=HugeShift, _rep=replicate_bits, _sv=signed_value, _shl=shl, _ws=write_slice, _apu=apply_update,
                  _div=self.div)
        exec(compile(self.src, '<ast-sim>', 'exec'), ns)
        self.comb_round = ns['comb_round']
        self.seq_funcs = [(i, ev, ns[nm]) for i, ev, nm in self.seq]
        self.events_by_idx = {i: p['events'] for i, p in enumerate(procs)}
        self.init_funcs = [(i, ns[nm]) for i, nm in self.init_idx]
        self.seq_shadow_funcs = {i: [(m, ns[nm]) for m, nm in v] for i, v in self.seq_shadow.items()}
        self.init_shadow_funcs = {i: [(m, ns[nm]) for m, nm in v] for i, v in self.init_shadow.items()}

    @staticmethod
    def _seq_def(g, name, p):
        g.emit(0, f'def {name}(b):')
        if stmt_has_blocking(p['body']):
            g.emit(1, 'b = b[:]')
        g.emit(1, 'emit = []')
        g.stmt(p['body'], 1, 0, 'seq')
        g.emit(1, 'return emit')

    @staticmethod
    def _init_def(g, name, p):
        g.emit(0, f'def {name}(b):')
        g.emit(1, 'pend = []')
        g.stmt(p['body'], 1, 0, 'comb')
        g.emit(1, 'for _u in pend: _apu(b,_u)')
        g.emit(1, 'return b')

    # lfp_candidate: comb_iter with lfp_fuel rounds (early exit at a fixed point is exact)
    def lfp(self, b):
        for _ in range(self.fuel):
            prev = b[:]
            self.comb_round(b)
            if b == prev:
                break
        return b

    def initialize(self, seed):
        b = list(seed)
        for i, f in self.init_funcs:
            sh = self.init_shadow_funcs.get(i)
            if sh:
                copies = [(m, sf, b[:]) for m, sf in sh]
                f(b)
                for m, sf, c in copies:
                    try:
                        sf(c)
                        if c != b:
                            self.div.add(m)
                    except Exception:
                        self.div.add(m)
            else:
                f(b)
        return b

    def driven(self, pre, sig, newv):
        """phase_driven_state p ev pre"""
        d = list(pre)
        while sig >= len(d):
            d.append(0)
        d[sig] = newv
        return self.lfp(d)

    def phase(self, pre, sig, newv):
        """PhaseSemantics p ev pre (only changed_signal and new_value of ev matter)."""
        return self.phase_ex(pre, sig, newv)[0]

    def phase_ex(self, pre, sig, newv):
        """(PhaseSemantics p ev pre, phase_driven_state p ev pre)."""
        d = list(pre)
        while sig >= len(d):
            d.append(0)
        d[sig] = newv
        self.lfp(d)
        updates = []
        for i, events, f in self.seq_funcs:
            for edge, s in events:
                old = pre[s] if s < len(pre) else 0
                new = d[s] if s < len(d) else 0
                if edge_fires(edge, old, new):
                    emitted = f(d)
                    updates.extend(emitted)
                    for m, sf in self.seq_shadow_funcs.get(i, ()):
                        try:
                            if sf(d) != emitted:
                                self.div.add(m)
                        except Exception:
                            self.div.add(m)
                    break
        driven = d[:]
        for u in updates:
            apply_update(d, u)
        return self.lfp(d), driven

    def fires(self, idx, pre, driven):
        """process_matches_states pre driven (process idx) for a Sequential process."""
        for edge, s_ in self.events_by_idx[idx]:
            old = pre[s_] if s_ < len(pre) else 0
            new = driven[s_] if s_ < len(driven) else 0
            if edge_fires(edge, old, new):
                return True
        return False

    def run(self, pre, events):
        for sig, v in events:
            pre = self.phase(pre, sig, v)
        return pre


# ----------------------------------------------------------------------------------------
# RV32I decode (re-implementation of riscv-coq Decode.decode for the I base) and ISA reference
# ----------------------------------------------------------------------------------------
M32 = 0xFFFFFFFF


def bits(x, lo, hi):
    return (x >> lo) & ((1 << (hi - lo)) - 1)


def sext(width, v):
    v &= (1 << width) - 1
    return v - (1 << width) if v >> (width - 1) else v


def decode(code):
    """Return (mnemonic, rd, rs1, rs2, imm) or None (InvalidI / non-I instruction)."""
    opcode = bits(code, 0, 7)
    rd, f3, rs1, rs2 = bits(code, 7, 12), bits(code, 12, 15), bits(code, 15, 20), bits(code, 20, 25)
    f7, f6, shamt_hi = bits(code, 25, 32), bits(code, 26, 32), bits(code, 25, 26)
    imm12 = sext(12, bits(code, 20, 32))
    simm12 = sext(12, (bits(code, 25, 32) << 5) | bits(code, 7, 12))
    sbimm = sext(13, (bits(code, 31, 32) << 12) | (bits(code, 25, 31) << 5) | (bits(code, 8, 12) << 1) | (bits(code, 7, 8) << 11))
    jimm = sext(21, (bits(code, 31, 32) << 20) | (bits(code, 21, 31) << 1) | (bits(code, 20, 21) << 11) | (bits(code, 12, 20) << 12))
    imm20 = sext(32, bits(code, 12, 32) << 12)
    shamt = bits(code, 20, 26)
    if opcode == 3 and f3 in (0, 1, 2, 4, 5):
        return ({0: 'lb', 1: 'lh', 2: 'lw', 4: 'lbu', 5: 'lhu'}[f3], rd, rs1, 0, imm12)
    if opcode == 15 and rd == 0 and f3 == 0 and rs1 == 0 and bits(code, 28, 32) == 0:
        return ('fence', 0, 0, 0, 0)
    if opcode == 15 and rd == 0 and f3 == 1 and rs1 == 0 and imm12 == 0:
        return ('fence.i', 0, 0, 0, 0)
    if opcode == 19:
        if f3 in (0, 2, 3, 4, 6, 7):
            return ({0: 'addi', 2: 'slti', 3: 'sltiu', 4: 'xori', 6: 'ori', 7: 'andi'}[f3], rd, rs1, 0, imm12)
        if f3 == 1 and f6 == 0 and shamt_hi == 0:
            return ('slli', rd, rs1, 0, shamt)
        if f3 == 5 and f6 == 0 and shamt_hi == 0:
            return ('srli', rd, rs1, 0, shamt)
        if f3 == 5 and f6 == 16 and shamt_hi == 0:
            return ('srai', rd, rs1, 0, shamt)
    if opcode == 23:
        return ('auipc', rd, 0, 0, imm20)
    if opcode == 35 and f3 in (0, 1, 2):
        return ({0: 'sb', 1: 'sh', 2: 'sw'}[f3], 0, rs1, rs2, simm12)
    if opcode == 51:
        t = {(0, 0): 'add', (0, 32): 'sub', (1, 0): 'sll', (2, 0): 'slt', (3, 0): 'sltu', (4, 0): 'xor',
             (5, 0): 'srl', (5, 32): 'sra', (6, 0): 'or', (7, 0): 'and'}.get((f3, f7))
        if t:
            return (t, rd, rs1, rs2, 0)
    if opcode == 55:
        return ('lui', rd, 0, 0, imm20)
    if opcode == 99 and f3 in (0, 1, 4, 5, 6, 7):
        return ({0: 'beq', 1: 'bne', 4: 'blt', 5: 'bge', 6: 'bltu', 7: 'bgeu'}[f3], 0, rs1, rs2, sbimm)
    if opcode == 103 and f3 == 0:
        return ('jalr', rd, rs1, 0, imm12)
    if opcode == 111:
        return ('jal', rd, 0, 0, jimm)
    return None


DATAOP21 = {'lui', 'auipc', 'addi', 'slti', 'sltiu', 'xori', 'ori', 'andi', 'slli', 'srli', 'srai',
            'add', 'sub', 'sll', 'slt', 'sltu', 'xor', 'srl', 'sra', 'or', 'and'}
BRANCHES = {'beq', 'bne', 'blt', 'bge', 'bltu', 'bgeu'}


def jump_family_check(words):
    """Python port of CPUJumpFamilyProgramDomain.check_program (21 data ops, JAL, 6 branches,
    JALR with base register x0; every successor static, aligned and inside the image)."""
    n = len(words)
    if not (0 < n <= 101):
        return False
    for idx, code in enumerate(words):
        if not (0 <= code < 1 << 32):
            return False
        ins = decode(code)
        if ins is None:
            return False
        name, rd, rs1, rs2, imm = ins
        if name == 'jalr':
            if rs1 != 0:
                return False
            succ = [imm % (1 << 32) & ((1 << 32) - 2)]
        elif name in DATAOP21:
            succ = [4 * idx + 4]
        elif name == 'jal':
            succ = [4 * idx + imm]
        elif name in BRANCHES:
            succ = [4 * idx + 4, 4 * idx + imm]
        else:
            return False
        for a in succ:
            if not (0 <= a < 4 * n and a % 4 == 0):
                return False
    return True


def isa_step(regs, pc, ins, mem=None):
    """One RV32I step for the domain classes; returns new pc (regs mutated).  Reference: the
    RISC-V unprivileged spec, written independently of the RTL.  `mem` (a bytearray of 4 bytes at
    address 0) is only needed for the DarkRISCV domain, whose loads/stores use x0+0."""
    name, rd, rs1, rs2, imm = ins
    a, c = regs[rs1], regs[rs2]
    npc = (pc + 4) & M32
    val = None
    if name in ('lb', 'lh', 'lw', 'lbu', 'lhu', 'sb', 'sh', 'sw'):
        addr = (a + imm) & M32
        assert addr == 0 and mem is not None
        word = int.from_bytes(mem, 'little')
        if name == 'lb':
            val = sext(8, word & 0xFF) & M32
        elif name == 'lbu':
            val = word & 0xFF
        elif name == 'lh':
            val = sext(16, word & 0xFFFF) & M32
        elif name == 'lhu':
            val = word & 0xFFFF
        elif name == 'lw':
            val = word
        else:
            n = {'sb': 1, 'sh': 2, 'sw': 4}[name]
            mem[0:n] = (c & ((1 << (8 * n)) - 1)).to_bytes(n, 'little')
    elif name == 'fence.i':
        pass
    elif name == 'lui':
        val = imm & M32
    elif name == 'auipc':
        val = (pc + imm) & M32
    elif name == 'addi':
        val = (a + imm) & M32
    elif name == 'slti':
        val = int(sext(32, a) < imm)
    elif name == 'sltiu':
        val = int(a < (imm & M32))
    elif name == 'xori':
        val = a ^ (imm & M32)
    elif name == 'ori':
        val = a | (imm & M32)
    elif name == 'andi':
        val = a & (imm & M32)
    elif name == 'slli':
        val = (a << (imm & 31)) & M32
    elif name == 'srli':
        val = a >> (imm & 31)
    elif name == 'srai':
        val = (sext(32, a) >> (imm & 31)) & M32
    elif name == 'add':
        val = (a + c) & M32
    elif name == 'sub':
        val = (a - c) & M32
    elif name == 'sll':
        val = (a << (c & 31)) & M32
    elif name == 'slt':
        val = int(sext(32, a) < sext(32, c))
    elif name == 'sltu':
        val = int(a < c)
    elif name == 'xor':
        val = a ^ c
    elif name == 'srl':
        val = a >> (c & 31)
    elif name == 'sra':
        val = (sext(32, a) >> (c & 31)) & M32
    elif name == 'or':
        val = a | c
    elif name == 'and':
        val = a & c
    elif name == 'jal':
        val = npc
        npc = (pc + imm) & M32
    elif name == 'jalr':
        val = npc
        npc = ((a + imm) & M32) & ~1
    elif name in BRANCHES:
        taken = {'beq': a == c, 'bne': a != c, 'blt': sext(32, a) < sext(32, c),
                 'bge': sext(32, a) >= sext(32, c), 'bltu': a < c, 'bgeu': a >= c}[name]
        if taken:
            npc = (pc + imm) & M32
    else:
        raise ValueError(name)
    if val is not None and rd != 0:
        regs[rd] = val
    return npc


def isa_trace(words, steps):
    """Return (pcs, regfiles, mems): pc before each of `steps` instructions, the register file and
    the 32-bit word at data address 0 after it."""
    regs = [0] * 32
    mem = bytearray(4)
    pc = 0
    pcs, rfs, mems = [], [], []
    for _ in range(steps):
        pcs.append(pc)
        pc = isa_step(regs, pc, decode(words[pc // 4] if pc // 4 < len(words) else CV_NOP), mem)
        rfs.append(list(regs))
        mems.append(int.from_bytes(mem, 'little'))
    return pcs, rfs, mems


# ----------------------------------------------------------------------------------------
# Random in-domain programs
# ----------------------------------------------------------------------------------------
def gen_program(rng, check=jump_family_check, allow_jalr=True):
    """Random program accepted by the Python port of the checker (retries until accepted)."""
    while True:
        n = rng.choice([3, 4, 5, 6, 8, 10, 14, 20, 30, 50, 80, 101])
        n = rng.randint(2, n)
        pool_size = rng.choice([2, 3, 4, 6, 12, 31])
        pool = [0] + rng.sample(range(1, 32), pool_size)
        weights = dict(data=rng.choice([40, 70, 90]), br=rng.choice([0, 8, 20]), jal=rng.choice([1, 3, 6]),
                       jalr=rng.choice([0, 2, 4]) if allow_jalr else 0)
        words = []
        for i in range(n):
            kind = rng.choices(['data', 'br', 'jal', 'jalr'], [weights['data'], weights['br'], weights['jal'], weights['jalr']])[0]
            if i == n - 1:
                kind = rng.choice(['jal', 'jalr'] if allow_jalr else ['jal'])
            words.append(gen_instruction(rng, kind, i, n, pool))
        if check(words):
            return words


def r_type(f7, rs2, rs1, f3, rd, op):
    return (f7 << 25) | (rs2 << 20) | (rs1 << 15) | (f3 << 12) | (rd << 7) | op


def pick_target(rng, i, n):
    """Mostly short forward jumps (so programs make progress), sometimes anywhere (loops)."""
    if i + 1 < n and i != n - 1 and rng.random() < 0.8:
        return rng.randrange(i + 1, min(n, i + 9))
    return rng.randrange(n)


def gen_instruction(rng, kind, i, n, pool):
    reg = lambda: rng.choice(pool)
    wreg = lambda: rng.choice(pool + pool + [rng.randrange(32)])
    if kind == 'data':
        c = rng.randrange(8)
        if c == 0:
            return (rng.getrandbits(20) << 12) | (wreg() << 7) | rng.choice([55, 23])
        if c in (1, 2, 3):
            f3 = rng.choice([0, 2, 3, 4, 6, 7])
            imm = rng.choice([rng.randrange(4096), rng.randrange(-8, 8) & 0xFFF, 0, 1, 0xFFF, 0x800])
            return (imm << 20) | (reg() << 15) | (f3 << 12) | (wreg() << 7) | 19
        if c == 4:
            f3, f6 = rng.choice([(1, 0), (5, 0), (5, 16)])
            return (f6 << 26) | (rng.randrange(32) << 20) | (reg() << 15) | (f3 << 12) | (wreg() << 7) | 19
        f3, f7 = rng.choice([(0, 0), (0, 32), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (5, 32), (6, 0), (7, 0)])
        return r_type(f7, reg(), reg(), f3, wreg(), 51)
    if kind == 'br':
        t = pick_target(rng, i, n)
        imm = 4 * (t - i)
        f3 = rng.choice([0, 1, 4, 5, 6, 7])
        u = imm & 0x1FFF
        return (((u >> 12) & 1) << 31) | (((u >> 5) & 0x3F) << 25) | (reg() << 20) | (reg() << 15) | (f3 << 12) | \
            (((u >> 1) & 0xF) << 8) | (((u >> 11) & 1) << 7) | 99
    if kind == 'jal':
        t = pick_target(rng, i, n)
        imm = (4 * (t - i)) & 0x1FFFFF
        return (((imm >> 20) & 1) << 31) | (((imm >> 1) & 0x3FF) << 21) | (((imm >> 11) & 1) << 20) | \
            (((imm >> 12) & 0xFF) << 12) | (wreg() << 7) | 111
    imm = 4 * pick_target(rng, i, n) + rng.choice([0, 0, 1])
    return (imm << 20) | (0 << 15) | (0 << 12) | (wreg() << 7) | 103


# ----------------------------------------------------------------------------------------
# Bzeeno harness (mirrors results/r-jump-itree-20261102-a2/JumpITree.v)
# ----------------------------------------------------------------------------------------
BZ_ROM, BZ_RESETN, BZ_CLK = 330, 1, 0
BZ_WB_VALID, BZ_WB_PC, BZ_RF = 308, 309, 319
BZ_BOOT = [(1, 0), (0, 1), (0, 0), (1, 1)]   # reset_assert, rise, fall, reset_release (FrozenEnvironment)
BZ_SIGNALS = dict(rom=330, wb_valid=308, wb_pc=309, rf=319)


def pack_words(words):
    img = 0
    for w in reversed(words):
        img = w | (img << 32)
    return img


def bz_boot(sim, words):
    seed = [0] * sim.n
    seed[BZ_ROM] = pack_words(words)
    seed[BZ_RESETN] = 1
    return sim.run(seed, BZ_BOOT)


def rf_words(state, base=BZ_RF):
    r = state[base]
    return [(r >> (32 * i)) & M32 for i in range(32)]


class BzeenoRun:
    """Cycle-by-cycle execution; actual_cycle = rise then fall, observer reads the state after rise."""

    def __init__(self, sim, words):
        self.sim = sim
        self.state = bz_boot(sim, words)

    def cycle(self):
        mid = self.sim.phase(self.state, BZ_CLK, 1)
        valid = mid[BZ_WB_VALID] & 1
        pc = mid[BZ_WB_PC] & M32 if valid else None
        rf_mid = mid[BZ_RF]
        self.state = self.sim.phase(mid, BZ_CLK, 0)
        return pc, rf_mid, self.state[BZ_RF]


def bz_trace(sim, words, cycles):
    run = BzeenoRun(sim, words)
    commits, rfs = [], []
    for c in range(cycles):
        pc, rf_mid, rf_end = run.cycle()
        commits.append(pc)
        rfs.append(rf_end)
    return commits, rfs


def rf_from_int(r):
    return [(r >> (32 * i)) & M32 for i in range(32)]


# ----------------------------------------------------------------------------------------
# DarkRISCV harness (mirrors DarkRISCV38DerivedTarget.v / DarkRISCV38DerivedCycle.v)
# ----------------------------------------------------------------------------------------
DK_CLK, DK_RES, DK_IADDR, DK_IDATA, DK_DADDR, DK_DATAI = 1, 2, 4, 5, 9, 16
DK_REGS, DK_PC, DK_XRES, DK_HLT, DK_FLUSH = 63, 65, 22, 23, 43
DK_RAM_BYTES = 128


def dark_decode_supported(code):
    ins = decode(code % (1 << 32))
    if ins is None or ins[0] == 'fence':
        return None
    return ins


def dark_closed_cfg(words):
    """Python port of DarkRISCV38DerivedProgramDomain.ClosedCFG (a Prop in Coq; every field is
    decidable): each covered pc decodes to a Supported38 instruction (the 38 = 21 data ops, 5
    loads, 3 stores, 6 branches, JAL, JALR, FENCE.I) with static memory/JALR operands (x0+0)
    and all successors covered; FENCE.I only as the exact word 4111."""
    n = len(words)
    if not (0 < n <= 2 ** 30):
        return False

    def covered(a):
        return 0 <= a < 4 * n and a % 4 == 0
    for idx, code in enumerate(words):
        pc = 4 * idx
        ins = dark_decode_supported(code)
        if ins is None:
            return False
        name, rd, rs1, rs2, imm = ins
        if name in ('lb', 'lh', 'lw', 'lbu', 'lhu', 'sb', 'sh', 'sw') and not (rs1 == 0 and imm == 0):
            return False
        if name == 'jalr' and not (rs1 == 0 and imm == 0):
            return False
        if name == 'jal':
            succ = [(pc + imm) % 2 ** 32]
        elif name == 'jalr':
            succ = [0]
        elif name in BRANCHES:
            succ = [(pc + 4) % 2 ** 32, (pc + imm) % 2 ** 32]
        else:
            succ = [(pc + 4) % 2 ** 32]
        if not all(covered(a) for a in succ):
            return False
        if name == 'fence.i' and code % 2 ** 32 != 4111:
            return False
    return True


def gen_dark_program(rng, max_len=60):
    while True:
        n = rng.randint(2, rng.choice([4, 8, 12, 20, 36, max_len]))
        pool_size = rng.choice([2, 3, 4, 6, 12, 31])
        pool = [0] + rng.sample(range(1, 32), pool_size)
        w = dict(data=rng.choice([40, 70]), br=rng.choice([0, 10, 25]), jal=rng.choice([2, 5, 10]),
                 jalr=rng.choice([0, 3, 6]), load=rng.choice([0, 8, 20]), store=rng.choice([0, 8, 20]),
                 fence=rng.choice([0, 3]))
        kinds = list(w)
        words = []
        for i in range(n):
            kind = rng.choices(kinds, [w[k] for k in kinds])[0]
            if i == n - 1:
                kind = rng.choice(['jal', 'jalr'])
            if kind == 'load':
                f3 = rng.choice([0, 1, 2, 4, 5])
                words.append((f3 << 12) | (rng.choice(pool + [rng.randrange(32)]) << 7) | 3)
            elif kind == 'store':
                f3 = rng.choice([0, 1, 2])
                words.append((rng.choice(pool) << 20) | (f3 << 12) | 35)
            elif kind == 'fence':
                words.append(4111)
            elif kind == 'jalr':
                words.append((rng.choice(pool + [rng.randrange(32)]) << 7) | 103)
            else:
                words.append(gen_instruction(rng, kind, i, n, pool))
        if dark_closed_cfg(words):
            return words


def ram_word(bank, address):
    base = 4 * (address // 4)
    return (bank >> (8 * base)) & M32 if 0 <= base < 125 else 0


def ram_write_word(bank, address, data, msk):
    base = 4 * (address // 4)
    if not (0 <= base < 125):
        return bank
    for lane in range(4):
        if msk & (1 << lane):
            bank = write_slice(bank, 8 * (base + lane), 8, (data >> (8 * lane)) & 0xFF)
    return bank


class DarkRun:
    """Runtime = (rtl, ram, reset_cycles); observe s then actual_cycle s (ordered_scheduler)."""

    def __init__(self, sim, words):
        self.sim = sim
        self.words = words
        seed = [0] * sim.n
        seed[DK_RES] = 1
        seed[6] = 1
        seed[17] = 1
        seed[DK_REGS] = 0
        self.rtl = sim.initialize(seed)
        self.ram = 0
        self.reset = 4

    def rom(self, addr):
        i = addr // 4
        return self.words[i] if i < len(self.words) else 0

    def observe(self):
        driven = self.sim.driven(self.rtl, DK_CLK, 1)
        if driven[DK_XRES] & 1 == 0 and driven[DK_FLUSH] & 3 == 0 and driven[DK_HLT] & 1 == 0:
            return driven[DK_PC] & M32
        return None

    def cycle(self):
        sim, s = self.sim, self.rtl
        driven = sim.driven(s, DK_CLK, 1)
        rising = sim.phase(s, DK_CLK, 1)
        bank = self.ram
        if driven[8] & 1 == 1 and driven[14] & 1 == 1:
            bank = ram_write_word(bank, driven[9] & M32, driven[15] & M32, driven[11] & 0xF)
        replied = sim.phase(rising, DK_IDATA, self.rom(s[DK_IADDR] & M32) & M32)
        fallen = sim.phase(replied, DK_CLK, 0)
        rtl = sim.phase(fallen, DK_DATAI, ram_word(bank, fallen[DK_DADDR] & M32))
        if self.reset == 1:
            rtl = sim.phase(rtl, DK_RES, 0)
            self.reset = 0
        elif self.reset >= 2:
            self.reset -= 1
        self.rtl, self.ram = rtl, bank

    def step(self):
        """One scheduler step: (commit pc or None, rf words after the cycle, ram word 0 after)."""
        pc = self.observe()
        self.cycle()
        return pc, (self.rtl[DK_REGS] if len(self.rtl) > DK_REGS else 0), self.ram & M32


# ----------------------------------------------------------------------------------------
# CV32E40P harness (mirrors CV32E40PFull38RetirementAdapter / CV32E40PLoadOrderedObservation /
# CV32E40PReq39Trace, i.e. the machinery of `actual_reset_infinite_rtl_isa_refinement`)
# ----------------------------------------------------------------------------------------
CV_NOP = 19
CV_RST, CV_CLK = 8, 7
# obi_ports_image: public inputs driven before every cycle (signal, value); 18/20/23/28 are dynamic
CV_STATIC_DRIVES = [(9, 1), (10, 0), (11, 0), (12, 0), (13, 0), (14, 0), (15, 0), (17, 1)]
CV_RF = 902          # 1024-bit register file (rf_register s r = norm 32 (s[902] >> 32 r))
CV_PROC_WB, CV_PROC_RF = 98, 44


def cv_instruction_from_image(words, address):
    """instruction_from_image: nth (address/4) image nop for non-negative aligned addresses."""
    if address >= 0 and address % 4 == 0:
        i = address // 4
        return words[i] if i < len(words) else CV_NOP
    return CV_NOP


def cv_memory_read_word(word, address):
    return word & M32 if (address & ~3) == 0 else 0


def cv_store_lane(word, be, data, lane):
    return write_slice(word, 8 * lane, 8, data >> (8 * lane)) if (be >> lane) & 1 else word


def cv_memory_store_word(word, req):
    addr, wr, be, data = req
    if wr and (addr & ~3) == 0:
        for lane in range(4):
            word = cv_store_lane(word, be, data, lane)
    return word


class CvRun:
    """One CV32E40P run: `step()` = observe the commits of the current scheduler state
    (ordered_observed_commits) and advance one full physical cycle (full_cycle_image +
    advance_branch_monitor + actual_wb_owner_step)."""

    def __init__(self, sim, words):
        self.sim = sim
        self.words = words
        z = sim.initialize([0] * 1800)                       # initialized_zero
        z[CV_RST] = 1
        pre_reset = sim.lfp(z)                               # pre_reset
        post_reset = sim.phase(pre_reset, CV_RST, 0)         # reset_fall
        self.rtl = sim.phase(post_reset, CV_RST, 1)          # released = trace0.trace_rtl
        self.ipend = None            # trace_instruction_pending
        self.dpend = None            # trace_data_pending  (addr, write, be, wdata)
        self.mem = 0                 # trace_memory_word
        self.pending = None          # pending_token  (pc, instruction)
        self.wb = None               # observed_wb
        self.pjump = None            # full38_pending_jump
        self.cursor = 0              # full38_cursor

    def environment(self):
        sim = self.sim
        d = list(self.rtl)
        iv = 0 if self.ipend is None else 1
        idata = CV_NOP if self.ipend is None else cv_instruction_from_image(self.words, self.ipend)
        dv = 0 if self.dpend is None else 1
        dread = 0 if self.dpend is None else cv_memory_read_word(self.mem, self.dpend[0])
        for sig, v in CV_STATIC_DRIVES + [(18, iv), (20, idata), (22, 1), (23, dv), (28, dread), (29, 0), (32, 0), (36, 1)]:
            d[sig] = v
        return sim.lfp(d)

    def snapshot(self):
        """The Full38Observation as a list of lists (same layout as the Coq cross-check script)."""
        tok = lambda t: [] if t is None else [t[0], t[1]]
        return [list(self.rtl), [self.mem], tok(self.pending), tok(self.wb),
                [] if self.ipend is None else [self.ipend],
                [] if self.dpend is None else [self.dpend[0], 1 if self.dpend[1] else 0, self.dpend[2], self.dpend[3]],
                [self.cursor], [] if self.pjump is None else [self.pjump]]

    def step(self):
        sim = self.sim
        pre = self.environment()                              # environment_state_image
        rising, driven = sim.phase_ex(pre, CV_CLK, 1)         # rising_state_image, phase_driven_state clk_rise
        # --- observer on (pre, driven), using the previous settled state for signal 597
        qualified = sim.fires(CV_PROC_RF, pre, driven) and (driven[885] & 1) == 1
        alu = pre[223] != 0 and pre[135] != 0                 # alu_completes pre
        load_tok = self.wb if (qualified and (driven[1281] & 1) == 1 and (pre[23] & 1) == 1) else None
        scalar_tok = self.pending if (qualified and (self.rtl[597] & 1) == 0 and alu) else None
        pcs = tuple(t[0] for t in (load_tok, scalar_tok) if t is not None)
        self.last_commits = pcs
        # --- advance_full38_monitor: sampled jump target and architectural cursor
        issue = (pre[121], pre[718]) if (pre[222] != 0 and pre[122] != 0) else None
        if scalar_tok is not None:
            if (pre[571] & 1) == 1 and (pre[572] & 1) == 1:
                new_cursor = pre[591] & M32
            elif self.pjump is not None:
                new_cursor = self.pjump
            else:
                new_cursor = (scalar_tok[0] + 4) % 2 ** 32
        elif load_tok is not None:
            new_cursor = (load_tok[0] + 4) % 2 ** 32
        else:
            new_cursor = self.cursor
        if issue is not None:
            new_pjump = (driven[385] & M32) if (driven[1070] & 3) in (1, 2) else None
        else:
            new_pjump = None if alu else self.pjump
        # --- advance_branch_monitor, actual_wb_owner_step
        new_pending = issue if issue is not None else (None if alu else self.pending)
        if sim.fires(CV_PROC_WB, pre, driven):
            if driven[1193] & 1 == 0:
                new_wb = None
            elif driven[1276] & 1 == 0:
                new_wb = self.wb if (driven[1277] & 1) == 0 else None
            else:
                en = (driven[1258] & 1) & ((~(driven[1274] & 1)) & 1)
                new_wb = None if en == 0 else self.pending
        else:
            new_wb = self.wb
        # --- full_cycle_image
        falling = sim.phase(rising, CV_CLK, 0)
        settled = sim.lfp(falling)
        accepted = None
        if pre[21] != 0:
            accepted = (pre[26], pre[24] != 0, pre[25], pre[27])
        self.ipend = None if pre[16] == 0 else pre[19]
        if accepted is not None:
            self.mem = cv_memory_store_word(self.mem, accepted)
        self.dpend = accepted
        self.rtl = settled
        self.pending, self.wb = new_pending, new_wb
        self.cursor, self.pjump = new_cursor, new_pjump
        return (pcs if pcs else None), settled[CV_RF], self.mem


def cv_is_supported(code):
    """GoodSupportedCode /\\ Plain32: decodes to one of the 38 classes (no FENCE, no C/CSR/ECALL...)."""
    if not (0 <= code < 1 << 32) or code & 3 != 3:
        return None
    ins = decode(code)
    if ins is None or ins[0] == 'fence':
        return None
    return ins


MEM_OPS = ('lb', 'lh', 'lw', 'lbu', 'lhu', 'sb', 'sh', 'sw')


def cv_domain_status(words, steps=3000):
    """Python port of the ProgramDomainCertificate conditions, checked along the ISA run from
    `initial_isa`: Supported32Program (every word, reachable or not), ISAInvariant (pc mod 4 = 0),
    RuntimeDomain = ExecutionReady /\\ OriginalWordAccess (loads/stores: byte address rs1+imm = 0
    exactly; taken branch and jump targets aligned).  Fetches beyond the image read the default
    NOP (nop_rom); the 32-bit pc wraps, so a run that falls off the image re-enters it at pc 0
    after at most 2^30 NOPs (this is fast-forwarded, not ignored).  Returns
      'violation'  some step leaves the domain (or a word is unsupported)
      'closed'     the exact (pc, registers, memory) state repeats: in domain for the whole infinite run
      'bounded'    no violation in `steps` instructions (not a proof for the infinite run)."""
    if not 0 < len(words) <= 1 << 12:
        return 'violation'
    for w in words:
        if cv_is_supported(w) is None:
            return 'violation'
    regs = [0] * 32
    mem = bytearray(4)
    pc = 0
    n = len(words)
    seen = set()
    remaining = steps
    while remaining > 0:
        if pc % 4:
            return 'violation'
        idx = pc // 4
        if idx >= n:
            skip = (1 << 30) - idx          # NOPs until pc wraps to 0
            if skip >= remaining:
                return 'bounded'
            remaining -= skip
            pc = 0
            continue
        key = (pc, tuple(regs), bytes(mem))
        if key in seen:
            return 'closed'
        seen.add(key)
        name, rd, rs1, rs2, imm = decode(words[idx])
        a, c = regs[rs1], regs[rs2]
        if name in MEM_OPS and (a + imm) & M32 != 0:
            return 'violation'
        if name == 'jal' and (pc + imm) & 3:
            return 'violation'
        if name == 'jalr' and (((a + imm) & M32) & ~1) & 3:
            return 'violation'
        if name in BRANCHES:
            taken = {'beq': a == c, 'bne': a != c, 'blt': sext(32, a) < sext(32, c),
                     'bge': sext(32, a) >= sext(32, c), 'bltu': a < c, 'bgeu': a >= c}[name]
            if taken and (pc + imm) & 3:
                return 'violation'
        pc = isa_step(regs, pc, (name, rd, rs1, rs2, imm), mem)
        remaining -= 1
    return 'bounded'


def cv_domain_check(words, steps=3000):
    return cv_domain_status(words, steps) != 'violation'


def gen_cv_program(rng, max_len=48):
    """Random programs accepted by cv_domain_check.  Memory operations use a never-written
    register (value 0) with immediate 0, so the byte address is exactly 0; jumps are aligned;
    JALR bases are x0, a never-written register or an AUIPC-fed register (checked dynamically)."""
    while True:
        n = rng.randint(2, rng.choice([4, 8, 12, 20, 36, max_len]))
        zregs = [0] + rng.sample(range(1, 32), rng.choice([0, 1, 2]))
        others = [r for r in range(1, 32) if r not in zregs]
        pool = zregs[:1] + rng.sample(others, rng.choice([2, 3, 4, 6, 12, 28]))
        w = dict(data=rng.choice([30, 55, 80]), br=rng.choice([0, 8, 20]), jal=rng.choice([1, 3, 6]),
                 jalr=rng.choice([0, 2, 4]), load=rng.choice([0, 8, 20]), store=rng.choice([0, 8, 20]),
                 fence=rng.choice([0, 2]), auipc=rng.choice([0, 3]))
        kinds = list(w)
        words = []
        for i in range(n):
            kind = rng.choices(kinds, [w[k] for k in kinds])[0]
            if i == n - 1:
                kind = rng.choice(['jal', 'jal', 'jalr'])
            wr = lambda: rng.choice([r for r in pool if r != 0] + [0] + [rng.choice(others)])
            if kind == 'load':
                f3 = rng.choice([0, 1, 2, 4, 5])
                words.append((rng.choice(zregs) << 15) | (f3 << 12) | (wr() << 7) | 3)
            elif kind == 'store':
                f3 = rng.choice([0, 1, 2])
                words.append((rng.choice(pool) << 20) | (rng.choice(zregs) << 15) | (f3 << 12) | 35)
            elif kind == 'fence':
                words.append(4111)
            elif kind == 'auipc':
                words.append((0 << 12) | (rng.choice(pool + others) << 7) | 23)
            elif kind == 'jalr':
                base = rng.choice(zregs + pool)
                imm = (4 * rng.randrange(n) if base in zregs else 4 * rng.randrange(-4, 8)) + rng.choice([0, 0, 1])
                words.append(((imm & 0xFFF) << 20) | (base << 15) | (wr() << 7) | 103)
            else:
                x = gen_instruction(rng, kind, i, n, pool)
                if x & 0x7F not in (99, 35) and (x >> 7) & 31 in zregs[1:]:
                    x &= ~(31 << 7)       # never write the zero-valued base registers
                words.append(x)
        if cv_domain_status(words) == 'closed':      # in domain for the whole infinite ISA run
            return words


# ----------------------------------------------------------------------------------------
# Uniform design interface for traces / comparisons
# ----------------------------------------------------------------------------------------
class Design:
    def __init__(self, name, ast_paths, check, gen):
        self.name, self.check, self.gen = name, check, gen

    def run(self, sim, words):
        raise NotImplementedError


class BzDesign(Design):
    def __init__(self):
        super().__init__('bzeeno', None, jump_family_check, gen_program)

    def run(self, sim, words):
        r = BzeenoRun(sim, words)
        return lambda: (lambda pc, mid, end: (pc, end, 0))(*r.cycle())


class DkDesign(Design):
    def __init__(self):
        super().__init__('darkriscv', None, dark_closed_cfg, gen_dark_program)

    def run(self, sim, words):
        r = DarkRun(sim, words)
        return r.step


class CvDesign(Design):
    has_ram = True

    def __init__(self):
        super().__init__('cv32e40p', None, cv_domain_check, gen_cv_program)

    def run(self, sim, words):
        return CvRun(sim, words).step


# ----------------------------------------------------------------------------------------
# AngeloJacobo/RISC-V 5-stage RV32I (angelo5_top: core + combined registered-read memory; env is inside the AST)
# proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0
# ----------------------------------------------------------------------------------------
A5_RST, A5_CLK, A5_MEM = 1, 0, 2
A5_WB_CE, A5_WB_PC, A5_RF = 90, 76, 128      # writeback_ce, memoryaccess_pc (= pc of the instruction in stage 5), base_regfile
A5_BOOT = [(A5_RST, 0), (A5_CLK, 1), (A5_CLK, 0), (A5_CLK, 1), (A5_CLK, 0), (A5_RST, 1)]   # assert reset, 2 clocks, release after fall
A5_MEM_WORDS = 128


class Angelo5Run:
    """Reset (async), then cycles.  A commit is an instruction in the writeback stage (writeback_ce) in the state before the
    clock edge; its register write lands at that edge, so the RF returned by step() already contains it (same convention as DarkRun)."""

    def __init__(self, sim, words):
        assert len(words) <= A5_MEM_WORDS
        seed = [0] * sim.n
        seed[A5_RST] = 1
        seed[A5_MEM] = pack_words(words)
        self.sim = sim
        self.state = sim.run(seed, A5_BOOT)

    def step(self):
        s = self.state
        pc = s[A5_WB_PC] & M32 if s[A5_WB_CE] & 1 else None
        mid = self.sim.phase(s, A5_CLK, 1)
        self.state = self.sim.phase(mid, A5_CLK, 0)
        # base_regfile[31:1] is rebased by Verilator (index = addr-1): cell k is x(k+1); cell 31 is phantom.  Shift to word r = x_r.
        return pc, (self.state[A5_RF] << 32) & ((1 << 1024) - 1), 0


class Angelo5Design(Design):
    has_ram = False
    examples = [[0x00100093, 0x00200113, 0x002081b3, 0x0000006f], [0x00200113, 0x00c000e7, 0x00300193, 0x00400213, 0x0000006f]]

    def __init__(self, name='angelo5'):
        super().__init__(name, None, jump_family_check, gen_program)

    def run(self, sim, words):
        return Angelo5Run(sim, words).step


DESIGNS = dict(bzeeno=BzDesign(), darkriscv=DkDesign(), cv32e40p=CvDesign())
DESIGNS['angelo5'] = Angelo5Design()   # additive entry (AngeloJacobo/RISC-V)
DESIGNS['angelo5fix'] = Angelo5Design('angelo5fix')   # repaired derived copy (JALR bit-0 fix)
Design.has_ram = False
DkDesign.has_ram = True

# ----------------------------------------------------------------------------------------
# Steel (riscv-steel rvx_core @ 7af8290a, wrapper experiments/framework/steel/steel_top.v).  Additive entry.
# Environment: unified 512-byte synchronous memory (image seeded in `ram`), reset held 3 rising edges.
# Commit = a clock edge at which program_counter advances for a real instruction:
#   core.flush==0 & clock_enable & !load_pending & !store_pending & !take_trap  (pc = core.program_counter).
# proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0
# ----------------------------------------------------------------------------------------
ST_CLK, ST_RST, ST_RAM = 0, 1, 15
ST_CE, ST_STATE, ST_FLUSH, ST_RF, ST_INSTR, ST_LP, ST_PC, ST_SP, ST_TRAP = 170, 200, 203, 214, 217, 234, 253, 265, 268
ST_RESET_EDGES = 3
STEEL_SIGNALS = {ST_CLK: 'steel_top.clock', ST_RST: 'steel_top.reset', ST_RAM: 'steel_top.ram', ST_CE: 'steel_top.core.clock_enable',
                 ST_STATE: 'steel_top.core.current_state', ST_FLUSH: 'steel_top.core.flush',
                 ST_RF: 'steel_top.core.integer_file', ST_INSTR: 'steel_top.core.instruction', ST_LP: 'steel_top.core.load_pending',
                 ST_PC: 'steel_top.core.program_counter', ST_SP: 'steel_top.core.store_pending', ST_TRAP: 'steel_top.core.take_trap'}


def steel_rf_words(r):
    """integer_file holds x1..x31 in cells 0..30 (cell 31 = padding for the out-of-range rd=0 write)."""
    return [0] + [(r >> (32 * i)) & M32 for i in range(31)]


class SteelRun:
    def __init__(self, sim, words):
        self.sim = sim
        seed = [0] * sim.n
        seed[ST_RST] = 1
        seed[ST_RAM] = pack_words(list(words)[:128])
        s = sim.initialize(seed)
        for _ in range(ST_RESET_EDGES):
            s = sim.phase(sim.phase(s, ST_CLK, 1), ST_CLK, 0)
        self.state = sim.phase(s, ST_RST, 0)    # reset released after a falling edge
        self.trapped = False

    rtl = property(lambda self: self.state)   # alias used by cpu_isa_trace.validate

    def commit_pc(self):
        s = self.state
        if s[ST_TRAP] & 1:
            self.trapped = True
        if s[ST_FLUSH] == 0 and s[ST_CE] & 1 and not s[ST_LP] & 1 and not s[ST_SP] & 1 and not s[ST_TRAP] & 1:
            return s[ST_PC] & M32
        return None

    def step(self):
        pc = self.commit_pc()
        self.state = self.sim.phase(self.sim.phase(self.state, ST_CLK, 1), ST_CLK, 0)
        r = self.state[ST_RF]
        return pc, sum(((r >> (32 * i)) & M32) << (32 * (i + 1)) for i in range(31)), 0


class SteelDesign(Design):
    def __init__(self):
        super().__init__('steel', None, jump_family_check, gen_program)

    def run(self, sim, words):
        return SteelRun(sim, words).step


DESIGNS['steel'] = SteelDesign()   # additive entry (riscv-steel)


# ----------------------------------------------------------------------------------------
# srv32 (kuopinghsu/srv32 @ 7129bdcf, 3-stage; wrapper experiments/framework/srv32/srv32_env.v with ROM, synchronous read)
# proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0
# ----------------------------------------------------------------------------------------
SV_CLK, SV_RST, SV_ROM = 0, 1, 2
SV_STALL_R, SV_FLUSH, SV_IF_STALL, SV_EX_STALL, SV_EX_PC, SV_EX_FLUSH, SV_REGS = 232, 234, 236, 237, 241, 272, 244
SV_BOOT = [(SV_RST, 0), (SV_CLK, 1), (SV_CLK, 0), (SV_RST, 1)]   # assert reset (async), one clock under reset, release
SV_ROM_WORDS = 128
SV_SIGNALS = {SV_CLK: 'srv32_env.clk', SV_RST: 'srv32_env.resetb', SV_ROM: 'srv32_env.rom', SV_STALL_R: 'srv32_env.riscv.stall_r',
              SV_FLUSH: 'srv32_env.riscv.flush', SV_IF_STALL: 'srv32_env.riscv.if_stall', SV_EX_STALL: 'srv32_env.riscv.ex_stall',
              SV_EX_PC: 'srv32_env.riscv.ex_pc', SV_EX_FLUSH: 'srv32_env.riscv.ex_flush', SV_REGS: 'srv32_env.riscv.regs'}


class Srv32Run:
    """Reset (async), then cycles.  srv32 has no retirement signal under -DSYNTHESIS (wb_pc is `ifndef SYNTHESIS`), so the
    observer keeps ghost history variables equivalent to the debug-only ones: `ex_bubble` (the EX stage holds the NOP the core
    injects while `flush`=1 after reset, or its reset value) and `wb` (pc of the valid instruction in WB, or None).  Per clock
    edge with ex_stall=0 (settled state before the edge): an instruction in EX is valid iff !ex_flush and !ex_bubble; it moves to WB;
    the instruction that was in WB retires at this edge (its register write lands at it, so step()'s RF already contains it)."""

    def __init__(self, sim, words):
        assert len(words) <= SV_ROM_WORDS
        seed = [0] * sim.n
        seed[SV_RST] = 1
        seed[SV_ROM] = pack_words(words)
        self.sim = sim
        # power-up state: all registers 0, inputs applied, combinational logic settled (so that resetb 1->0 is a real negedge
        # for every derived copy of resetb, as in an event-driven simulator at t=0)
        self.state = sim.run(sim.lfp(seed), SV_BOOT)
        self.ex_bubble, self.wb = True, None

    def step(self):
        s = self.state
        retire = None
        if s[SV_EX_STALL] & 1 == 0 and s[SV_STALL_R] & 1 == 0:
            retire = self.wb
            self.wb = None if (s[SV_EX_FLUSH] & 1 or self.ex_bubble) else s[SV_EX_PC] & M32
        if s[SV_IF_STALL] & 1 == 0:
            self.ex_bubble = bool(s[SV_FLUSH] & 1)
        mid = self.sim.phase(s, SV_CLK, 1)
        self.state = self.sim.phase(mid, SV_CLK, 0)
        # regs[31:1] is rebased by Verilator (index = n-1) and padded to 32 cells: cell k is x(k+1).  Shift to word r = x_r.
        return retire, (self.state[SV_REGS] << 32) & ((1 << 1024) - 1), 0

    @property
    def rtl(self):      # cpu_isa_trace.validate reads the settled RTL state through `.rtl`
        return self.state


class Srv32Design(Design):
    has_ram = False
    examples = [[0x00100093, 0x00200113, 0x002081b3, 0x0000006f], [0x00200113, 0x00c000e7, 0x00300193, 0x00400213, 0x0000006f]]

    def __init__(self):
        super().__init__('srv32', None, jump_family_check, gen_program)

    def run(self, sim, words):
        return Srv32Run(sim, words).step


DESIGNS['srv32'] = Srv32Design()   # additive entry (kuopinghsu/srv32)


# ----------------------------------------------------------------------------------------
# NERV harness (experiments/framework/nerv/nerv_top.sv: unmodified nerv + ROM image + 1-word RAM; phase A)
# Signal ids are those of experiments/framework/generated/nerv/report.json (checked by tools/nerv_cosim.py).
# Reset: reset=1 over one rising edge, then reset=0; the first cycle afterwards is the reset_q cycle (no commit).
# Commit = nerv's RVFI-valid condition: cycle_insn && !mem_rd_enable (pc), or cycle_late_wr (a load: pc-4), or a
# trap/interrupt cycle (reported as pc | 1<<32 so that it can never match an ISA pc).
# proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.
# ----------------------------------------------------------------------------------------
NV_CLK, NV_RESET, NV_ROM, NV_RAM0, NV_IMEM_DATA = 0, 1, 2, 3, 4
NV_REGFILE, NV_INSN, NV_PC = 42, 43, 45
NV_MEM_RD_EN, NV_MEM_WR_EN, NV_INTR, NV_CYCLE_INSN, NV_TRAP, NV_LATE = 33, 29, 111, 112, 113, 114
NV_BOOT = [(NV_RESET, 1), (NV_CLK, 1), (NV_CLK, 0), (NV_RESET, 0)]
NV_SIGNALS = {'clock': 0, 'reset': 1, 'rom': 2, 'ram0': 3, 'imem_data': 4, 'uut.regfile': 42, 'uut.insn': 43,
              'uut.pc': 45, 'uut.mem_rd_enable': 33, 'uut.mem_wr_enable': 29, 'uut.cycle_intr': 111,
              'uut.cycle_insn': 112, 'uut.cycle_trap': 113, 'uut.cycle_late_wr': 114}


class NervRun:
    """Cycle-by-cycle execution; the observation is read from the settled state before the rising edge."""

    def __init__(self, sim, words, check_stable=False):
        self.sim = sim
        self.check_stable = check_stable
        seed = [0] * sim.n
        seed[NV_ROM] = pack_words(words)
        self.state = sim.run(sim.initialize(seed), NV_BOOT)

    def step(self):
        """(commit pc | None, raw regfile int (x0 word NOT masked), ram0 word) after one clock cycle."""
        sim, s = self.sim, self.state
        if self.check_stable:
            again = sim.comb_round(s[:])
            assert again == s, 'combinational state is not a fixed point after a phase'
        pc = s[NV_PC] & M32
        if s[NV_TRAP] & 1 or s[NV_INTR] & 1:
            commit = (1 << 32) | pc
        elif s[NV_CYCLE_INSN] & 1 and not s[NV_MEM_RD_EN] & 1:
            commit = pc
        elif s[NV_LATE] & 1:
            commit = (pc - 4) & M32
        else:
            commit = None
        self.state = sim.phase(sim.phase(s, NV_CLK, 1), NV_CLK, 0)
        return commit, self.state[NV_REGFILE], self.state[NV_RAM0] & M32


class NvDesign(Design):
    has_ram = True
    examples = [[0x00100093, 0x00200113, 0x002081b3, 0x0000006f], [0x00200113, 0x00c000e7, 0x00300193, 0x00400213, 0x0000006f]]

    def __init__(self):
        super().__init__('nerv', None, jump_family_check, gen_program)

    def run(self, sim, words):
        r = NervRun(sim, words)

        def step():
            pc, rf, mem = r.step()
            return pc, rf & ~M32, mem        # regfile[0] is written by `addi x0,..` but never read (rs=0 gates it)
        return step


DESIGNS['nerv'] = NvDesign()   # additive entry (NERV, YosysHQ)


def commit_list(pc):
    """A cycle's commits as a list: None -> [], int -> [pc], tuple (CV32E40P: 0, 1 or 2 commits) -> list."""
    if pc is None:
        return []
    return list(pc) if isinstance(pc, tuple) else [pc]


def trace(design, sim, words, cycles):
    """Per cycle: (commit pc | None, register-file word list, ram word 0)."""
    step = design.run(sim, words)
    out = []
    for _ in range(cycles):
        pc, rf, mem = step()
        out.append((pc, rf_from_int(rf), mem))
    return out


def validate_against_isa(design, sim, words, cycles):
    """Return None if the RTL trace matches the ISA reference, else a description of the mismatch."""
    return _compare_trace_to_isa(design, words, trace(design, sim, words, cycles))


def _compare_trace_to_isa(design, words, tr):
    pcs = [p for t in tr for p in commit_list(t[0])]
    ipcs, irf, imem = isa_trace(words, len(pcs))
    if pcs != ipcs:
        k = next(i for i, (a, b) in enumerate(zip(pcs, ipcs)) if a != b)
        return f'commit {k}: rtl pc {pcs[k]} vs isa pc {ipcs[k]}'
    n = 0
    for c, (pc, rf, mem) in enumerate(tr):
        n += len(commit_list(pc))
        exp = irf[n - 1] if n else [0] * 32
        if design.has_ram:
            # stores/loads to address 0 are architectural state too
            expm = imem[n - 1] if n else 0
            if mem != expm:
                return f'cycle {c} after {n} commits: ram word {mem:#x} vs isa {expm:#x}'
        if rf != exp:
            diff = [(i, a, b) for i, (a, b) in enumerate(zip(rf, exp)) if a != b][:3]
            return f'cycle {c} after {n} commits: rf differs {diff}'
    return None


# ----------------------------------------------------------------------------------------
# Cross-check against Coq itself (vm_compute of PhaseSemantics on a scratch file)
# ----------------------------------------------------------------------------------------
def coq_env():
    import os
    import subprocess
    cmd = 'source /opt/miniforge3/etc/profile.d/conda.sh && conda activate TP && env'
    out = subprocess.run(['bash', '-c', cmd], capture_output=True, text=True, check=True).stdout
    return dict(line.split('=', 1) for line in out.splitlines() if '=' in line)


def coq_phase_trace(root, ast_dir, ast_ns, ast_module, program_ident, seed, events, workdir, ast_file=None,
                    initialize=False):
    """Run `PhaseSemantics` in Coq (vm_compute) on `events` from `seed`; return all prefix states.

    root: project root.  ast_dir/ast_ns: -R mapping of the directory holding the compiled AST module
    (e.g. results/.../ConfiguredAST.vo -> GeneratedRuntimeInput).  If ast_file is given (a mutant AST
    source) it is compiled first inside `workdir` and used instead of ast_dir."""
    import subprocess
    work = Path(workdir)
    work.mkdir(parents=True, exist_ok=True)
    env = coq_env()
    flags = ['-R', f'{root}/src', 'Pfv']
    if ast_file is not None:
        d = work / 'ast'
        d.mkdir(exist_ok=True)
        dest = d / Path(ast_file).name
        dest.write_text(Path(ast_file).read_text())
        r = subprocess.run(['coqc'] + flags + ['-R', str(d), ast_ns, str(dest)], env=env, capture_output=True, text=True, cwd=d)
        if r.returncode:
            raise RuntimeError('coqc of AST failed: ' + r.stderr[-800:])
        flags += ['-R', str(d), ast_ns]
    else:
        flags += ['-R', str(ast_dir), ast_ns]
    evs = '; '.join(f'ev {s}%nat ({v})%Z' for s, v in events)
    seed_txt = '; '.join(f'({v})' for v in seed)
    text = f"""From Coq Require Import ZArith List.
Import ListNotations.
Require Import {ast_ns}.{ast_module} Lang.ExtendedSV Lang.ExtendedSVScalarHistory.
Import ExtendedSV ExtendedSVScalarHistory.
Open Scope Z_scope.
Definition prog := {program_ident}.
Definition ev (s:nat) (v:Z) := {{|changed_signal:=s; old_value:=0; new_value:=v|}}.
Definition seed : State := [{seed_txt}].
Definition evs : list Event := [{evs}].
Fixpoint trace p (es:list Event) (pre:State) : list State :=
  match es with [] => [pre] | e::t => pre :: trace p t (PhaseSemantics p e pre) end.
Eval vm_compute in (trace prog evs {'(initialize prog seed)' if initialize else 'seed'}).
"""
    f = work / 'Xcheck.v'
    f.write_text(text)
    r = subprocess.run(['coqc'] + flags + [str(f)], env=env, capture_output=True, text=True, cwd=work)
    if r.returncode:
        raise RuntimeError('coqc failed: ' + r.stderr[-1500:])
    body = r.stdout.split('=', 1)[1].rsplit('\n     :', 1)[0]
    body = body.replace('%Z', '')
    states = [[int(x) for x in re.findall(r'-?\d+', grp)] for grp in re.findall(r'\[([^\[\]]*)\]', body[body.index('[') + 1:])]
    return states


# ----------------------------------------------------------------------------------------
def load_sim(path):
    return Sim(parse_ast_file(path))


ROOT = Path(__file__).resolve().parent.parent
DEFAULT_AST = dict(
    bzeeno=ROOT / 'results/pending-configured-input-20261024-a4-bzeeno/ConfiguredAST.v',
    darkriscv=ROOT / 'experiments/framework/generated/dark38-derived/DarkRISCV38DerivedAST.v',
    cv32e40p=ROOT / 'src/Ex/Generated/CV32E40PExtendedAST.v')
DEFAULT_AST['steel'] = ROOT / 'experiments/framework/generated/steel/SteelAST.v'
DEFAULT_AST['angelo5'] = ROOT / 'experiments/framework/generated/angelo5/Angelo5AST.v'
DEFAULT_AST['angelo5fix'] = ROOT / 'experiments/framework/generated/angelo5-fixed/Angelo5FixedAST.v'
DEFAULT_AST['srv32'] = ROOT / 'experiments/framework/generated/srv32/Srv32AST.v'
DEFAULT_AST['nerv'] = ROOT / 'experiments/framework/generated/nerv/NervAST.v'
COQ_PROGRAM = dict(
    bzeeno=('GeneratedRuntimeInput', 'ConfiguredAST', 'BzeenoLoadUseJalASTConfigured3122be4a95.bzeeno_load_use_jal_program',
            ROOT / 'results/pending-configured-input-20261024-a4-bzeeno'),
    darkriscv=('Dark38', 'DarkRISCV38DerivedAST', 'DarkRISCV38DerivedAST.dark38_program',
               ROOT / 'experiments/framework/generated/dark38-derived'))

# programs that appear in the Coq example modules (accepted and rejected)
BZ_EXAMPLES_ACCEPTED = [
    [0x00100093, 0x00000067], [0x00200113, 0x00c000e7, 0x00300193, 0x00400213, 0x0000006f], [0x00100093, 0x000000e7]]
BZ_EXAMPLES_REJECTED = [[0x00100093, 0x04000067], [0x00100093, 0x00008067], [0x00100093, 0x00200067]]


# CV32E40P: the 38-instruction DarkRISCV image has the same static shape (memory ops x0+0, JALR x0+0);
# plus the smallest startup examples
CV_EXAMPLES = [[0x00100093, 0x00200113, 0x002081b3, 0x0000006f]]


CV_REJECTED = [
    [0x00100093, 0x00001073],            # CSRRW (not in the 38)
    [0x00100093, 0x00000073],            # ECALL
    [0x00100093, 0x00100073],            # EBREAK
    [0x00100093, 0x0ff0000f],            # FENCE (only FENCE.I is in the 38)
    [0x00100093, 0x00008082],            # compressed word (low bits != 3)
    [0x00100093, 0x00102223],            # sw x1,4(x0): byte address 4
    [0x00100093, 0x0010a023],            # sw x1,0(x1): byte address 1
    [0x00100093, 0x00000163],            # beq x0,x0,+2: taken, misaligned target
    [0x00100093, 0x00208067],            # jalr x0,2(x1): target 2 (after &~1), misaligned
]
CV_ACCEPTED_EXTRA = [
    [0x00100093, 0x00402023, 0x0000006f],  # sw x4,0(x0)
    [0x00100093, 0x00001163, 0x0000006f],  # bne x0,x0,+2: never taken, so alignment is irrelevant
]


def program_set(design, n, seed):
    """Deterministic list of n programs accepted by the design's checker."""
    rng = random.Random(seed)
    progs = [list(w) for w in {'bzeeno': BZ_EXAMPLES_ACCEPTED, 'darkriscv': [DARK_IMAGE38],
                               'cv32e40p': CV_EXAMPLES}.get(design.name, getattr(design, 'examples', []))]
    while len(progs) < n:
        progs.append(design.gen(rng))
    return progs[:n]


def _op(f, imm):
    return (imm << 20) | (1 << 15) | (f << 12) | 128 | 19


def _reg(f, f7):
    return (f7 << 25) | (2 << 20) | (1 << 15) | (f << 12) | 128 | 51


DARK_IMAGE38 = ([4096 + 128 + 55, 4096 + 128 + 23] + [_op(f, 1) for f in (0, 2, 3, 4, 6, 7, 1, 5)] + [_op(5, 1025)]
                + [_reg(0, 0), _reg(0, 32), _reg(1, 0), _reg(2, 0), _reg(3, 0), _reg(4, 0), _reg(5, 0), _reg(5, 32), _reg(6, 0), _reg(7, 0)]
                + [(2 << 20) | (1 << 15) | (f << 12) | 512 | 99 for f in (0, 1, 4, 5, 6, 7)]
                + [(f << 12) | 128 | 3 for f in (0, 1, 2, 4, 5)] + [(1 << 20) | (f << 12) | 35 for f in (0, 1, 2)]
                + [4194304 + 128 + 111, 4111, 103])


G_VAL = {}


def _validate_one(item):
    """(mismatch text | None, committed mnemonic counts) for one program (single trace run)."""
    k, w = item
    design, sim, cycles = G_VAL['design'], G_VAL['sim'], G_VAL['cycles']
    tr = trace(design, sim, w, cycles)
    pcs = [p for t in tr for p in commit_list(t[0])]
    mismatch = _compare_trace_to_isa(design, w, tr)
    counts = {}
    for pc in pcs:
        m = decode(w[pc // 4] if pc // 4 < len(w) else CV_NOP)[0]
        counts[m] = counts.get(m, 0) + 1
    return mismatch, counts


def cmd_validate(a):
    design = DESIGNS[a.design]
    sim = load_sim(a.ast or DEFAULT_AST[a.design])
    t0 = time.time()
    # (b) checker cross-check on the Coq example programs
    report = dict(design=a.design, ast=str(a.ast or DEFAULT_AST[a.design]), seed=a.seed)
    if a.design == 'bzeeno':
        assert all(jump_family_check(w) for w in BZ_EXAMPLES_ACCEPTED)
        assert not any(jump_family_check(w) for w in BZ_EXAMPLES_REJECTED)
        report['checker_examples'] = dict(accepted=len(BZ_EXAMPLES_ACCEPTED), rejected=len(BZ_EXAMPLES_REJECTED))
    elif a.design == 'cv32e40p':
        assert all(cv_domain_check(w) for w in CV_EXAMPLES)
        assert cv_domain_check(DARK_IMAGE38) and all(cv_domain_check(w) for w in CV_ACCEPTED_EXTRA)
        assert not any(cv_domain_check(w) for w in CV_REJECTED)
        report['checker_examples'] = dict(accepted=len(CV_EXAMPLES) + 1 + len(CV_ACCEPTED_EXTRA), rejected=len(CV_REJECTED))
    elif a.design == 'srv32':
        assert all(jump_family_check(w) for w in Srv32Design.examples)
        report['checker_examples'] = dict(accepted=len(Srv32Design.examples), rejected=0)
    elif a.design in ('angelo5', 'angelo5fix'):
        assert all(jump_family_check(w) for w in Angelo5Design.examples)
        report['checker_examples'] = dict(accepted=len(Angelo5Design.examples), rejected=0)
    else:
        assert dark_closed_cfg(DARK_IMAGE38)
        report['checker_examples'] = dict(accepted=1, rejected=0)
    progs = program_set(design, a.programs, a.seed)
    assert all(design.check(w) for w in progs)
    mnem = {}
    commits = 0
    bad = []
    G_VAL.update(design=design, sim=sim, cycles=a.cycles)
    jobs = getattr(a, 'jobs', 1)
    if jobs > 1:
        import multiprocessing as mp
        with mp.get_context('fork').Pool(jobs) as pool:
            results = pool.map(_validate_one, list(enumerate(progs)), chunksize=4)
    else:
        results = [_validate_one(x) for x in enumerate(progs)]
    for k, (mismatch, counts) in enumerate(results):
        if mismatch:
            bad.append(dict(program=k, words=[hex(x) for x in progs[k]], mismatch=mismatch))
        for m, c in counts.items():
            mnem[m] = mnem.get(m, 0) + c
            commits += c
    report.update(programs=len(progs), cycles_each=a.cycles, total_cycles=len(progs) * a.cycles,
                  committed_instructions=commits, mismatches=len(bad), first_mismatches=bad[:5],
                  committed_by_mnemonic=dict(sorted(mnem.items())), seconds=round(time.time() - t0, 1))
    print(json.dumps(report, indent=1))
    if a.out:
        Path(a.out).write_text(json.dumps(report, indent=1) + '\n')
    return 1 if bad else 0


CV_COQ_TEMPLATE = """From Coq Require Import ZArith List.
Import ListNotations.
Require Import Lang.ExtendedSV Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PReq39Trace
  Ex.External.CV32E40PAddiReachability Ex.External.CV32E40PTwoCommitITreeInterface
  Ex.External.CV32E40PLoadOrderedObservation Ex.External.CV32E40PFull38RetirementAdapter.
Import ExtendedSV CV32E40PReq39Trace CV32E40PAddiReachability CV32E40PTwoCommitITreeInterface
  CV32E40PLoadOrderedObservation CV32E40PFull38RetirementAdapter.
Open Scope Z_scope.
Definition image : InstructionImage := [%(words)s].
Definition tok (o : option IssueToken) : list Z :=
  match o with Some t => [token_pc t; token_instruction t] | None => [] end.
Definition cc (c : CycleCommits) : list Z :=
  match c with SilentCycle => [] | OneCommit a => [a] | TwoCommits a b => [a; b] end.
Definition opt (o : option Z) : list Z := match o with Some a => [a] | None => [] end.
Definition obs (s : Full38Observation) : list (list Z) :=
  let core := observed_core (full38_base s) in
  let ts := physical_state core in
  [cc (full38_observed_commits image s); trace_rtl ts; [trace_memory_word ts]; tok (pending_token core);
   tok (observed_wb (full38_base s)); opt (trace_instruction_pending ts);
   match trace_data_pending ts with
   | Some r => [obi_data_address r; if obi_data_write r then 1 else 0; obi_data_byte_enable r; obi_data_write_data r]
   | None => [] end;
   [full38_cursor s]; opt (full38_pending_jump s)].
Fixpoint tr (n : nat) (s : Full38Observation) : list (list (list Z)) :=
  match n with O => [obs s] | S k => obs s :: tr k (advance_full38_monitor image s) end.
Eval vm_compute in (tr %(n)d%%nat full38_reset).
"""


def parse_nested(text):
    """Parse Coq's printed nested lists of Z into python lists of ints."""
    toks = re.findall(r'\[|\]|-?\d+', text)
    stack = [[]]
    for t in toks:
        if t == '[':
            stack.append([])
        elif t == ']':
            x = stack.pop()
            stack[-1].append(x)
        else:
            stack[-1].append(int(t))
    return stack[0][0]


def cv_coq_trace(words, cycles, workdir):
    import subprocess
    work = Path(workdir)
    work.mkdir(parents=True, exist_ok=True)
    f = work / 'CvCheck.v'
    f.write_text(CV_COQ_TEMPLATE % dict(words='; '.join(str(w) for w in words), n=cycles))
    flags = ['-R', f'{ROOT}/src', 'Pfv', '-R', f'{ROOT}/dep/coqutil/src/coqutil/', 'coqutil',
             '-R', f'{ROOT}/dep/riscv-coq/src/riscv/', 'riscv']
    r = subprocess.run(['coqc'] + flags + [str(f)], env=coq_env(), capture_output=True, text=True, cwd=work)
    if r.returncode:
        raise RuntimeError('coqc failed: ' + r.stderr[-1500:])
    body = r.stdout.split('=', 1)[1].rsplit('\n     :', 1)[0].replace('%Z', '')
    return parse_nested(body)


def cv_python_trace(sim, words, cycles):
    run = CvRun(sim, words)
    out = []
    for _ in range(cycles + 1):
        snap = run.snapshot()
        run.step()
        out.append([list(run.last_commits)] + [snap[0]] + snap[1:])
    return out


def cmd_coq_cv(a):
    sim = load_sim(a.ast or DEFAULT_AST['cv32e40p'])
    rng = random.Random(a.seed)
    ok = True
    for k in range(a.programs):
        if a.words:
            words = [int(x, 0) for x in a.words.split(',')]
            assert cv_domain_check(words), 'witness program rejected by the checker'
        else:
            words = list(CV_COQ_PROGRAMS[k]) if k < len(CV_COQ_PROGRAMS) else gen_cv_program(rng, 16)
        t0 = time.time()
        py = cv_python_trace(sim, words, a.cycles)
        coq = cv_coq_trace(words, a.cycles, a.work + f'/c{k}')
        same = len(py) == len(coq) and all(x == y for x, y in zip(py, coq))
        first = next((i for i, (x, y) in enumerate(zip(py, coq)) if x != y), None)
        ncommits = sum(len(x[0]) for x in py)
        print(f'program {k}: {len(words)} words, {a.cycles + 1} observations ({a.cycles} cycles, {ncommits} commits), '
              f'{len(py[0][1])} signals each, equal={same}' + (f' first differing step {first}' if first is not None else '')
              + f' ({time.time() - t0:.0f}s)', flush=True)
        ok &= same
    return 0 if ok else 1


# short programs hitting loads/stores/branches/jumps early so that a few cycles cover them
CV_COQ_PROGRAMS = [
    [0x00100093, 0x00200113, 0x002081b3, 0x0000006f],
    [0x00500093, 0x00102023, 0x00002183, 0x00318233, 0x00000263, 0x0000006f],
    [0x00100093, 0x0080006f, 0x00200113, 0x00300193, 0x00409463, 0x00000067],
]


def cmd_coq(a):
    if a.design == 'cv32e40p':
        return cmd_coq_cv(a)
    design = DESIGNS[a.design]
    ns, mod, ident, d = COQ_PROGRAM[a.design]
    ast = a.ast or DEFAULT_AST[a.design]
    sim = load_sim(ast)
    rng = random.Random(a.seed)
    ok = True
    for k in range(a.programs):
        if a.words:
            words = [int(x, 0) for x in a.words.split(',')]
            assert design.check(words), 'witness program rejected by the checker'
        else:
            words = list(BZ_EXAMPLES_ACCEPTED[1]) if (k == 0 and a.design == 'bzeeno') else design.gen(rng)
        if a.design == 'bzeeno':
            seed = [0] * sim.n
            seed[BZ_ROM] = pack_words(words)
            seed[BZ_RESETN] = 1
            events = BZ_BOOT + [(BZ_CLK, 1), (BZ_CLK, 0)] * a.cycles
            sim_states = [seed]
            st = seed
            for sig, v in events:
                st = sim.phase(st, sig, v)
                sim_states.append(st)
            coq_states = coq_phase_trace(str(ROOT), d, ns, mod, ident, seed, events, a.work + f'/b{k}',
                                         ast_file=a.ast if a.ast else None)
        else:
            # Dark: replay the sequence of event applications performed by DarkRun in Coq
            seed0 = [0] * sim.n
            seed0[DK_RES] = 1; seed0[6] = 1; seed0[17] = 1
            ev_list, sim_states = dark_event_log(sim, words, a.cycles)
            events = [(s_, v_) for s_, v_ in ev_list]
            init_state = sim.initialize(seed0)
            coq_states = coq_phase_trace(str(ROOT), d, ns, mod, ident, seed0, events, a.work + f'/d{k}',
                                         ast_file=a.ast if a.ast else None, initialize=True)
            sim_states = [init_state] + sim_states
        n = min(len(coq_states), len(sim_states))
        same = all(coq_states[i] == sim_states[i][:len(coq_states[i])] and not any(sim_states[i][len(coq_states[i]):])
                   for i in range(n))
        print(f'program {k}: {len(words)} words, {len(events)} events, {n} states compared, equal={same}')
        ok &= same
    return 0 if ok else 1


def dark_event_log(sim, words, cycles):
    """The sequence of PhaseSemantics events Dark's actual_cycle applies (rise, response, fall, RAM
    response, reset drop), flattened.  Only sequential composition: the RAM and the driven-state
    based decisions do not alter the state transformations, so they are replayed as a plain
    phase_run for the Coq cross-check by recording the event values chosen by the Python harness."""
    run = DarkRun(sim, words)
    events, states = [], []
    real_phase = sim.phase

    def logging_phase(pre, sig, v):
        post = real_phase(pre, sig, v)
        events.append((sig, v))
        states.append(post)
        return post
    sim.phase = logging_phase
    try:
        for _ in range(cycles):
            driven_pre = len(events)
            run.cycle()
    finally:
        sim.phase = real_phase
    return events, states


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest='cmd', required=True)
    v = sub.add_parser('validate', help='compare the original design AST against the ISA reference')
    v.add_argument('--design', choices=list(DESIGNS), required=True)
    v.add_argument('--jobs', type=int, default=1)
    v.add_argument('--ast')
    v.add_argument('--programs', type=int, default=200)
    v.add_argument('--cycles', type=int, default=400)
    v.add_argument('--seed', type=int, default=20261102)
    v.add_argument('--out')
    c = sub.add_parser('coq', help='compare PhaseSemantics (Coq vm_compute) with the simulator')
    c.add_argument('--design', choices=list(DESIGNS), required=True)
    c.add_argument('--ast', help='mutant AST source to cross-check instead of the original')
    c.add_argument('--programs', type=int, default=2)
    c.add_argument('--cycles', type=int, default=8)
    c.add_argument('--seed', type=int, default=7)
    c.add_argument('--words', help='comma separated hex words (default: random accepted programs)')
    c.add_argument('--work', required=True)
    a = ap.parse_args(argv)
    return {'validate': cmd_validate, 'coq': cmd_coq}[a.cmd](a)


if __name__ == '__main__':
    sys.exit(main())
