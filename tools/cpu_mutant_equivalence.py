#!/usr/bin/env python3
"""Screen AST mutants for local equivalence with z3 (fault-injection experiment).

For each mutant of `cpu_rtl_mutants.py`, take the maximal expression that
contains the mutated site in its process body (an argument of an assignment,
an `if` guard or an lvalue index), translate the original and the mutated
expression to SMT bit-vectors following `ExtendedSV.eval_expr` exactly, and
ask z3 whether some state makes them differ:
  equivalent      unsat: the process computes the same function, so the mutant
                  is equivalent and is excluded from the detection denominator;
  not_equivalent  sat, with a witness (signal values);
  unknown         timeout or unsupported construct.
Local inequivalence does not imply the fault is observable at the ISA level
(it may sit in logic the verified programs never reach); that is tagged separately.
Run with a Python that has z3 (e.g. /opt/miniforge3/envs/lhq/bin/python).
"""
import argparse
import json
import re
from pathlib import Path

import z3

TOKEN = re.compile(r'\(|\)|-?\d+|[A-Za-z_][\w.]*')
ARITY = {'EConst': ('n', 'z'), 'EVar': ('n', 'n'), 'ESel': ('n', 'e', 'e'), 'EConcat': ('n', 'e', 'e'),
         'EReplicate': ('n', 'n', 'e'), 'EExtend': ('n', 'b', 'e'), 'EUnary': ('n', 'o', 'e'),
         'EBinary': ('n', 'o', 'e', 'e'), 'ECond': ('n', 'e', 'e', 'e')}


def parse(text):
    toks = TOKEN.findall(text)
    pos = 0

    def term():
        nonlocal pos
        t = toks[pos]
        if t == '(':
            pos += 1
            head = toks[pos]
            if head in ARITY:
                pos += 1
                node = [head] + [term() for _ in ARITY[head]]
            else:  # parenthesised atom such as (-1)
                node = term()
            assert toks[pos] == ')', toks[pos:pos + 3]
            pos += 1
            return node
        pos += 1
        return t
    node = term()
    return node


def width(e):
    return int(e[1])


def to_bv(v, w):
    return z3.ZeroExt(w - v.size(), v) if v.size() < w else z3.Extract(w - 1, 0, v)


class Translator:
    def __init__(self):
        self.signals = {}

    def var(self, sig, w):
        x = self.signals.get(sig)
        if x is None or x.size() < w:
            x = z3.BitVec(f's{sig}', 64 if w <= 64 else w)
            self.signals[sig] = x
        return z3.Extract(w - 1, 0, x)

    def ev(self, e):
        """Bit-vector of exactly width(e) bits, equal to eval_expr (which is norm w)."""
        h = e[0]
        w = width(e)
        if h == 'EConst':
            return z3.BitVecVal(int(e[2]) % (1 << w), w)
        if h == 'EVar':
            return self.var(int(e[2]), w)
        if h == 'ESel':
            b, l = self.ev(e[2]), self.ev(e[3])
            m = max(w, b.size(), l.size()) + 1
            return z3.Extract(w - 1, 0, z3.LShR(to_bv(b, m), to_bv(l, m)))
        if h == 'EConcat':
            hi, lo = self.ev(e[2]), self.ev(e[3])
            return to_bv(z3.Concat(hi, lo), w)
        if h == 'EReplicate':
            body = self.ev(e[3])
            n = int(e[2])
            if n == 0:
                return z3.BitVecVal(0, w)
            return to_bv(z3.Concat(*([body] * n)) if n > 1 else body, w)
        if h == 'EExtend':
            body = self.ev(e[3])
            m = max(w, body.size())
            v = z3.SignExt(m - body.size(), body) if e[2] == 'true' else to_bv(body, m)
            return z3.Extract(w - 1, 0, v)
        if h == 'EUnary':
            body = self.ev(e[3])
            m = max(w, body.size())
            b = to_bv(body, m)
            if e[2] == 'UNot':
                return z3.Extract(w - 1, 0, ~b)
            if e[2] == 'UNegate':
                return z3.Extract(w - 1, 0, -b)
            return to_bv(z3.If(body != 0, z3.BitVecVal(1, 1), z3.BitVecVal(0, 1)), w)
        if h == 'EBinary':
            op, l, r = e[2], self.ev(e[3]), self.ev(e[4])
            m = max(w, l.size(), r.size()) + 1
            L, R = to_bv(l, m), to_bv(r, m)
            one, zero = z3.BitVecVal(1, 1), z3.BitVecVal(0, 1)
            boolz = lambda c: to_bv(z3.If(c, one, zero), w)
            if op in ('BAnd', 'BOr', 'BXor', 'BAdd', 'BSub', 'BMul'):
                v = {'BAnd': L & R, 'BOr': L | R, 'BXor': L ^ R, 'BAdd': L + R, 'BSub': L - R, 'BMul': L * R}[op]
                return z3.Extract(w - 1, 0, v)
            if op == 'BEq':
                return boolz(L == R)
            if op == 'BNeq':
                return boolz(L != R)
            if op == 'BLtU':
                return boolz(z3.ULT(L, R))
            if op == 'BGtU':
                return boolz(z3.UGT(L, R))
            if op == 'BGtS':
                ls = z3.SignExt(m - l.size(), l)
                rs = z3.SignExt(m - r.size(), r)
                return boolz(ls > rs)
            if op == 'BShiftL':
                return z3.Extract(w - 1, 0, L << R)
            if op == 'BShiftR':
                return z3.Extract(w - 1, 0, z3.LShR(L, R))
            if op == 'BShiftRS':
                return z3.Extract(w - 1, 0, z3.SignExt(m - l.size(), l) >> R)
        if h == 'ECond':
            g, y, n = self.ev(e[2]), self.ev(e[3]), self.ev(e[4])
            return z3.If(g == 0, to_bv(n, w), to_bv(y, w))
        raise ValueError('unsupported ' + h)


def enclosing_expr(body, a, b):
    """Maximal parenthesised E-term of body containing [a, b)."""
    best = None
    stack = []
    for i, c in enumerate(body):
        if c == '(':
            stack.append(i)
        elif c == ')':
            s = stack.pop()
            if s <= a and i + 1 >= b and re.match(r'\(E[A-Z]\w* ', body[s:s + 12]):
                if best is None or s < best[0]:
                    best = (s, i + 1)
    return best


def check(original_body, mutated_body, timeout_ms=20000):
    # locate the changed window
    a = 0
    while a < min(len(original_body), len(mutated_body)) and original_body[a] == mutated_body[a]:
        a += 1
    bo, bm = len(original_body), len(mutated_body)
    while bo > a and bm > a and original_body[bo - 1] == mutated_body[bm - 1]:
        bo, bm = bo - 1, bm - 1
    so = enclosing_expr(original_body, a, max(bo, a + 1))
    sm = enclosing_expr(mutated_body, a, max(bm, a + 1))
    if so is None or sm is None or so[0] != sm[0]:
        # whole assignment RHS replaced, or a bare constant: compare the minimal spans
        so = so or (a, bo)
        sm = (so[0], so[1] + (bm - bo))
    eo, em = original_body[so[0]:so[1]], mutated_body[sm[0]:sm[1]]
    try:
        t = Translator()
        x, y = t.ev(parse(eo)), t.ev(parse(em))
    except Exception as exc:  # unsupported construct
        return dict(verdict='unknown', reason=str(exc)[:200], original_expr=eo[:300], mutated_expr=em[:300])
    s = z3.Solver()
    s.set('timeout', timeout_ms)
    m = max(x.size(), y.size())
    s.add(to_bv(x, m) != to_bv(y, m))
    r = s.check()
    out = dict(original_expr=eo[:300], mutated_expr=em[:300])
    if r == z3.unsat:
        out['verdict'] = 'equivalent'
    elif r == z3.sat:
        mod = s.model()
        out['verdict'] = 'not_equivalent'
        out['witness'] = {str(d): mod[d].as_long() for d in mod.decls()}
    else:
        out['verdict'] = 'unknown'
        out['reason'] = 'z3 ' + str(r)
    return out


PROCESS = re.compile(r'(?m)^Definition (process_\d+) : Process := (.*)$')


def run(mutants_json, output=None):
    data = json.loads(Path(mutants_json).read_text())
    cache = {}
    results = {}
    for row in data['mutants']:
        f = row['files'][0]
        if f['original'] not in cache:
            cache[f['original']] = dict(PROCESS.findall(Path(f['original']).read_text()))
        name = f'process_{row["process"]}'
        mutated = dict(PROCESS.findall(Path(f['mutant']).read_text()))[name]
        results[row['id']] = dict(type=row['type'], **check(cache[f['original']][name], mutated))
    counts = {}
    for r in results.values():
        counts[r['verdict']] = counts.get(r['verdict'], 0) + 1
    report = dict(source=str(mutants_json), counts=counts, mutants=results)
    if output:
        Path(output).write_text(json.dumps(report, indent=2) + '\n')
    return report


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('mutants_json')
    p.add_argument('--output')
    a = p.parse_args()
    r = run(a.mutants_json, a.output)
    print(json.dumps(r['counts'], indent=2))
