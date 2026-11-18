#!/usr/bin/env python3
"""Generic non-vacuity check for generated fact lists (template route).

A theorem `CombLFP .. -> FactsHold fixed facts -> ...` is vacuous if no assignment of the signals satisfies all facts
(`eval_expr s e = z` for every (e, z)), e.g. when a scenario says `guard = 1` and also pins a leaf of the guard to 0.  This tool
asks z3 for a satisfying assignment of the facts, treating every signal as a free bit-vector (the same translation as
tools/cpu_mutant_equivalence.py).  It is a necessary condition only (the facts are not checked against the circuit), but it catches
contradictory scenarios.

Library use (generators):  from cpu_tmpl_factcheck import check_sets, assert_all_sat
   check_sets({name: [(expr_tuple_or_coq_text, value), ...]}) -> {name: ('sat', model) | ('unsat', None) | ('unknown', None)}
   (runs z3 in a subprocess of /opt/miniforge3/envs/lhq/bin/python, so any interpreter can call it)
CLI (any interpreter):  python tools/cpu_tmpl_factcheck.py FILE.v ...   scans `Definition facts_X:Facts:=[..]` and
   `Definition prem_X .. := norm w (read_signal f id%nat) = v /\\ ..` and reports UNSAT sets; exit 1 if any.
Untrusted tool (a filter before Coq). proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import json
import re
import subprocess
import sys
from pathlib import Path

Z3PY = '/opt/miniforge3/envs/lhq/bin/python'
HERE = Path(__file__).resolve().parent
TOK = re.compile(r'\(|\)|\[|\]|,|;|-?\d+|[A-Za-z_][\w.]*|%nat')
ARITY = {'EConst': ('n', 'z'), 'EVar': ('n', 'n'), 'ESel': ('n', 'e', 'e'), 'EConcat': ('n', 'e', 'e'),
         'EReplicate': ('n', 'n', 'e'), 'EExtend': ('n', 'b', 'e'), 'EUnary': ('n', 'o', 'e'),
         'EBinary': ('n', 'o', 'e', 'e'), 'ECond': ('n', 'e', 'e', 'e')}


def parse_expr(toks, pos):
    t = toks[pos]
    if t == '(':
        pos += 1
        head = toks[pos]
        if head in ARITY:
            pos += 1
            node = [head]
            for k in ARITY[head]:
                if k == 'e':
                    sub, pos = parse_expr(toks, pos)
                    node.append(sub)
                else:
                    node.append(toks[pos]); pos += 1
                    if pos < len(toks) and toks[pos] == '%nat':
                        pos += 1
        else:
            node, pos = parse_expr(toks, pos)
        assert toks[pos] == ')', toks[pos:pos + 4]
        return node, pos + 1
    raise ValueError(f'bad expr at {toks[pos:pos+4]}')


def parse_facts(text):
    """text = '[(e,z); (e,z); ...]' (Coq) -> [(node, int)]"""
    toks = [t for t in TOK.findall(text)]
    pos = 0
    assert toks[pos] == '['
    pos += 1
    out = []
    while toks[pos] != ']':
        assert toks[pos] == '(', toks[pos:pos + 4]
        pos += 1
        e, pos = parse_expr(toks, pos)
        assert toks[pos] == ','
        pos += 1
        v = int(toks[pos]); pos += 1
        if toks[pos] == '%Z':
            pos += 1
        assert toks[pos] == ')'
        pos += 1
        out.append((e, v))
        if toks[pos] == ';':
            pos += 1
    return out


def scan(text):
    """-> {name: [(node, value)]} for literal fact lists and premise conjunctions of a Coq file"""
    res = {}
    for m in re.finditer(r'Definition (facts_\w+)\s*:\s*Facts\s*:=\s*(\[)', text):
        i, depth = m.end(2) - 1, 0
        j = i
        while True:
            c = text[j]
            depth += (c == '[') - (c == ']')
            j += 1
            if depth == 0:
                break
        res[m.group(1)] = parse_facts(text[i:j])
    for m in re.finditer(r'Definition (prem_\w+)\s*\(\s*\w+\s*:\s*State\s*\)\s*:\s*Prop\s*:=([^.]*)\.', text):
        facts = []
        for w, sig, v in re.findall(r'norm (\d+)\s*\(read_signal \w+ (\d+)%nat\)\s*=\s*(-?\d+)', m.group(2)):
            facts.append((['EVar', w, sig], int(v)))
        if facts:
            res[m.group(1)] = facts
    return res


def to_node(e):
    """python AST tuple (cpu_tmpl_ast style) or Coq text -> parsed node"""
    if isinstance(e, str):
        toks = TOK.findall(e)
        return parse_expr(toks, 0)[0]
    import cpu_tmpl_ast as T
    return parse_expr(TOK.findall(T.coq(e)), 0)[0]


def _solve(sets, timeout_ms=20000):
    import z3
    sys.path.insert(0, str(HERE))
    import cpu_mutant_equivalence as M
    out = {}
    for name, facts in sets.items():
        tr = M.Translator()
        s = z3.Solver()
        s.set('timeout', timeout_ms)
        for e, v in facts:
            w = int(e[1])
            s.add(tr.ev(e) == z3.BitVecVal(int(v) % (1 << w), w))
        r = s.check()
        out[name] = ['sat' if r == z3.sat else 'unsat' if r == z3.unsat else 'unknown']
    return out


def check_sets(named):
    """named: {name: [(expr, value)]}, expr = generator tuple, Coq text or parsed node"""
    payload = {}
    for n, fl in named.items():
        payload[n] = [(e if isinstance(e, list) else to_node(e), v) for e, v in fl]
    r = subprocess.run([Z3PY, str(Path(__file__).resolve()), '--solve'], input=json.dumps(payload), capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError('factcheck solver failed: ' + r.stderr[-2000:])
    return {k: tuple(v) + (None,) * (2 - len(v)) for k, v in json.loads(r.stdout).items()}


def assert_all_sat(named, what=''):
    res = check_sets(named)
    bad = sorted(k for k, v in res.items() if v[0] != 'sat')
    if bad:
        raise SystemExit(f'factcheck {what}: {len(bad)} of {len(named)} fact sets are not satisfiable (vacuous): {bad[:5]}...')
    return res


if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == '--solve':
        data = json.loads(sys.stdin.read())
        print(json.dumps(_solve(data)))
        sys.exit(0)
    total = bad = 0
    for f in sys.argv[1:]:
        sets = scan(Path(f).read_text())
        if not sets:
            print(f'{f}: no literal fact lists / premise conjunctions found')
            continue
        res = check_sets(sets)
        unsat = sorted(k for k, v in res.items() if v[0] == 'unsat')
        unk = sorted(k for k, v in res.items() if v[0] == 'unknown')
        total += len(sets)
        bad += len(unsat)
        print(f'{f}: {len(sets)} sets, {len(sets)-len(unsat)-len(unk)} sat, {len(unsat)} UNSAT, {len(unk)} unknown')
        if unsat:
            print('  UNSAT e.g.:', unsat[:6])
    sys.exit(1 if bad else 0)
