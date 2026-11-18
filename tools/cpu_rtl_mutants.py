#!/usr/bin/env python3
"""Seeded RTL fault injection at the imported-AST level (fault-injection experiment).

The Verilog frontends (Verilator XML -> ExtendedSV) are a trusted, unmechanised
translation and Verilator is not installed here, so a fault is injected into
the imported Coq AST: one process body is changed by one classic RTL mutation
operator. Each mutant is recorded with its process, RTL instance and source
line, and the original/mutated expression text, so it reads as an RTL change.
The same mutation is applied to every AST file that encodes the same design
(e.g. Bzeeno's configured and declared ASTs). Original files are never edited.

Operators (type: change):
  arith_op      BAdd<->BSub, BMul->BAdd
  logic_op      BAnd<->BOr, BXor->BOr
  shift_op      BShiftL<->BShiftR, BShiftRS<->BShiftR
  rel_op        BEq<->BNeq, BLtU<->BGtU, BGtS->BGtU
  const_flip    one bit of an EConst flipped
  stuck_at      RHS of a combinational/registered assignment replaced by 0 or 1
  mux_swap      ECond arms swapped
  operand_swap  one EVar replaced by another same-width signal read by the process
  drop_cond     (EBinary 1 BAnd x y) replaced by x or y
  drop_not      (EUnary w UNot x) replaced by x
This tool proves nothing; the proof chain decides detection.
"""
import argparse
import hashlib
import json
import random
import re
from pathlib import Path

PROCESS = re.compile(r'(?m)^(Definition (process_\d+) : Process := )(.*)$')
SWAP = {
    'arith_op': {'BAdd': 'BSub', 'BSub': 'BAdd', 'BMul': 'BAdd'},
    'logic_op': {'BAnd': 'BOr', 'BOr': 'BAnd', 'BXor': 'BOr'},
    'shift_op': {'BShiftL': 'BShiftR', 'BShiftR': 'BShiftL', 'BShiftRS': 'BShiftR'},
    'rel_op': {'BEq': 'BNeq', 'BNeq': 'BEq', 'BLtU': 'BGtU', 'BGtU': 'BLtU', 'BGtS': 'BGtU'},
}
TYPES = list(SWAP) + ['const_flip', 'stuck_at', 'mux_swap', 'operand_swap', 'drop_cond', 'drop_not']


def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()


def term_end(s, i):
    """End index of the term starting at s[i]: a balanced (...) or one atom."""
    if s[i] == '(':
        depth = 0
        for j in range(i, len(s)):
            depth += (s[j] == '(') - (s[j] == ')')
            if depth == 0:
                return j + 1
        raise ValueError('unbalanced term')
    m = re.compile(r'[^\s()\[\];]+').match(s, i)
    return m.end()


def args(s, i, n):
    """Spans of the n arguments after position i (skipping blanks)."""
    out = []
    for _ in range(n):
        while s[i] == ' ':
            i += 1
        j = term_end(s, i)
        out.append((i, j))
        i = j
    return out


def sites(body, readers):
    """All mutation sites of one process body: (type, start, end, replacement, detail)."""
    found = []
    for m in re.finditer(r'\(EBinary (\d+) (\w+) ', body):
        width, op = int(m.group(1)), m.group(2)
        for kind, table in SWAP.items():
            if op in table:
                a = m.start(2)
                found.append((kind, a, a + len(op), table[op], f'{op}->{table[op]}'))
        if op == 'BAnd' and width == 1:
            (x0, x1), (y0, y1) = args(body, m.end(), 2)
            end = term_end(body, m.start())
            for keep, (k0, k1) in (('lhs', (x0, x1)), ('rhs', (y0, y1))):
                found.append(('drop_cond', m.start(), end, body[k0:k1], f'keep {keep}'))
    for m in re.finditer(r'\(EUnary (\d+) UNot ', body):
        (x0, x1), = args(body, m.end(), 1)
        found.append(('drop_not', m.start(), term_end(body, m.start()), body[x0:x1], 'remove inversion'))
    for m in re.finditer(r'\(EConst (\d+) (-?\d+)\)', body):
        width, value = int(m.group(1)), int(m.group(2))
        if width == 0:
            continue
        bit = 0 if width == 1 else random.Random(m.start()).randrange(width)
        new = value ^ (1 << bit)
        found.append(('const_flip', m.start(), m.end(), f'(EConst {width} {new})', f'bit {bit}: {value}->{new}'))
    for m in re.finditer(r'\(ECond (\d+) ', body):
        (g0, g1), (y0, y1), (n0, n1) = args(body, m.end(), 3)
        found.append(('mux_swap', y0, n1, body[n0:n1] + ' ' + body[y0:y1], 'swap arms'))
    for m in re.finditer(r'SAssign (true|false) ', body):
        (e0, e1), = args(body, m.end(), 1)
        lhs = re.compile(r'\s*\(L\w+ (\d+) ').match(body, e1)
        if not lhs or body[e0:e1].startswith('(EConst'):
            continue
        width = int(lhs.group(1))
        for v in (0, 1):
            found.append(('stuck_at', e0, e1, f'(EConst {width} {v})', f'stuck-at-{v}'))
    for m in re.finditer(r'\(EVar (\d+) (\d+)\)', body):
        width, sig = int(m.group(1)), int(m.group(2))
        others = sorted(r for r, w in readers if w == width and r != sig)
        if others:
            other = random.Random(m.start() * 7 + sig).choice(others)
            found.append(('operand_swap', m.start(), m.end(), f'(EVar {width} {other})', f'signal {sig}->{other}'))
    return found


def readers_of(body):
    return {(int(s), int(w)) for w, s in re.findall(r'\(EVar (\d+) (\d+)\)', body)}


def generate(ast_paths, report_path, count, seed, output, exclude_instances=()):
    texts = [Path(p).read_text() for p in ast_paths]
    procs = [{m.group(2): (m.start(3), m.group(3)) for m in PROCESS.finditer(t)} for t in texts]
    for other in procs[1:]:
        if {k: v[1] for k, v in other.items()} != {k: v[1] for k, v in procs[0].items()}:
            raise ValueError('AST files do not encode the same processes')
    report = json.loads(Path(report_path).read_text()) if report_path else {}
    names = {row['id']: row['path'] for row in report.get('signal_table', [])}
    ptable = {row['index']: row for row in report.get('process_table', [])}
    pool = {t: [] for t in TYPES}
    for name, (_, body) in procs[0].items():
        index = int(name.split('_')[1])
        inst = ptable.get(index, {}).get('instance', '')
        if any(inst.startswith(x) for x in exclude_instances):
            continue
        for site in sites(body, readers_of(body)):
            pool[site[0]].append((name, index, inst) + site)
    rng = random.Random(seed)
    chosen, quota = [], {t: 0 for t in TYPES}
    order = [t for t in TYPES if pool[t]]
    # Stratified: round-robin over operator types, uniform within a type.
    for t in order:
        rng.shuffle(pool[t])
    while len(chosen) < count and any(pool[t] for t in order):
        for t in order:
            if pool[t] and len(chosen) < count:
                chosen.append(pool[t].pop())
                quota[t] += 1
    out = Path(output)
    out.mkdir(parents=True, exist_ok=False)
    rows = []
    for k, (name, index, inst, kind, a, b, new, detail) in enumerate(chosen):
        mid = f'm{k:03d}'
        files = []
        for path, text, table in zip(ast_paths, texts, procs):
            start, body = table[name]
            mutated = body[:a] + new + body[b:]
            assert mutated != body
            dest = out / mid / Path(path).name
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_text(text[:start] + mutated + text[start + len(body):])
            files.append(dict(original=str(path), mutant=str(dest), sha256=sha(dest.read_text())))
        body = procs[0][name][1]
        sigs = sorted({s for s, _ in readers_of(body[a:b] + ' ' + new)})
        rows.append(dict(id=mid, type=kind, detail=detail, process=index, instance=inst,
            source_line=ptable.get(index, {}).get('line'), original=body[a:b][:400], mutated=new[:400],
            signals={str(s): names.get(s, '') for s in sigs}, files=files))
    summary = dict(seed=seed, requested=count, generated=len(rows), per_type=quota,
                   available_sites={t: len(pool[t]) + quota[t] for t in TYPES},
                   ast_files=[dict(path=str(p), sha256=sha(t)) for p, t in zip(ast_paths, texts)],
                   method='AST-level single-site mutation; frontend is trusted and Verilator is not installed',
                   mutants=rows)
    (out / 'mutants.json').write_text(json.dumps(summary, indent=2) + '\n')
    return summary


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--ast', action='append', required=True, help='AST file (repeat for copies of the same design)')
    p.add_argument('--report', help='import report.json with signal_table/process_table')
    p.add_argument('--count', type=int, default=50)
    p.add_argument('--seed', type=int, default=20261102)
    p.add_argument('--exclude-instance', action='append', default=[])
    p.add_argument('--output', required=True)
    a = p.parse_args()
    s = generate(a.ast, a.report, a.count, a.seed, a.output, a.exclude_instance)
    print(json.dumps({k: s[k] for k in ('generated', 'per_type', 'available_sites')}, indent=2))
