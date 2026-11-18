"""Design-independent AST access for the template route (read-only, untrusted).

Parses the generated `Definition process_N : Process` lines with the parser of
cpu_ast_sim, prints expressions as Coq text, and indexes combinational scalar
assignments. Nothing here is a proof claim; Coq re-checks every use.
"""
import json
from pathlib import Path
import cpu_ast_sim as sim

PROOF_AUTHOR = 'LLM-generated: Claude Code (claude-sonnet-5-5)'


class Ast:
    def __init__(self, ast_file, report_file):
        self.file = Path(ast_file)
        self.prog = sim.parse_ast_file(ast_file)
        self.procs = self.prog['processes']
        self.names = self.prog['names']
        rep = json.loads(Path(report_file).read_text())
        self.sig = {r['id']: r for r in rep['signal_table']}
        self.comb_ids = [i for i, p in enumerate(self.procs) if p['kind'] == 'Combinational']
        self.comb = {}   # root -> dict(proc, k, width, rhs)
        for k, i in enumerate(self.comb_ids):
            b = self.procs[i]['body']
            if b[0] == 'SAssign' and b[3][0] == 'LVar':
                self.comb[b[3][2]] = dict(proc=i, name=self.names[i], k=k, width=b[3][1], rhs=b[2], nba=b[1])

    def path(self, i):
        return self.sig[i]['path'].split('.')[-1]

    def find_assign(self, proc, root):
        """Path (list of statement indices) and rhs of the assignment to `root` in process `proc`."""
        found = []

        def walk(s, path):
            if s[0] == 'SAssign':
                lv = s[3]
                while lv[0] == 'LSel':
                    lv = lv[2]
                if lv[2] == root:
                    found.append((path, s))
            elif s[0] == 'SSeq':
                for j, c in enumerate(s[1]):
                    walk(c, path + [j])
            elif s[0] == 'SIf':
                walk(s[2], path + [0])
                walk(s[3], path + [1])
        walk(self.procs[proc]['body'], [])
        if len(found) != 1:
            raise ValueError(f'process {proc}: {len(found)} assignments to {root}')
        return found[0]


def coq(e):
    k = e[0]
    if k == 'EConst':
        return f'(EConst {e[1]} {e[2]})' if e[2] >= 0 else f'(EConst {e[1]} ({e[2]}))'
    if k == 'EVar':
        return f'(EVar {e[1]} {e[2]}%nat)'
    if k in ('ESel', 'EConcat'):
        return f'({k} {e[1]} {coq(e[2])} {coq(e[3])})'
    if k == 'EReplicate':
        return f'(EReplicate {e[1]} {e[2]} {coq(e[3])})'
    if k == 'EExtend':
        return f'(EExtend {e[1]} {"true" if e[2] else "false"} {coq(e[3])})'
    if k == 'EUnary':
        return f'(EUnary {e[1]} {e[2]} {coq(e[3])})'
    if k == 'EBinary':
        return f'(EBinary {e[1]} {e[2]} {coq(e[3])} {coq(e[4])})'
    if k == 'ECond':
        return f'(ECond {e[1]} {coq(e[2])} {coq(e[3])} {coq(e[4])})'
    raise ValueError(k)


def evars(e, acc=None):
    acc = set() if acc is None else acc
    if e[0] == 'EVar':
        acc.add((e[1], e[2]))
    elif e[0] != 'EConst':
        for c in e[1:]:
            if isinstance(c, tuple) and c and isinstance(c[0], str) and c[0].startswith('E'):
                evars(c, acc)
    return acc
