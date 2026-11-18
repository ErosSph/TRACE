#!/usr/bin/env python3
"""Steel datapath/controls planner on the Bzeeno Session/Spec/emit machinery (tools/cpu_tmpl_bzex.py, reused unchanged).
Untrusted generator; Coq re-checks.  proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import json, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import cpu_tmpl_ast as T
import cpu_tmpl_edge as E
import cpu_tmpl_symexec as X
import cpu_tmpl_bzex as B
import cpu_isa_classes as isa

import os
AST = str(Path(os.environ['VERILROCQ_STEEL_AST_DIR'])/'SteelAST.v') if 'VERILROCQ_STEEL_AST_DIR' in os.environ else 'experiments/framework/generated/steel/SteelAST.v'
REP = 'experiments/framework/generated/steel/report.json'


class SteelPlanner(B.Planner):
    def __init__(self):
        self.ast = T.Ast(AST, REP)
        a = self.ast
        self.writers = {}
        for k, i in enumerate(a.comb_ids):
            for r in E.assigned_roots(a.procs[i]['body']):
                self.writers.setdefault(r, []).append(k)
        self.nsig = max(a.sig) + 1
        self.pr = {'ast': {'module': 'Steel.SteelAST', 'program': 'SteelAST.steel_program', 'file': AST}}

class SteelSession(B.Session):
    """Bzeeno Session + roots written by covering constant-offset slice processes (alu_operation_code)."""
    def __init__(self, P, spec):
        super().__init__(P, spec)
        self.slice_stage = None     # (len(ksC), len(outsC)) when the slice root was resolved
        self.slices = []            # (k, root, off, w, rhs_expr, value)

    def ensure_const(self, root, width):
        e = ('EVar', width, root)
        if e in self.F:
            return self.F[e]
        ks = self.P.writers.get(root, [])
        bodies = [self.P.body(k) for k in ks]
        if ks and all(b[0] == 'SAssign' and b[3][0] == 'LSel' for b in bodies):
            return self.ensure_slices(root, width, ks)
        return super().ensure_const(root, width)

    def ensure_slices(self, root, width, ks):
        if self.slice_stage is not None:
            raise B.NoPlan('second slice root')
        cover, total = 0, 0
        for k in ks:
            b = self.P.body(k)
            lv = b[3]
            assert lv[2][0] == 'LVar' and lv[3][0] == 'EConst'
            w, off = lv[1], lv[3][2]
            z = self.cev(b[2], True)
            self.slices.append((k, root, off, w, b[2], z & ((1 << w) - 1)))
            m = ((1 << w) - 1) << off
            assert cover & m == 0
            cover |= m
            total |= (z & ((1 << w) - 1)) << off
        assert cover == (1 << width) - 1
        self.slice_stage = (len(self.ksC), len(self.outsC))
        e = ('EVar', width, root)
        self.F[e] = total
        self.slice_fact = (e, total)
        return total


# base register/input facts at the driven state of a committing cycle (root, value)
BASE = [(1, 0), (14, 0), (200, 2), (257, 0), (247, 0), (251, 0), (248, 1), (12, 1), (13, 0), (186, 0), (187, 0), (188, 0), (189, 0)]

if __name__ == '__main__':
    P = SteelPlanner()
    cl = {c['name']: c for c in isa.classes()}[sys.argv[1] if len(sys.argv)>1 else 'Add']
    consts = list(BASE) + [(221, cl['opcode'])] + ([(219, cl['funct3'])] if cl['funct3'] is not None else []) + ([(220, cl['funct7'])] if cl['funct7'] is not None else [])
    spec = B.Spec('probe', consts, [(217,'w'),(258,'a'),(259,'b'),(253,'pc')], [(277, 'x'),(243,'y'),(215,'z')])
    while True:
        S = SteelSession(P, spec)
        try:
            S.plan(); print('PLAN OK', len(S.eq), len(S.ksC), 'slices', S.slices, S.slice_stage); break
        except B.NoPlan as e:
            print('NoPlan', e); break
