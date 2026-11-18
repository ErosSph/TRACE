#!/usr/bin/env python3
"""srv32 template route: second set of next-value lemmas (capture of the instruction word fields: ex_insn, ex_src*_sel, ex_dst_sel; imem_rdata).
Same optimisation as cpu_tmpl_srv32_nx.py (D-form hypotheses).  Untrusted generator.
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import sys
from pathlib import Path
import cpu_tmpl_srv32_nx as N
from cpu_tmpl_srv32_nx import Nx, dw, rs


def lemmas():
    L = []
    A = L.append
    A(Nx('nx_249', 249, ['w'], [dw(236, 1, 0), dw(233, 32, 'w')], 'w', norms=[('w', 32)]))
    for r, lsb in ((252, 15), (253, 20), (254, 7)):
        A(Nx(f'nx_{r}', r, ['w'], [dw(236, 1, 0), dw(233, 32, 'w')], f'norm 5 (Z.shiftr w {lsb})', norms=[('w', 32)]))
    A(Nx('nx_12', 12, ['a', 'rw'], [dw(5, 1, 1), dw(4, 32, 'a'), dw(13, 32, 'rw')], 'if Z.eqb (norm 23 (Z.shiftr a 9)) 0 then rw else 0', norms=[('a', 32), ('rw', 32)],
         fin='change (1 =? 0) with false. cbv iota. change (norm 5 9) with 9. change (norm 23 0) with 0. rewrite (Z.eqb_sym 0 (norm 23 (Z.shiftr a 9))). destruct (Z.eqb (norm 23 (Z.shiftr a 9)) 0); cbn [boolz Z.eqb].\n all: first [change (norm 1 1) with 1 | change (norm 1 0) with 0]; cbv iota delta [Z.eqb]; cbn [Z.eqb]; rewrite ?N_rw; try reflexivity.\n all: cbn; reflexivity.'))
    # ex_mem2reg (258) after the rise: 0 for every non-load opcode of the domain, whatever the old value (0 or 1; dmem_rvalid = 1)
    for opc in (51, 19, 103, 55, 23, 111, 99):
        for o in (0, 1):
            A(Nx(f'nx_258_{opc}_o{o}', 258, ['w'], [dw(233, 32, 'w'), dw(37, 1, 1), dw(258, 1, o), f'norm 7 (Z.shiftr w (norm 5 0)) = {opc}'], '0', norms=[('w', 32)]))
    return L


def text(module='Srv32Nx2'):
    h = N.HEAD
    return N.text(module, lemmas(), h)


if __name__ == '__main__':
    t, ex = text()
    Path(sys.argv[1]).write_text(t)
    print(sys.argv[1], len(t.splitlines()))
