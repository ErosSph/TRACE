#!/usr/bin/env python3
"""ISA-side field and post-state lemmas of the Bzeeno template route (generated per class from the class table).
Template: framework/template-sources/bz/BzTmplIsa.v.in ; markers @DEST_ALTS@ (destination field of every data-op/jump class from
CPUClassTableInverse.inv_<C>) and @SRC_ALTS@ (rs1/rs2 fields of the branch classes, rs1 of Jalr).
Untrusted generator; Coq checks everything. proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import sys
from pathlib import Path
import cpu_isa_classes as isa
import cpu_class_table as ct


def build(template):
    text = Path(template).read_text()
    dest, src1, src2 = [], [], []
    # argument counts of the constructors from the class table
    arity = {}
    for c in isa.classes():
        toks = ct_split(ct.args(c))
        arity[c['name']] = len(toks)
    for c in isa.classes():
        n, k = c['name'], c['kind']
        us = ' '.join(['_'] * arity[n])
        if k in ('dataop', 'jal', 'jalr'):
            dest.append(f'exact (proj1 (proj1 (CPUClassTableInverse.CPUClassTableInverse.inv_{n} w {us} H)))')
        if k == 'branch':
            src1.append(f'exact (proj1 (proj1 (CPUClassTableInverse.CPUClassTableInverse.inv_{n} w {us} H)))')
            src2.append(f'exact (proj1 (proj2 (proj1 (CPUClassTableInverse.CPUClassTableInverse.inv_{n} w {us} H))))')
    text = text.replace('@DEST_ALTS@', ' | '.join(dest))
    text = text.replace('@BSRC1_ALTS@', ' | '.join(src1)).replace('@BSRC2_ALTS@', ' | '.join(src2))
    return text


def ct_split(a):
    toks, depth, cur = [], 0, ''
    for ch in a:
        if ch == '(':
            depth += 1
        if ch == ')':
            depth -= 1
        if ch == ' ' and depth == 0:
            toks.append(cur)
            cur = ''
        else:
            cur += ch
    toks.append(cur)
    return toks


if __name__ == '__main__':
    Path(sys.argv[2]).write_text(build(sys.argv[1]))
