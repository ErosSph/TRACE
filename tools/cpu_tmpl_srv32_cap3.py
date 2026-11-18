#!/usr/bin/env python3
"""srv32 capture facts, part 3: the flag registers the decode of the 29 classes leaves at 0 although Cap (part 1) does not state them:
ex_system (269), ex_system_op (270) (rise process 4) and ex_mem2reg (258) (rise process 5).  Same facts / xeval method as cpu_tmpl_srv32_cap.py.
Untrusted generator.  proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import sys
from pathlib import Path
import cpu_tmpl_ast as T
import cpu_isa_classes as isa
import cpu_tmpl_srv32_cap as C


def text(module='Srv32Cap3'):
    body = ['Notation P := srv32_program (only parsing).']
    ex = []
    for c in isa.classes():
        body.append(C.class_text(c, regs_override=[(269, 1, 0), (270, 1, 0)], proc=4, suffix='cap3'))
        ex += [f'{module}.{c["name"]}_cap3']
    hdr = C.HDR.replace('@STAGE_MOD@', C.STAGE.rsplit('.', 1)[0]).replace('@EDGE_MOD@', C.EDGE.rsplit('.', 1)[0])
    t = (f'(** srv32: capture facts part 3 (tools/cpu_tmpl_srv32_cap3.py). proof_author: {T.PROOF_AUTHOR}; external_llm_api_calls=0. *)\n' + hdr
         + f'Module {module}.\n' + '\n'.join(body) + f'\nEnd {module}.\n' + 'Goal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.\n' + ''.join(f'Print Assumptions {e}.\n' for e in ex))
    return t, ex


if __name__ == '__main__':
    t, ex = text()
    Path(sys.argv[1]).write_text(t)
    print(sys.argv[1], len(t.splitlines()))
