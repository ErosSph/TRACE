#!/usr/bin/env python3
"""srv32 register-file write step at the rising edge (bank 244, process 15) on src/Lang/ExtendedSVBankWriteBlk.v.
Shape: `if resetb then (if guard then { bank[idx] <= data; } else skip) else <reset loop>`; once resetb = 1 the reset branch is never taken.
  rf_write_lane : guard true  -> lane i of the bank after the edge = (i = j ? norm 32 data : old lane), j = (wb_dst_sel - 1) mod 32 (lane 31 = padded dead cell)
  rf_write_off  : guard false -> the bank is unchanged
The resetb / guard / data / index expressions are read from the AST (process 15), not typed.  Untrusted generator; Coq checks everything.
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import sys
from pathlib import Path
import cpu_tmpl_ast as T

SRC = Path('framework/template-sources/Srv32RfCore.v.in')


def shape():
    a = T.Ast('experiments/framework/generated/srv32/Srv32AST.v', 'experiments/framework/generated/srv32/report.json')
    b = a.procs[15]['body']
    sif = b[1][0][1][0]            # SSeq [SSeq [SIf c (SIf g (SSeq [SAssign ..]) SSkip) other]]
    c, inner = sif[1], sif[2]
    g, blk = inner[1], inner[2]
    asg = blk[1][0]
    return c, g, asg[2], asg[3]


def text(module):
    c, g, e, lhs = shape()
    idx = lhs[3]
    t = SRC.read_text()
    for k, v in dict(MOD=module, RESETB=T.coq(c), GUARD=T.coq(g), DATA=T.coq(e), INDEX=T.coq(idx), DST1=T.coq(idx[3])).items():
        t = t.replace('@' + k + '@', v)
    return t, [f'{module}.rf_write_lane', f'{module}.rf_write_off']


if __name__ == '__main__':
    t, ex = text('Srv32Rf')
    Path(sys.argv[1]).write_text(t)
