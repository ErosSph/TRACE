#!/usr/bin/env python3
"""goal_arch / goal_front / goal_admission modules of the Bzeeno template D step (assembled from hand-written cores in
framework/template-sources/bz/*.v.in with the step module's own definitions of `design`, `plan_shape`, `plan_next` and the goal).
The shared header copies, verbatim, the text of the accepted step module (results/r-tmpl-bz-step-20261103-a3/BzTmplStep.v) between
`Definition design` and `Local Notation R`, so the theorems state exactly the goals of the step module (checked by Coq at the step).
Usage: cpu_tmpl_bzarch.py CORE.v.in OUT.v [--step results/.../BzTmplStep.v]
Untrusted generator; Coq checks everything. proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import re
import sys
from pathlib import Path

STEP = 'results/r-tmpl-bz-step-20261103-a3/BzTmplStep.v'


def step_defs(step=STEP):
    t = Path(step).read_text()
    a = t.index('Definition design(')
    b = t.index('Local Notation R :=')
    return t[a:b]


def build(core, step=STEP):
    text = Path(core).read_text()
    return text.replace('@STEP_DEFS@', step_defs(step))


if __name__ == '__main__':
    a = sys.argv[1:]
    step = a[a.index('--step') + 1] if '--step' in a else STEP
    Path(a[1]).write_text(build(a[0], step))
