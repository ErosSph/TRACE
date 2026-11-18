"""NERV template-route helpers (untrusted generator support): AST tables, writer table, Coq runner.
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import json, subprocess, tempfile, os
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
REPORT = json.loads((ROOT / 'experiments/framework/generated/nerv-lit/report.json').read_text())
SIG = {s['id']: s for s in REPORT['signal_table']}
PROC = REPORT['process_table']
COMB = [p for p in PROC if p['kind'] == 'Combinational']
COMB_POS = {p['index']: k for k, p in enumerate(COMB)}
NAME = {i: s['path'].split('.')[-1] for i, s in SIG.items()}
BYNAME = {}
for i, s in SIG.items():
    if s['path'].startswith('nerv_top.uut.'):
        BYNAME[s['path'].split('.')[-1]] = i
def width(r): return SIG[r]['width']
def wtab_text():
    nsig = max(SIG) + 1
    wt = [[] for _ in range(nsig)]
    for k, p in enumerate(COMB):
        for r in p['writers']:
            wt[r].append(k)
    return 'Definition wtab:list(list nat):=[' + '; '.join('[' + ';'.join(f'{x}%nat' for x in w) + ']' for w in wt) + '].\n'
LOADPATHS = ['-R', '.', 'Pfv', '-R', '../dep/coqutil/src/coqutil/', 'coqutil', '-R', '../dep/riscv-coq/src/riscv/', 'riscv',
             '-R', '../experiments/framework/generated/nerv-lit', 'NervLit']
def coqc(txt, workdir=None, extra=()):
    wd = workdir or tempfile.mkdtemp(prefix='nv', dir=os.environ.get('NV_SCRATCH', None))
    fn = Path(wd) / 'Probe.v'
    fn.write_text(txt)
    r = subprocess.run(['coqc', *LOADPATHS, *extra, str(fn)], cwd=ROOT / 'src', capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError(r.stdout + r.stderr)
    return r.stdout
PRE = '''From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVSymExec Lang.ExtendedSVFactChain Lang.ExtendedSVSymExecSym Lang.ExtendedSVEval4
 Lang.ExtendedSVSymExecOverlay4 Lang.ExtendedSVSymExecHavoc NervLit.NervLitAST.
Import ListNotations ExtendedSV ExtendedSVSymExec ExtendedSVFactChain ExtendedSVSymExecSym ExtendedSVEval4 ExtendedSVSymExecOverlay4 ExtendedSVSymExecHavoc.
Local Open Scope Z_scope.
Notation P := NervLitAST.nerv_program.
Definition ps := filter is_comb (processes P).
'''
