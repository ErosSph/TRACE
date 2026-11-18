#!/usr/bin/env python3
"""Gate driver for the Bzeeno cycle-route modules (hand-written cores in framework/template-sources/bz/<Module>.v, optionally
preceded by generated text).  Providers: the reference providers (old-chain low-level namespaces; only definitions/low-level facts that
are logged as reused) plus the accepted template modules named with --tmpl NS=results/dir.
Usage: python tools/cpu_tmpl_bzgate.py FILE.v NAMESPACE MODULE OUTDIR [--tmpl NS=dir ...] [--export Module.name ...]
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import argparse
import json
import re
import sys
from pathlib import Path
import cpu_tmpl_accept as acc

REF = Path('results/r-jump-itree-20261102-a2')


def providers(tmpl):
    prov = json.loads((REF / 'providers.json').read_text())
    prov.append(dict(namespace='GeneratedJumpITree', directory=str(REF.resolve())))
    for t in tmpl:
        ns, d = t.split('=')
        prov.append(dict(namespace=ns, directory=str(Path(d).resolve())))
    return prov


def run(src, ns, module, out, tmpl, exports=None, extra=None):
    text = Path(src).read_text() if isinstance(src, (str, Path)) else src
    if not exports:
        exports = sorted(set(re.findall(r'^Print Assumptions ([A-Za-z0-9_.]+)\.', text, re.M)))
    r = acc.accept(out, ns, module, text, exports, [], providers=providers(tmpl),
                   extra=dict(generator='tools/cpu_tmpl_bzgate.py', design='bzeeno', **(extra or {})))
    print(json.dumps({k: r[k] for k in r if k in ('accepted', 'coqc_seconds', 'coqchk_seconds', 'assumptions', 'coqc_exit', 'coqchk_exit', 'coqc_peak_rss_kb')}))
    return r


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('src'); ap.add_argument('namespace'); ap.add_argument('module'); ap.add_argument('out')
    ap.add_argument('--tmpl', action='append', default=[])
    a = ap.parse_args()
    r = run(a.src, a.namespace, a.module, a.out, a.tmpl)
    sys.exit(0 if r['accepted'] else 1)
