#!/usr/bin/env python3
"""Gate runner for the Steel controls module (tools/cpu_tmpl_stctl.py).  proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import argparse, json, sys
sys.path.insert(0, __import__('os').path.dirname(__file__))
import cpu_tmpl_stctl as T
import cpu_tmpl_stcase as C

ap = argparse.ArgumentParser()
ap.add_argument('--module', default='SteelTmplCtl')
ap.add_argument('--out', required=True)
ap.add_argument('--namespace')
ap.add_argument('--accept', action='store_true')
ap.add_argument('--classes')
ap.add_argument('--kind', default='ctl', choices=['ctl', 'imm', 'mis'])
a = ap.parse_args()
names = a.classes.split(',') if a.classes else list(C.classes())
if a.kind == 'mis':
    import os
    os.environ['STNOMIS'] = '1'
    if not a.classes:
        names = [n for n in names if n in T.JUMPFAM]
    text, infos, exports = T.module_text(a.module, names, suffix='mis', block_args=T.mis_args, title='misaligned-target facts of the jump family', extra_pre=T.MISPRE)
elif a.kind == 'imm':
    if not a.classes:
        names = [n for n in names if C.classes()[n]['group'] in T.IMMTYPE]
    text, infos, exports = T.module_text(a.module, names, suffix='imm', block_args=T.imm_args, title='immediates', extra_pre=T.IMMPRE)
else:
    text, infos, exports = T.module_text(a.module, names)
if a.accept:
    import cpu_tmpl_accept as acc
    r = acc.accept(a.out, a.namespace, a.module, text, exports, [('experiments/framework/generated/steel', 'Steel')],
                   extra=dict(generator='tools/cpu_tmpl_stctl.py', design='steel', per_class=infos))
    print(json.dumps({k: v for k, v in r.items() if k not in ('loadpaths', 'per_class')}, indent=1))
    sys.exit(0 if (r['accepted'] or r.get('coqc_accepted')) else 1)
open(a.out, 'w').write(text)
