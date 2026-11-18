#!/usr/bin/env python3
"""Measured own-module gate; no dependency rebuilds or accepted-directory writes."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time
from cpu_certificate_acceptance import ALLOWED_AXIOMS
from check_reference_value_rules import audit_all_exports

ROOT = Path(__file__).resolve().parents[1]
AUTHOR = 'LLM-generated: OpenAI Codex'

def run(command, log):
    start = time.monotonic()
    with log.open('w') as stream:
        proc = subprocess.Popen(command, stdout=stream, stderr=subprocess.STDOUT)
        _, status, usage = os.wait4(proc.pid, 0)
        proc.returncode = os.waitstatus_to_exitcode(status)
    return dict(command=command, exit=proc.returncode, wall_seconds=time.monotonic()-start,
                peak_rss_kib=usage.ru_maxrss, cpu_seconds=usage.ru_utime+usage.ru_stime)

def check(source, out, namespace, providers=(), loadpaths=(), inplace=False):
    out.mkdir(parents=True, exist_ok=False)
    source = Path(source)
    text = source.read_text()
    exports = re.findall(r'^Print Assumptions (\S+)\.$', text, re.M)
    if not exports:
        raise ValueError('explicit Print Assumptions exports required')
    # Mark only the audit tail; chatter from intermediate tactics is not evidence.
    text = text.replace('Print Assumptions ', 'Goal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.\nPrint Assumptions ', 1)
    target = source if inplace else out/source.name
    if not inplace:
        target.write_text(text)
    flags = ['-R','src','Pfv','-R','dep/coqutil/src/coqutil','coqutil','-R','dep/riscv-coq/src/riscv','riscv']
    for p in list(providers)+list(loadpaths):
        flags += ['-R',p['directory'],p['namespace']]
    if not inplace:
        flags += ['-R',str(out.resolve()),namespace]
    report = dict(proof_author=AUTHOR, external_llm_api_calls=0, label='measured', accepted=False,
                  source_sha256=hashlib.sha256(target.read_bytes()).hexdigest(), exports=exports,
                  kernel_scope='own module; previously built dependencies', providers=list(providers))
    (out/'providers.json').write_text(json.dumps(list(providers),indent=2)+'\n')
    report['coqc'] = run(['_opam/bin/coqc','-time',*flags,str(target)],out/'coqc.log')
    if report['coqc']['exit']==0:
        log=(out/'coqc.log').read_text()
        try:
            axioms=audit_all_exports(log.split('TMPL_AUDIT_BEGIN')[-1] if not inplace else log, len(exports))
            report['assumptions']=sorted(axioms)
            report['audit_passed']=not (axioms-ALLOWED_AXIOMS)
        except ValueError as e:
            report['audit_passed']=False
            report['audit_error']=str(e)
        module=namespace+'.'+source.stem
        report['coqchk']=run(['_opam/bin/coqchk','-silent',*flags,'-norec',module],out/'coqchk.log')
        report['accepted']=report['audit_passed'] and report['coqchk']['exit']==0
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(directory=str(out),accepted=report['accepted'],coqc_exit=report['coqc']['exit'], coqc_seconds=report['coqc']['wall_seconds']),indent=1),flush=True)
    return report

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('source',type=Path); ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--namespace',required=True); ap.add_argument('--providers',type=Path)
    ap.add_argument('--loadpath',action='append',default=[],help='NAMESPACE=DIRECTORY')
    ap.add_argument('--inplace',action='store_true',help='compile new library at its canonical source path')
    a=ap.parse_args(); os.chdir(ROOT)
    pp=json.loads(a.providers.read_text()) if a.providers else []
    lp=[dict(namespace=x.split('=',1)[0],directory=x.split('=',1)[1]) for x in a.loadpath]
    r=check(a.source,a.out,a.namespace,pp,lp,a.inplace)
    raise SystemExit(0 if r['accepted'] else 1)
