"""Generate original-LFP scalar equations beyond RF-specific readers.

Actual straight-line blocking bodies and all sampling/frame conditions are
checked by the existing generic scalar-block theorem. This does not invent
combinational aliases or assume guards, token identities, or CPU correctness.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import time
import cpu_auto_adapter as adapter
import cpu_rf_read_ports as ports
from cpu_certificate_acceptance import run_stage


def analyze(ast,roots):
    combinations=[p for p in ast['processes'] if p['kind']=='Combinational']
    blocks=[];outputs=[];residuals=[];by_name={}
    for root in sorted(set(roots)):
        writers=[p for p in combinations if root in p['writers']]
        if len(writers)!=1:
            residuals.append(dict(root=root,reason='requires one actual combinational writer'))
            continue
        proc=writers[0]
        try:assignments=ports.flatten_blocking(proc['body'])
        except ValueError as exc:
            residuals.append(dict(root=root,process=proc['name'],reason=str(exc)));continue
        if proc['name'] not in by_name:
            by_name[proc['name']]=len(blocks)
            blocks.append(dict(process=proc['name'],comb_index=combinations.index(proc),assignments=assignments))
        index=max(i for i,st in enumerate(assignments) if int(st.args[2].args[1].name)==root)
        _,rhs,lhs=assignments[index].args
        outputs.append(dict(block_index=by_name[proc['name']],assignment_index=index,
            process=proc['name'],width=int(lhs.args[0].name),output_root=root,rhs=rhs))
    return dict(blocks=blocks,ports=outputs,residuals=residuals)


def proposal(profile,roots):
    ast=adapter.load_ast(adapter.ROOT/profile['ast']['file'])
    analysis=analyze(ast,roots)
    source=ports.render(profile['ast'],ast,analysis)
    return ast,analysis,source


def emit_library(profile,destination,roots,check=False):
    _,analysis,source=proposal(profile,roots)
    if analysis['residuals'] or not analysis['ports']:raise ValueError('unsupported scalar comb selection')
    path=Path(destination)
    if check:
        if not path.is_file() or path.read_text()!=source:
            raise ValueError('persistent scalar comb source differs from generation')
    elif path.exists():raise ValueError('destination exists; use --check-source')
    else:
        path.parent.mkdir(parents=True,exist_ok=True);path.write_text(source)
    return dict(source=str(path),source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        source_matches_generator=True,coq_checked=False)


def check_profile(profile,output,roots,timeout=1200):
    output=Path(output)
    if output.exists():raise ValueError('output must be fresh')
    output.mkdir(parents=True)
    ast,analysis,source=proposal(profile,roots)
    file=output/'ScalarCombBindings.v';file.write_text(source)
    transport=profile['ast'].get('syntax_program') is not None and profile['ast']['syntax_program']!=profile['ast']['program']
    count=len(analysis['ports'])*(2 if transport else 1)
    report=dict(accepted=False,ast_sha256=ast['source_sha256'],
        source_sha256=hashlib.sha256(source.encode()).hexdigest(),actual_program=profile['ast']['program'],
        outputs=[{k:v for k,v in item.items() if k!='rhs'} for item in analysis['ports']],
        residuals=analysis['residuals'],audited_exports=count,llm_calls=0,
        instruction_identity_proved=False,global_invariant_synthesized=False)
    if analysis['residuals'] or not analysis['ports']:report['status']='unsupported_comb_scalar_selection'
    else:
        flags=list(adapter.framework.FLAGS)
        for extra in profile.get('coq_load_paths',[]):flags+=['-R',extra['directory'],extra['namespace']]
        flags+=['-R',str(output.resolve()),'GeneratedScalarComb']
        start=time.monotonic()
        c,t=run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-q',*flags,str(file.resolve())],output/'coqc.log',timeout)
        report.update(coqc_exit=c.returncode,coqc_timed_out=t,coqc_seconds=time.monotonic()-start)
        if c.returncode==0:
            report['assumptions_closed']=ports.audit_output(c.stdout,count)
            start=time.monotonic()
            k,t=run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                'GeneratedScalarComb.ScalarCombBindings'],output/'coqchk.log',timeout)
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,coqchk_seconds=time.monotonic()-start)
            report['accepted']=report['assumptions_closed'] and k.returncode==0
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--profile',type=Path,required=True)
    p.add_argument('--roots',type=int,nargs='+',required=True)
    mode=p.add_mutually_exclusive_group(required=True)
    mode.add_argument('--output',type=Path);mode.add_argument('--emit-source',type=Path)
    mode.add_argument('--check-source',type=Path)
    p.add_argument('--timeout',type=float,default=1200);a=p.parse_args()
    if not 0<a.timeout<=1200:p.error('timeout must be positive and at most1200 seconds')
    profile=json.loads(a.profile.read_text())
    if a.emit_source or a.check_source:
        print(json.dumps(emit_library(profile,a.emit_source or a.check_source,a.roots,
            check=bool(a.check_source)),indent=2));return 0
    result=check_profile(profile,a.output,a.roots,a.timeout)
    print(json.dumps(result,indent=2));return 0 if result['accepted'] else 1


if __name__=='__main__':raise SystemExit(main())
