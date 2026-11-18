"""Publish a regenerated checked dependency catalog and original-budget phase.

Ordinary project module paths only. This does not discover an architectural
invariant or prove compatibility with an existing consumer's domain.
"""
from __future__ import annotations
import argparse,hashlib,json,re,time
from pathlib import Path
import cpu_auto_adapter as adapter
import cpu_dependency_catalog as catalog
import cpu_bounded_catalog_phase as phase
import cpu_scalar_captures as scalar
from cpu_certificate_acceptance import run_stage


def sources(profile,stem,share_static_catalog):
    if not isinstance(stem,str) or not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',stem):
        raise ValueError('library stem must be a simple Coq identifier')
    _,_,_,text=catalog.proposal(profile)
    return [(stem+'Catalog',text,2),
      (stem+'Phase',phase.phase_source(profile,share_static_catalog,
        'Ex.Generated.'+stem+'Catalog'),7 if share_static_catalog else 4)]


def validate_provider(profile,provider,candidate):
    provider=Path(provider);candidate=Path(candidate)
    r=json.loads((provider/'report.json').read_text())
    q=json.loads((candidate/'report.json').read_text())
    if not(r.get('accepted') and r.get('metadata',{}).get('converges')
           and r.get('metadata',{}).get('covers_writers') and q.get('accepted')
           and q.get('original_full_phase_under_catalog_shape_proved')):
        raise ValueError('accepted complete original-budget catalog and phase required')
    ast,_,_,text=catalog.proposal(profile)
    shared=q.get('share_static_catalog',False)
    expected=phase.phase_source(profile,shared)
    digest=lambda s:hashlib.sha256(s.encode()).hexdigest()
    if ((provider/'Catalog.v').read_text()!=text or (candidate/'Phase.v').read_text()!=expected
        or r['source_sha256']!=digest(text) or q['source_sha256']!=digest(expected)
        or q['provider_source_sha256']!=r['source_sha256']
        or any(x['actual_program']!=profile['ast']['program'] for x in (r,q))
        or any(x['ast_sha256']!=ast['source_sha256'] for x in (r,q))
        or q['original_iteration_budget']!=r['metadata']['budget']):
        raise ValueError('candidate source, AST, program or budget mismatch')
    return r,q


def publish(profile,provider,candidate,stem,output,timeout=1200):
    output=Path(output)
    if output.exists():raise ValueError('use a fresh result directory')
    r,q=validate_provider(profile,provider,candidate)
    plan=sources(profile,stem,q.get('share_static_catalog',False))
    destination=adapter.ROOT/'src/Ex/Generated'
    for name,text,_ in plan:
        path=destination/(name+'.v')
        if path.exists() and path.read_text()!=text:
            raise ValueError('refuse to replace different library: '+str(path))
    output.mkdir(parents=True)
    flags=list(adapter.framework.FLAGS)
    for e in profile.get('coq_load_paths',[]):flags+=['-R',e['directory'],e['namespace']]
    report=dict(accepted=False,actual_program=r['actual_program'],ast_sha256=r['ast_sha256'],
      original_iteration_budget=r['metadata']['budget'],libraries=[],llm_calls=0,
      actual_consumer_reconnected=False,existing_shape_compatibility_proved=False,
      new_global_invariant_synthesized=False,itree_refinement_proved=False)
    start=time.monotonic();deadline=start+timeout
    for name,text,exports in plan:
        path=destination/(name+'.v');path.write_text(text)
        row=dict(module='Pfv.Ex.Generated.'+name,path=str(path.relative_to(adapter.ROOT)),
          source_sha256=hashlib.sha256(text.encode()).hexdigest(),accepted=False)
        report['libraries'].append(row)
        remaining=deadline-time.monotonic()
        if remaining<=0:row['status']='shared_deadline_exhausted';break
        cs=time.monotonic()
        c,t=run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path)],
          output/(name+'.coqc.log'),remaining)
        row.update(coqc_exit=c.returncode,coqc_timed_out=t,coqc_seconds=time.monotonic()-cs,
          assumptions_closed=c.returncode==0 and scalar.audit_output(c.stdout,exports))
        remaining=deadline-time.monotonic()
        if not row['assumptions_closed'] or remaining<=0:break
        ks=time.monotonic()
        k,t=run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',row['module']],
          output/(name+'.coqchk.log'),remaining)
        row.update(coqchk_exit=k.returncode,coqchk_timed_out=t,coqchk_seconds=time.monotonic()-ks,
          accepted=k.returncode==0)
        if not row['accepted']:break
        row['object_sha256']=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest()
    report['accepted']=len(report['libraries'])==2 and all(x['accepted'] for x in report['libraries'])
    report['original_full_phase_under_catalog_shape_proved']=report['accepted']
    report['overall_seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in ('profile','provider','candidate','output'):p.add_argument('--'+name,type=Path,required=True)
    p.add_argument('--stem',required=True);a=p.parse_args()
    result=publish(json.loads(a.profile.read_text()),a.provider,a.candidate,a.stem,a.output)
    print(json.dumps(result,indent=2));raise SystemExit(0 if result['accepted'] else 1)
