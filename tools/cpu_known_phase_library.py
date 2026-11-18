"""Publish checked actual-fuel phase candidates as ordinary reusable Coq libraries.

No design-name dispatch, proof-text injection, replacement Program, or automatic
global invariant claim. Historical result namespaces are not runtime imports.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import time
import cpu_auto_adapter as adapter
import cpu_known_producers as known
import cpu_phase_from_known as phase
import cpu_scalar_captures as scalar
from cpu_certificate_acceptance import run_stage


def sources(profile,stem,short_circuit_indices=False):
    if not isinstance(stem,str) or not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',stem):
        raise ValueError('library stem must be a simple Coq identifier')
    names={part:stem+part for part in ('Known','Complete','Eligibility','Phase')}
    modules={part:'Ex.Generated.'+name for part,name in names.items()}
    _,text=known.proposal(profile,short_circuit_indices)
    texts={
        'Known':text,
        'Complete':known.completion_source(profile,modules['Known']),
        'Eligibility':phase.eligibility_source(profile,modules['Known'],modules['Complete']),
        'Phase':phase.phase_source(profile,modules['Known'],modules['Complete'],modules['Eligibility'])}
    return [(names[k],texts[k],2 if k in ('Known','Phase') else 1) for k in names]


def validate_provider(profile,provider,candidate):
    provider=Path(provider);candidate=Path(candidate)
    r=json.loads((provider/'report.json').read_text())
    if not (r.get('accepted') and r.get('complete_original_producer_list_proved')):
        raise ValueError('complete checked producer certificate required')
    q=json.loads((candidate/'report.json').read_text())
    if not (q.get('accepted') and q.get('original_full_phase_proved')):
        raise ValueError('complete checked producer and phase candidates required')
    ast,text=known.proposal(profile,r.get('short_circuit_indices',False))
    expected={provider/'Known.v':text,provider/'Complete.v':known.completion_source(profile),
        candidate/'Eligibility.v':phase.eligibility_source(profile),
        candidate/'Phase.v':phase.phase_source(profile)}
    for path,wanted in expected.items():
        if path.read_text()!=wanted:raise ValueError('candidate source/profile mismatch: '+str(path))
    if r['actual_program']!=profile['ast']['program'] or q['actual_program']!=r['actual_program']:
        raise ValueError('actual Program mismatch')
    digest=lambda s:hashlib.sha256(s.encode()).hexdigest()
    if (r['ast_sha256']!=ast['source_sha256'] or r['source_sha256']!=digest(text)
        or r['complete_source_sha256']!=digest(expected[provider/'Complete.v'])
        or q['producer_source_sha256']!=r['source_sha256']
        or q['complete_source_sha256']!=r['complete_source_sha256']):
        raise ValueError('candidate provenance mismatch')
    for part in ('Eligibility','Phase'):
        if q[part+'_source_sha256']!=digest(expected[candidate/(part+'.v')]):
            raise ValueError('phase source fingerprint mismatch')
    return r


def publish(profile,provider,candidate,stem,output,timeout=1200):
    output=Path(output)
    if output.exists():raise ValueError('use a fresh result directory')
    r=validate_provider(profile,provider,candidate)
    plan=sources(profile,stem,r.get('short_circuit_indices',False))
    destination=adapter.ROOT/'src/Ex/Generated'
    # Validate every destination before writing any of them.
    for name,text,_ in plan:
        path=destination/(name+'.v')
        if path.exists() and path.read_text()!=text:
            raise ValueError('refuse to replace different library: '+str(path))
    output.mkdir(parents=True)
    flags=list(adapter.framework.FLAGS)
    for e in profile.get('coq_load_paths',[]):flags+=['-R',e['directory'],e['namespace']]
    report=dict(accepted=False,actual_program=profile['ast']['program'],
        ast_sha256=r['ast_sha256'],libraries=[],llm_calls=0,
        new_global_invariant_synthesized=False,itree_refinement_proved=False,
        actual_consumer_reconnected=False)
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
    report['accepted']=len(report['libraries'])==4 and all(x['accepted'] for x in report['libraries'])
    report['original_full_phase_proved']=report['accepted']
    report['overall_seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--profile',type=Path,required=True)
    p.add_argument('--provider',type=Path,required=True)
    p.add_argument('--candidate',type=Path,required=True)
    p.add_argument('--stem',required=True)
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args()
    result=publish(json.loads(args.profile.read_text()),args.provider,args.candidate,args.stem,args.output)
    print(json.dumps(result,indent=2));raise SystemExit(0 if result['accepted'] else 1)
