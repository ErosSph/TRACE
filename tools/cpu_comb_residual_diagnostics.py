"""Inspect the actual Coq registry residuals and report syntax-backed candidates.

This is deliberately not a soundness certificate for unaccepted processes.
Registry rule soundness is checked independently; syntactic self-reads can refer
to fresh intra-process temporaries and do not establish combinational cycles.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import time
import cpu_auto_adapter as adapter
import cpu_comb_rule_registry as registry
import cpu_scalar_captures as scalar
from cpu_certificate_acceptance import run_stage


def parse_indices(log):
    matches=re.findall(r'^REGISTRY_RESIDUAL_INDICES\s+(\[[0-9;\s]*\])\s*$',log,re.M)
    if len(matches)!=1:
        raise ValueError('missing or ambiguous original process indices')
    body=matches[0][1:-1].strip()
    values=[] if not body else [int(x.strip()) for x in body.split(';')]
    if values!=sorted(set(values)):
        raise ValueError('residual indices must be distinct and in original order')
    return values


def describe(ast, indices):
    result=[]
    for index in indices:
        if not 0<=index<len(ast['processes']):
            raise ValueError('index outside original process list')
        process=ast['processes'][index]
        if process['kind']!='Combinational':
            raise ValueError('residual is not combinational')
        nodes=list(adapter.walk(process['body']))
        reads=sorted({int(n.args[1].name) for n in nodes if n.name=='EVar'})
        writes=sorted({int(n.args[1].name) for n in nodes if n.name=='LVar'})
        assigns=[n for n in nodes if n.name=='SAssign']
        modes=sorted({n.args[0].name for n in assigns})
        result.append(dict(index=index,process=process['name'],
            body_sha256=hashlib.sha256(adapter.render(process['body']).encode()).hexdigest(),
            syntactic_expression_reads=reads,syntactic_whole_lvalue_roots=writes,
            syntactic_read_write_overlap=sorted(set(reads)&set(writes)),
            assignment_modes=modes,contains_case=any(n.name=='SCase' for n in nodes),
            candidate_family=('output-independent-nonblocking' if modes==['true']
                and not set(reads)&set(writes) else 'state-threaded-or-other'),
            producer_idempotence_proved=False,
            note='Syntactic overlap does not distinguish old values from freshly overwritten temporary values.'))
    return result


def proposal(profile, include_nba=False):
    if type(include_nba) is not bool:
        raise ValueError('include_nba must be boolean')
    ast,text,audits=registry.proposal(profile)
    if include_nba:
        text=text.replace('Ex.External.CPUCombRuleCatalog',
            'Ex.External.CPUCombRuleCatalog Ex.External.CPUCombNBAExtendedCatalog')
        text=text.replace('ExtendedSVCombRuleRegistry CPUCombRuleCatalog.',
            'ExtendedSVCombRuleRegistry CPUCombRuleCatalog CPUCombNBAExtendedCatalog.')
        text=re.sub(r'\bproducer_rules\b','producer_rules_with_nba',text)
    p=profile['ast']['program']
    marker='Local Opaque actual_order certified_order residual_order.'
    diagnostic=(f'Definition original_residual_indices := map fst (filter '
        f'(fun ip => is_comb (snd ip) && negb (producer_accepted producer_rules (snd ip))) '
        f'(combine (seq 0 (length (processes {p}))) (processes {p}))).\n'
        'Goal True. let ids := eval vm_compute in original_residual_indices in\n'
        ' idtac "REGISTRY_RESIDUAL_INDICES" ids. exact I. Qed.\n')
    if include_nba:
        diagnostic=re.sub(r'\bproducer_rules\b','producer_rules_with_nba',diagnostic)
    assert text.count(marker)==1
    return ast,text.replace(marker,diagnostic+marker),audits


def check(profile,output,timeout=1200,include_nba=False):
    output=Path(output)
    if output.exists():
        raise ValueError('output must be fresh; retain prior evidence')
    output.mkdir(parents=True)
    ast,text,audits=proposal(profile,include_nba)
    source=output/'Residuals.v'
    source.write_text(text)
    flags=list(adapter.framework.FLAGS)
    for entry in profile.get('coq_load_paths',[]):
        flags+=['-R',entry['directory'],entry['namespace']]
    flags+=['-R',str(output.resolve()),'GeneratedResiduals']
    report=dict(accepted=False,ast_sha256=ast['source_sha256'],
        actual_program=profile['ast']['program'],source_sha256=hashlib.sha256(text.encode()).hexdigest(),
        new_global_invariant_synthesized=False,original_full_phase_proved=False,
        itree_refinement_proved=False,llm_calls=0,
        checked_catalog='base-plus-output-independent-nba' if include_nba else 'base')
    start=time.monotonic()
    deadline=start+timeout
    c,t=run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-time',*flags,str(source.resolve())],output/'coqc.log',timeout)
    report.update(coqc_exit=c.returncode,coqc_timed_out=t,coqc_seconds=time.monotonic()-start)
    if c.returncode==0:
        indices=parse_indices(c.stdout)
        counts=registry.counts(c.stdout)
        assert len(indices)==counts['residual']
        report.update(counts=counts,residuals=describe(ast,indices),
            assumptions_closed=scalar.audit_output(c.stdout,audits))
        remaining=deadline-time.monotonic()
        if remaining>0:
            ks=time.monotonic()
            k,t=run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                'GeneratedResiduals.Residuals'],output/'coqchk.log',remaining)
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,coqchk_seconds=time.monotonic()-ks)
            report['accepted']=report['assumptions_closed'] and k.returncode==0
    report['overall_seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--include-nba',action='store_true')
    args=parser.parse_args()
    report=check(json.loads(args.profile.read_text()),args.output,include_nba=args.include_nba)
    print(json.dumps(report,indent=2))
    raise SystemExit(0 if report['accepted'] else 1)
