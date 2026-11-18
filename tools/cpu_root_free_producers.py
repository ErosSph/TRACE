"""Check arbitrary-lvalue root-free producers on actual remaining processes.

Reuse validated actual-fuel Known providers; report residual positions, NOT
original source indices. No CPU-name dispatch or inferred ISA correctness.
"""
from __future__ import annotations
import argparse,hashlib,json,re,time
from pathlib import Path
import cpu_auto_adapter as adapter
import cpu_known_producers as known
import cpu_comb_residual_diagnostics as diagnostics
import cpu_scalar_captures as scalar
from cpu_certificate_acceptance import run_stage


def proposal(profile,use_public_assembly=False):
    if type(use_public_assembly)is not bool:raise ValueError('public assembly mode must be boolean')
    known.completion_source(profile)  # Strict import/program validation.
    b=profile['ast'];p=b['program'];imports=[b['module'],*b.get('program_imports',[])]
    lines=['From Coq Require Import List Bool PeanoNat.',
      'Require Import Lang.ExtendedSV Lang.ExtendedSVCombIdempotence Lang.ExtendedSVKnownProducer',
      ' Lang.ExtendedSVRootFreeProducer Lang.ExtendedSVCombRuleAssembly',
      ' Lang.ExtendedSVInferredProducerCertificate Ex.External.CPUCombNBAExtendedCatalog',
      ' GeneratedKnownProducers.Known '+' '.join(imports)+'.',
      'Import ListNotations ExtendedSV ExtendedSVCombIdempotence ExtendedSVKnownProducer',
      ' ExtendedSVRootFreeProducer ExtendedSVCombRuleAssembly ExtendedSVInferredProducerCertificate',
      ' CPUCombNBAExtendedCatalog.',
      'Definition selected_order := filter root_free_producerb Known.remaining_order.',
      # One evaluation, one let-bound residual list; no repeated whole-program
      # known analysis merely to print several redundant counters.
      'Goal True.',
      ' let payload:=eval vm_compute in (let rest:=Known.remaining_order in',
      '  (length rest,map fst(filter(fun ip=>root_free_producerb(snd ip))',
      '    (combine(seq 0(length rest))rest)))) in',
      ' lazymatch payload with (?n,?ids)=>',
      '  idtac "ROOT_FREE_TOTAL" n;idtac "ROOT_FREE_POSITIONS" ids end. exact I. Qed.',
      f'Local Opaque {p} Known.actual_order ProducerIdempotent.',
      f'Theorem actual_root_free_producers : Forall(ProducerIdempotent {p})selected_order.',
      'Proof. apply Forall_forall. intros proc HI. apply filter_In in HI as [_ HC].',
      f' exact(checked_root_free_producer {p} proc HC). Qed.',
      'Theorem original_producers_when_remaining_root_free :',
      ' forallb root_free_producerb Known.remaining_order=true ->',
      f' Forall(ProducerIdempotent {p})Known.actual_order.',
      'Proof. intro HC.',
      f' apply(complete_registry_from_residual producer_rules_with_nba {p} Known.actual_order Known.actual_fuel_positive).',
      f' apply complete_filtered_exception with(f:=known_producerb {p}).',
      f' - exact(checked_known_producers {p} Known.base_residual).',
      ' - apply Forall_forall. intros proc HI. apply checked_root_free_producer.',
      '   exact(proj1(forallb_forall _ _)HC proc HI). Qed.']
    for i,name in enumerate(('actual_root_free_producers','original_producers_when_remaining_root_free')):
        lines += [f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{i}". exact I. Qed.',
                  'Print Assumptions '+name+'.']
    text='\n'.join(lines)+'\n'
    if use_public_assembly:
        text=text.replace('Require Import Lang.ExtendedSV ',
            'Require Import Lang.ExtendedSVRootFreeAssembly Lang.ExtendedSV ',1)
        text=text.replace('Import ListNotations ExtendedSV ',
            'Import ListNotations ExtendedSVRootFreeAssembly ExtendedSV ',1)
        first=('Proof. apply Forall_forall. intros proc HI. apply filter_In in HI as [_ HC].\n'
            f' exact(checked_root_free_producer {p} proc HC). Qed.')
        second=(f' apply complete_filtered_exception with(f:=known_producerb {p}).\n'
            f' - exact(checked_known_producers {p} Known.base_residual).\n'
            ' - apply Forall_forall. intros proc HI. apply checked_root_free_producer.\n'
            '   exact(proj1(forallb_forall _ _)HC proc HI). Qed.')
        assert text.count(first)==text.count(second)==1
        text=text.replace(first,f'Proof. exact(checked_root_free_order {p} Known.remaining_order). Qed.')
        text=text.replace(second,f' exact(known_then_root_free_complete {p} Known.base_residual HC). Qed.')
    return text


def parse(log):
    n=re.findall(r'^ROOT_FREE_TOTAL\s+(\d+)\s*$',log,re.M)
    if len(n)!=1:raise ValueError('missing/ambiguous residual count')
    total=int(n[0]);positions=diagnostics.parse_indices(log.replace('ROOT_FREE_POSITIONS','REGISTRY_RESIDUAL_INDICES'))
    if any(i>=total for i in positions):raise ValueError('position outside actual residual list')
    return dict(before=total,newly_accepted=len(positions),remaining=total-len(positions),
                covered_residual_positions=positions)


def check(profile,provider,output,timeout=1200,use_public_assembly=False):
    provider=Path(provider).resolve();output=Path(output)
    if output.exists():raise ValueError('use a fresh result directory')
    r=json.loads((provider/'report.json').read_text())
    if not r.get('accepted'):raise ValueError('checked actual-fuel Known provider required')
    ast,text=known.proposal(profile,r.get('short_circuit_indices',False))
    if (text!=(provider/'Known.v').read_text() or r['actual_program']!=profile['ast']['program']
        or r['ast_sha256']!=ast['source_sha256']
        or hashlib.sha256(text.encode()).hexdigest()!=r['source_sha256']):
        raise ValueError('provider does not match original profile/source')
    source=proposal(profile,use_public_assembly);output.mkdir(parents=True);path=output/'RootFree.v';path.write_text(source)
    flags=list(adapter.framework.FLAGS)
    for e in profile.get('coq_load_paths',[]):flags+=['-R',e['directory'],e['namespace']]
    flags+=['-R',str(provider),'GeneratedKnownProducers','-R',str(output.resolve()),'GeneratedRootFree']
    report=dict(accepted=False,actual_program=profile['ast']['program'],ast_sha256=ast['source_sha256'],
        source_sha256=hashlib.sha256(source.encode()).hexdigest(),provider_source_sha256=r['source_sha256'],
        covered_index_space='positions in the actual Known.remaining_order, not original process indices',
        complete_original_producer_list_proved=False,original_full_phase_proved=False,
        new_global_invariant_synthesized=False,itree_refinement_proved=False,llm_calls=0,
        use_public_assembly=use_public_assembly)
    start=time.monotonic();deadline=start+timeout
    k,t=run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedKnownProducers.Known'],
        output/'provider.coqchk.log',timeout)
    report.update(provider_coqchk_exit=k.returncode,provider_coqchk_timed_out=t)
    remaining=deadline-time.monotonic()
    if k.returncode==0 and remaining>0:
        cs=time.monotonic()
        c,t=run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',remaining)
        report.update(coqc_exit=c.returncode,coqc_timed_out=t,coqc_seconds=time.monotonic()-cs)
        if c.returncode==0:
            counts=parse(c.stdout)
            if counts['before']!=r['counts']['remaining']:raise ValueError('actual residual count changed')
            report['counts']=counts;report['assumptions_closed']=scalar.audit_output(c.stdout,2)
            remaining=deadline-time.monotonic()
            if report['assumptions_closed'] and remaining>0:
                ks=time.monotonic()
                k,t=run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedRootFree.RootFree'],
                    output/'coqchk.log',remaining)
                report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,coqchk_seconds=time.monotonic()-ks,
                    accepted=k.returncode==0)
    report['overall_seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--profile',type=Path,required=True);p.add_argument('--provider',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--public-assembly',action='store_true');args=p.parse_args()
    result=check(json.loads(args.profile.read_text()),args.provider,args.output,
                 use_public_assembly=args.public_assembly)
    print(json.dumps(result,indent=2));raise SystemExit(0 if result['accepted'] else 1)
