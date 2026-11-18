"""Actual-Program definite-assignment producer certificates.

Select from the checked base/NBA residuals, without CPU names or expected ISA
answers. Whole-order producer completeness is attempted only after Coq reports
zero residuals. It is not an ordered/LFP/global-invariant certificate.
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
import cpu_comb_residual_diagnostics as diagnostics
import cpu_scalar_captures as scalar
from cpu_certificate_acceptance import run_stage, SYMBOL


def proposal(profile,short_circuit_indices=False):
    if type(short_circuit_indices) is not bool:
        raise ValueError('short_circuit_indices must be boolean')
    ast,_,_=registry.proposal(profile)  # Reuse strict symbol/import validation.
    binding=profile['ast'];p=binding['program']
    imports=[binding['module'],*binding.get('program_imports',[])]
    lines=['From Coq Require Import List Bool PeanoNat.',
        'Require Import Lang.ExtendedSV Lang.ExtendedSVCombIdempotence',
        ' Lang.ExtendedSVCombRuleRegistry Lang.ExtendedSVCombRuleAssembly',
        ' Lang.ExtendedSVKnownProducer Ex.External.CPUCombRuleCatalog',
        ' Ex.External.CPUCombNBAExtendedCatalog '+' '.join(imports)+'.',
        'Import ListNotations ExtendedSV ExtendedSVCombIdempotence ExtendedSVCombRuleRegistry',
        ' ExtendedSVCombRuleAssembly ExtendedSVKnownProducer CPUCombRuleCatalog CPUCombNBAExtendedCatalog.',
        f'Definition actual_order := filter is_comb (processes {p}).',
        'Definition base_residual := residual_order producer_rules_with_nba actual_order.',
        f'Definition inferred_order := filter (known_producerb {p}) base_residual.',
        f'Definition remaining_order := filter (fun proc=>negb(known_producerb {p} proc)) base_residual.',
        f'Lemma actual_fuel_check : Nat.ltb 0 (statement_fuel {p})=true.',
        'Proof. vm_compute. reflexivity. Qed.',
        f'Lemma actual_fuel_positive : (0<statement_fuel {p})%nat.',
        f'Proof. exact(proj1(Nat.ltb_lt 0(statement_fuel {p}))actual_fuel_check). Qed.']
    for label,term in [('TOTAL','length actual_order'),('BASE_RESIDUAL','length base_residual'),
                       ('NEW_ACCEPTED','length inferred_order'),('REMAINING','length remaining_order'),
                       ('LFP_FUEL',f'lfp_fuel {p}'),('STATEMENT_FUEL',f'statement_fuel {p}')]:
        lines += [f'Goal True. let n:=eval vm_compute in ({term}) in idtac "KNOWN_{label}" n. exact I. Qed.']
    index_header=([f'Definition accepted_indices := map fst (filter (fun ip=>if is_comb(snd ip) then',
        f' if producer_accepted producer_rules_with_nba(snd ip) then false else known_producerb {p}(snd ip) else false)']
        if short_circuit_indices else
        [f'Definition accepted_indices := map fst (filter (fun ip=>is_comb(snd ip) &&',
         f' negb(producer_accepted producer_rules_with_nba(snd ip)) && known_producerb {p}(snd ip))'])
    lines += index_header + [
        f' (combine (seq 0(length(processes {p}))) (processes {p}))).',
        'Goal True. let ids:=eval vm_compute in accepted_indices in idtac "KNOWN_ACCEPTED_INDICES" ids. exact I. Qed.',
        f'Local Opaque actual_order {p} ProducerIdempotent.',
        f'Theorem actual_inferred_producers : Forall (ProducerIdempotent {p}) inferred_order.',
        f'Proof. exact(checked_known_producers {p} base_residual). Qed.',
        f'Theorem original_producers_if_remaining_empty : remaining_order=[] -> Forall (ProducerIdempotent {p}) actual_order.',
        'Proof. intro HE.',
        f' exact(complete_registry_from_residual producer_rules_with_nba {p} actual_order actual_fuel_positive',
        f' (known_residual_complete {p} base_residual HE)). Qed.']
    for i,name in enumerate(('actual_inferred_producers','original_producers_if_remaining_empty')):
        lines += [f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{i}". exact I. Qed.',f'Print Assumptions {name}.']
    return ast,'\n'.join(lines)+'\n'


def counts(log):
    result={}
    for key in ('TOTAL','BASE_RESIDUAL','NEW_ACCEPTED','REMAINING','LFP_FUEL','STATEMENT_FUEL'):
        matches=re.findall(r'^KNOWN_'+key+r'\s+(\d+)\s*$',log,re.M)
        if len(matches)!=1:
            raise ValueError('missing or ambiguous actual Coq count '+key)
        result[key.lower()]=int(matches[0])
    if (result['base_residual']>result['total'] or
        result['new_accepted']+result['remaining']!=result['base_residual']):
        raise ValueError('actual residual partition is inconsistent')
    return result


def completion_source(profile,known_module='GeneratedKnownProducers.Known'):
    binding=profile['ast'];p=binding['program']
    extra=binding.get('program_imports',[])
    if not isinstance(extra,list):raise ValueError('program imports must be a list')
    imports=[binding['module'],*extra]
    if not all(isinstance(s,str) and SYMBOL.fullmatch(s) for s in [p,*imports,known_module]):
        raise ValueError('program and imports must be Coq symbols')
    # Require is not transitive Import: the actual runtime's short module name
    # may only become visible after these explicit original namespace imports.
    return ('From Coq Require Import List.\n'
        'Require Import Lang.ExtendedSV Lang.ExtendedSVCombIdempotence '+known_module+' '+
        ' '.join(imports)+'.\n'
        'Import ListNotations ExtendedSV ExtendedSVCombIdempotence.\n'
        + ('' if known_module=='GeneratedKnownProducers.Known' else
           'Module Known := '+known_module+'.\n') +
        'Lemma original_remaining_empty : Known.remaining_order=[].\n'
        'Proof. vm_compute. reflexivity. Qed.\n'
        f'Theorem all_original_producers : Forall (ProducerIdempotent {p}) Known.actual_order.\n'
        'Proof. exact(Known.original_producers_if_remaining_empty original_remaining_empty). Qed.\n'
        'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_0". exact I. Qed.\n'
        'Print Assumptions all_original_producers.\n')


def check_profile(profile,output,timeout=1200,short_circuit_indices=True):
    output=Path(output)
    if output.exists():raise ValueError('use a fresh result directory')
    output.mkdir(parents=True)
    ast,text=proposal(profile,short_circuit_indices)
    source=output/'Known.v';source.write_text(text)
    flags=list(adapter.framework.FLAGS)
    for entry in profile.get('coq_load_paths',[]):flags+=['-R',entry['directory'],entry['namespace']]
    flags+=['-R',str(output.resolve()),'GeneratedKnownProducers']
    report=dict(accepted=False,source_sha256=hashlib.sha256(text.encode()).hexdigest(),
        ast_sha256=ast['source_sha256'],actual_program=profile['ast']['program'],
        complete_original_producer_list_proved=False,original_ordered_certificate_proved=False,
        original_full_phase_proved=False,new_global_invariant_synthesized=False,
        itree_refinement_proved=False,llm_calls=0,short_circuit_indices=short_circuit_indices)
    start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-time',*flags,str(source.resolve())],output/'coqc.log',timeout)
    report.update(coqc_exit=c.returncode,coqc_timed_out=t,coqc_seconds=time.monotonic()-start)
    if c.returncode==0:
        report['counts']=counts(c.stdout)
        indices=diagnostics.parse_indices(c.stdout.replace('KNOWN_ACCEPTED_INDICES','REGISTRY_RESIDUAL_INDICES'))
        if len(indices)!=report['counts']['new_accepted']:raise ValueError('accepted indices do not match count')
        report['newly_covered']=diagnostics.describe(ast,indices)
        for row in report['newly_covered']:
            row['producer_idempotence_proved']=False  # Upgrade only after native kernel below.
        report['assumptions_closed']=scalar.audit_output(c.stdout,2)
        remaining=deadline-time.monotonic()
        if remaining>0:
            ks=time.monotonic()
            k,t=run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                'GeneratedKnownProducers.Known'],output/'coqchk.log',remaining)
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,coqchk_seconds=time.monotonic()-ks)
            report['accepted']=report['assumptions_closed'] and k.returncode==0
        if report['accepted']:
            for row in report['newly_covered']:row['producer_idempotence_proved']=True
        if report['accepted'] and report['counts']['remaining']==0:
            complete=completion_source(profile)
            report['complete_source_sha256']=hashlib.sha256(complete.encode()).hexdigest()
            complete_path=output/'Complete.v';complete_path.write_text(complete)
            remaining=deadline-time.monotonic()
            if remaining>0:
                cs=time.monotonic()
                cc,ct=run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-time',*flags,str(complete_path.resolve())],
                    output/'complete.coqc.log',remaining)
                report.update(complete_coqc_exit=cc.returncode,complete_coqc_timed_out=ct,
                    complete_coqc_seconds=time.monotonic()-cs)
                report['complete_assumptions_closed']=cc.returncode==0 and scalar.audit_output(cc.stdout,1)
                if report['complete_assumptions_closed']:
                    remaining=deadline-time.monotonic()
                    if remaining>0:
                        ks=time.monotonic()
                        kk,kt=run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                            'GeneratedKnownProducers.Complete'],output/'complete.coqchk.log',remaining)
                        report.update(complete_coqchk_exit=kk.returncode,complete_coqchk_timed_out=kt,
                            complete_coqchk_seconds=time.monotonic()-ks)
                        report['complete_original_producer_list_proved']=kk.returncode==0
            report['accepted']=report['accepted'] and report['complete_original_producer_list_proved']
    report['overall_seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    report=check_profile(json.loads(args.profile.read_text()),args.output)
    print(json.dumps(report,indent=2));raise SystemExit(0 if report['accepted'] else 1)
