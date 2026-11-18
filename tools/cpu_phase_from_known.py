"""Connect checked complete actual-fuel producers to the original phase API.

No CPU-name branches or replacement Program. Failed preservation/disjointness
checks are ineligible, not proof of a DUT bug or successful phase generation.
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
import cpu_scalar_captures as scalar
from cpu_certificate_acceptance import run_stage
from cpu_certificate_acceptance import SYMBOL


def header(profile,known_module='GeneratedKnownProducers.Known',
           complete_module='GeneratedKnownProducers.Complete'):
    known.completion_source(profile)  # Validate symbols and runtime import list.
    if not all(isinstance(s,str) and SYMBOL.fullmatch(s) for s in (known_module,complete_module)):
        raise ValueError('certificate imports must be Coq symbols')
    b=profile['ast'];imports=[b['module'],*b.get('program_imports',[])]
    lines=['From Coq Require Import List Bool PeanoNat.',
        'Require Import Lang.ExtendedSV Lang.ExtendedSVCombIdempotence',
        ' Lang.ExtendedSVForeignUpdateTransport Lang.ExtendedSVStaticProcessGroups',
        ' Lang.ExtendedSVCombPositiveFuel Lang.ExtendedSVPhaseCertificate',
        ' Lang.ExtendedSVTransportRuleAssembly Ex.External.CPUCombRuleCatalog',
        ' '+known_module+' '+complete_module+' '+' '.join(imports)+'.',
        'Import ListNotations ExtendedSV ExtendedSVCombIdempotence ExtendedSVForeignUpdateTransport',
        ' ExtendedSVStaticProcessGroups ExtendedSVCombPositiveFuel ExtendedSVPhaseCertificate',
        ' ExtendedSVTransportRuleAssembly CPUCombRuleCatalog.']
    if known_module!='GeneratedKnownProducers.Known':lines+=['Module Known := '+known_module+'.']
    if complete_module!='GeneratedKnownProducers.Complete':lines+=['Module Complete := '+complete_module+'.']
    return lines


def eligibility_source(profile,known_module='GeneratedKnownProducers.Known',
                       complete_module='GeneratedKnownProducers.Complete'):
    p=profile['ast']['program'];lines=header(profile,known_module,complete_module)
    lines += ['Definition preservation_check := transport_orderb transport_rules Known.actual_order.',
        f'Definition disjoint_check := sequential_writers_disjointb {p}.',
        f'Definition positive_check := Nat.ltb 0 (lfp_fuel {p}).']
    for label,name in [('PRESERVATION','preservation_check'),('DISJOINT','disjoint_check'),('POSITIVE','positive_check')]:
        lines += [f'Goal True. let b:=eval vm_compute in {name} in idtac "KNOWN_PHASE_{label}" b. exact I. Qed.']
    lines += ['Lemma eligibility_provenance : True. Proof. exact I. Qed.',
        'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_0". exact I. Qed.',
        'Print Assumptions eligibility_provenance.']
    return '\n'.join(lines)+'\n'


def phase_source(profile,known_module='GeneratedKnownProducers.Known',
                 complete_module='GeneratedKnownProducers.Complete',
                 eligibility_module='GeneratedKnownPhase.Eligibility'):
    if not isinstance(eligibility_module,str) or not SYMBOL.fullmatch(eligibility_module):
        raise ValueError('eligibility import must be a Coq symbol')
    p=profile['ast']['program'];lines=header(profile,known_module,complete_module)
    lines += ['Require Import '+eligibility_module+'.']
    if eligibility_module!='GeneratedKnownPhase.Eligibility':
        lines+=['Module Eligibility := '+eligibility_module+'.']
    lines += [
        'Lemma preservation_checked : Eligibility.preservation_check=true.',
        'Proof. vm_compute. reflexivity. Qed.',
        'Lemma disjoint_checked : Eligibility.disjoint_check=true.',
        'Proof. vm_compute. reflexivity. Qed.',
        f'Lemma original_fuel_positive : (0<lfp_fuel {p})%nat.',
        f'Proof. exact(proj1(Nat.ltb_lt 0(lfp_fuel {p})) ltac:(vm_compute;reflexivity)). Qed.',
        f'Lemma original_statement_fuel_positive : (0<statement_fuel {p})%nat.',
        f'Proof. exact(proj1(Nat.ltb_lt 0(statement_fuel {p})) ltac:(vm_compute;reflexivity)). Qed.',
        f'Local Opaque {p} ProducerIdempotent.',
        f'Theorem original_ordered : OrderedProducerCertificate {p} Known.actual_order.',
        f'Proof. exact(ordered_from_checked_transports {p} transport_rules Known.actual_order',
        ' Complete.all_original_producers original_statement_fuel_positive preservation_checked). Qed.',
        'Theorem original_phase ev pre :',
        f' let driven:=phase_driven_state {p} ev pre in',
        f' CombLFP {p} (write_signal pre(changed_signal ev)(new_value ev)) driven /\\',
        f' CombLFP {p} (execute_process_order {p} driven(selected_on_transition {p} pre driven))',
        f' (PhaseSemantics {p} ev pre) /\\ PhaseIndependentAt {p} ev pre.',
        f'Proof. exact(original_positive_phase {p} original_fuel_positive original_ordered disjoint_checked ev pre). Qed.']
    for i,name in enumerate(('original_ordered','original_phase')):
        lines += [f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{i}". exact I. Qed.',f'Print Assumptions {name}.']
    return '\n'.join(lines)+'\n'


def parse_checks(log):
    result={}
    for key in ('PRESERVATION','DISJOINT','POSITIVE'):
        found=re.findall(r'^KNOWN_PHASE_'+key+r'\s+(true|false)\s*$',log,re.M)
        if len(found)!=1:raise ValueError('missing or ambiguous phase eligibility '+key)
        result[key.lower()]=found[0]=='true'
    return result


def check(profile,provider,output,timeout=1200):
    provider=Path(provider).resolve();output=Path(output)
    if output.exists():raise ValueError('output must be fresh')
    output.mkdir(parents=True)
    evidence=json.loads((provider/'report.json').read_text())
    report=dict(accepted=False,status='producer_certificate_required',
        original_full_phase_proved=False,new_global_invariant_synthesized=False,
        itree_refinement_proved=False,llm_calls=0,actual_program=profile['ast']['program'])
    if not evidence.get('accepted') or not evidence.get('complete_original_producer_list_proved'):
        (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report
    ast,text=known.proposal(profile,evidence.get('short_circuit_indices',False))
    if (evidence['actual_program']!=profile['ast']['program'] or evidence['ast_sha256']!=ast['source_sha256']
        or text!=(provider/'Known.v').read_text()
        or known.completion_source(profile)!=(provider/'Complete.v').read_text()):
        raise ValueError('producer evidence is not the exact actual profile/source')
    for file,key in (('Known.v','source_sha256'),('Complete.v','complete_source_sha256')):
        if hashlib.sha256((provider/file).read_bytes()).hexdigest()!=evidence[key]:
            raise ValueError('producer source fingerprint changed')
    report['producer_source_sha256']=evidence['source_sha256']
    report['complete_source_sha256']=evidence['complete_source_sha256']
    flags=list(adapter.framework.FLAGS)
    for e in profile.get('coq_load_paths',[]):flags+=['-R',e['directory'],e['namespace']]
    flags+=['-R',str(provider),'GeneratedKnownProducers','-R',str(output.resolve()),'GeneratedKnownPhase']
    start=time.monotonic();deadline=start+timeout
    def native(name,text,exports):
        path=output/(name+'.v');path.write_text(text)
        report[name+'_source_sha256']=hashlib.sha256(text.encode()).hexdigest()
        remaining=deadline-time.monotonic()
        if remaining<=0:return False,''
        cs=time.monotonic()
        c,t=run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/(name+'.coqc.log'),remaining)
        report.update({name+'_coqc_exit':c.returncode,name+'_coqc_timed_out':t,name+'_coqc_seconds':time.monotonic()-cs})
        audited=c.returncode==0 and scalar.audit_output(c.stdout,exports)
        report[name+'_assumptions_closed']=audited
        remaining=deadline-time.monotonic()
        if not audited or remaining<=0:return False,c.stdout
        ks=time.monotonic()
        k,t=run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
            'GeneratedKnownPhase.'+name],output/(name+'.coqchk.log'),remaining)
        report.update({name+'_coqchk_exit':k.returncode,name+'_coqchk_timed_out':t,name+'_coqchk_seconds':time.monotonic()-ks})
        return k.returncode==0,c.stdout
    ok,log=native('Eligibility',eligibility_source(profile),1)
    report['eligibility_checked']=ok
    if ok:
        checks=parse_checks(log);report['checks']=checks
        report['status']='original_phase_static_conditions_not_satisfied'
        if all(checks.values()):
            ok,_=native('Phase',phase_source(profile),2)
            report.update(accepted=ok,original_full_phase_proved=ok,
                status='proved_original_phase' if ok else 'original_phase_check_failed')
    else:report['status']='eligibility_check_failed'
    report['overall_seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile',type=Path,required=True)
    parser.add_argument('--provider',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    report=check(json.loads(args.profile.read_text()),args.provider,args.output)
    print(json.dumps(report,indent=2));raise SystemExit(0 if report['accepted'] else 1)
