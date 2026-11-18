"""Generate full original-phase proofs only after actual coverage is checked.

Zero residuals are necessary, not sufficient: the native full ordered check,
positive original fuel and sequential writer independence must also be proved.
No CPU names, fixed signal IDs, replacement Programs or ISA assumptions.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import time
import cpu_auto_adapter as adapter
import cpu_comb_rule_registry as registry
import cpu_scalar_captures as scalar
from cpu_certificate_acceptance import run_stage


def phase_source(profile):
    ast,text,count=registry.proposal(profile,True)
    p=profile['ast']['program']
    lines=['Require Import Lang.ExtendedSVCombPositiveFuel Lang.ExtendedSVStaticProcessGroups.',
        'Import ExtendedSVCombPositiveFuel ExtendedSVStaticProcessGroups.',
        'Local Transparent actual_order.',
        f'Local Opaque {p}.',
        f'Lemma original_iteration_budget_positive : Nat.ltb 0(lfp_fuel {p})=true.',
        'Proof. vm_compute. reflexivity. Qed.',
        f'Lemma original_iteration_budget_sound : (0<lfp_fuel {p})%nat.',
        f'Proof. exact(proj1(Nat.ltb_lt 0(lfp_fuel {p}))original_iteration_budget_positive). Qed.',
        f'Lemma original_sequential_writers_check : sequential_writers_disjointb {p}=true.',
        'Proof. vm_compute. reflexivity. Qed.',
        f'Theorem full_original_candidate_is_LFP seed : CombLFP {p} seed(lfp_candidate {p} seed).',
        f'Proof. exact(original_positive_candidate_is_LFP {p} original_iteration_budget_sound',
        ' original_ordered_certificate seed). Qed.',
        f'Theorem full_original_phase ev pre :',
        f' let driven:=phase_driven_state {p} ev pre in',
        f' CombLFP {p}(write_signal pre(changed_signal ev)(new_value ev))driven /\\',
        f' CombLFP {p}(execute_process_order {p} driven(selected_on_transition {p} pre driven))',
        f' (PhaseSemantics {p} ev pre) /\\ PhaseIndependentAt {p} ev pre.',
        f'Proof. exact(original_positive_phase {p} original_iteration_budget_sound',
        ' original_ordered_certificate original_sequential_writers_check ev pre). Qed.']
    for number,name in enumerate(('full_original_candidate_is_LFP','full_original_phase'),count):
        lines += [f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{number}". exact I. Qed.',
            f'Print Assumptions {name}.']
    return ast,text+'\n'+'\n'.join(lines)+'\n',count+2


def emit_library(profile,path):
    path=Path(path)
    if not path.is_absolute():path=adapter.ROOT/path
    try:path.resolve().relative_to(adapter.ROOT/'src/Ex/Generated')
    except ValueError:raise ValueError('library must stay under src/Ex/Generated')
    if path.suffix!='.v':raise ValueError('library must be a .v')
    _,text,_=phase_source(profile)
    if path.exists() and path.read_text()!=text:
        raise ValueError('refuse to overwrite a different generated library')
    path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
    return path


def check_profile(profile,output,timeout=1200):
    output=Path(output)
    if output.exists():raise ValueError('output must be fresh; keep previous evidence')
    output.mkdir(parents=True)
    coverage=registry.check_profile(profile,output/'coverage',timeout)
    report=dict(accepted=False,coverage_accepted=coverage['accepted'],
        original_full_phase_proved=False,global_invariant_synthesized=False,
        itree_refinement_proved=False,llm_calls=0)
    if not coverage['accepted']:
        report['status']='coverage_check_failed'
    elif coverage['counts']['residual']:
        report.update(status='unproved_original_producers_remain',counts=coverage['counts'])
    else:
        ast,text,count=phase_source(profile)
        source=output/'Phase.v';source.write_text(text)
        flags=list(adapter.framework.FLAGS)
        for entry in profile.get('coq_load_paths',[]):flags+=['-R',entry['directory'],entry['namespace']]
        flags+=['-R',str(output.resolve()),'GeneratedCombPhase']
        report.update(status='native_phase_check_failed',counts=coverage['counts'],
            source_sha256=hashlib.sha256(text.encode()).hexdigest(),
            ast_sha256=ast['source_sha256'],audited_exports=count)
        start=time.monotonic();deadline=start+timeout
        c,t=run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-time',*flags,str(source.resolve())],
            output/'coqc.log',max(0.01,deadline-time.monotonic()))
        report.update(coqc_exit=c.returncode,coqc_timed_out=t,coqc_seconds=time.monotonic()-start)
        if c.returncode==0:
            report['assumptions_closed']=scalar.audit_output(c.stdout,count)
            remaining=deadline-time.monotonic()
            if remaining>0:
                kernel_start=time.monotonic()
                k,t=run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                    'GeneratedCombPhase.Phase'],output/'coqchk.log',remaining)
                report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,
                    coqchk_seconds=time.monotonic()-kernel_start)
                report['accepted']=report['assumptions_closed'] and k.returncode==0
            else:report['kernel_not_run_due_to_overall_deadline']=True
        report['overall_phase_seconds']=time.monotonic()-start
        report['original_full_phase_proved']=report['accepted']
        if report['accepted']:report['status']='checked_original_full_phase'
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    result=check_profile(json.loads(args.profile.read_text()),args.output)
    print(json.dumps(result,indent=2))
    raise SystemExit(0 if result['accepted']else 1)
