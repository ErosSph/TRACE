"""Generate real-field initialization and arbitrary phase-history induction.

The shadow field owns its feedback value. Actual controls and other sampled
inputs are observations; these proofs do not imply architectural token identity,
closed dependency cones, progress, or complete CPU/ISA invariants.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import time
import cpu_auto_adapter as adapter
import cpu_scalar_expressions as expressions
import cpu_scalar_captures as scalar
from cpu_certificate_acceptance import run_stage


def self_width_supported(expression,root,width):
    return all(int(n.args[0].name)==width for n in adapter.walk(expression)
        if n.name=='EVar' and int(n.args[1].name)==root)


def proposal(profile,roots=None):
    ast,residuals,outputs,source,count=expressions.proposal(profile,roots)
    residuals=list(residuals);exports=[]
    lines=['Require Import Lang.ExtendedSVScalarHistory Lang.ExtendedSVHistoryComposition.',
        'Import ExtendedSVScalarHistory ExtendedSVHistoryComposition.']
    program=profile['ast']['program']
    for item in outputs:
        root,width,proc=item['root'],item['width'],item['process']
        if not self_width_supported(item['expression'],root,width):
            residuals.append(dict(root=root,reason='self read uses another normalized width'))
            continue
        name=f'root_{root}'
        lines += [f'Lemma {name}_self_width_checked :',
            f' self_widthb {width}%nat {root}%nat {name}_expression=true.',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Definition {name}_history_certificate : ScalarCertificate',
            f' {program} {root}%nat {width}%nat {ast["module"]}.{proc} {name}_expression :=',
            f' Build_ScalarCertificate _ _ _ _ _ {name}_comb_frame',
            f'   {name}_self_width_checked {name}_expression_phase.',
            f'Lemma {name}_history_step ev pre old : changed_signal ev<>{root}%nat ->',
            f' Related {width}%nat {root}%nat pre old ->',
            f' Related {width}%nat {root}%nat (PhaseSemantics {program} ev pre)',
            f'  (local_step {width}%nat {root}%nat {name}_expression old',
            f'   (frame_for {program} {ast["module"]}.{proc} {root}%nat ev pre)).',
            'Proof. exact (history_step _ _ _ _ _ '+name+'_history_certificate ev pre old). Qed.',
            f'Lemma {name}_history_initial pre : Related {width}%nat {root}%nat pre',
            f' (norm {width}%nat (read_signal pre {root}%nat)).',
            f'Proof. exact (history_initial {width}%nat {root}%nat pre). Qed.',
            f'Lemma {name}_history events pre :',
            f' Forall (fun ev=>changed_signal ev<>{root}%nat) events ->',
            f' norm {width}%nat (read_signal (phase_run {program} events pre) {root}%nat)=',
            f' local_run {width}%nat {root}%nat {name}_expression',
            f'  (observed_frames {program} {ast["module"]}.{proc} {root}%nat events pre)',
            f'  (norm {width}%nat (read_signal pre {root}%nat)).',
            f'Proof. exact (history_from_initial _ _ _ _ _ {name}_history_certificate events pre). Qed.']
        for suffix in ['history_certificate','history_step','history_initial','history']:
            lines += [f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{count}". exact I. Qed.',
                f'Print Assumptions {name}_{suffix}.']
            count+=1
        exports.append(dict(root=root,width=width,process=proc,
            theorem=name+'_history',step=name+'_history_step',initial=name+'_history_initial'))
    if exports:
        related=[];initial=[];steps=[];safe=[]
        for index,item in enumerate(exports):
            root,width,proc=item['root'],item['width'],item['process']
            related.append(f'Related {width}%nat {root}%nat pre (nth {index} old 0%Z)')
            initial.append(f'norm {width}%nat (read_signal pre {root}%nat)')
            steps.append(f'local_step {width}%nat {root}%nat root_{root}_expression '
                f'(nth {index} old 0%Z) (frame_for {program} {ast["module"]}.{proc} {root}%nat ev pre)')
            safe.append(f'changed_signal ev<>{root}%nat')
        lines += ['Definition FieldHistoryInvariant pre (old : list Z) : Prop := '+
            ' /\\ '.join(related+['True'])+'.',
            'Definition field_initial pre : list Z := ['+'; '.join(initial)+'].',
            'Definition field_local_phase ev pre (old : list Z) : list Z := ['+'; '.join(steps)+'].',
            'Definition field_event_safe ev : Prop := '+' /\\ '.join(safe+['True'])+'.',
            f'Definition field_replay := history_replay {program} field_local_phase.',
            'Local Opaque PhaseSemantics phase_driven_state read_signal norm Related local_step frame_for.',
            'Lemma field_history_initial pre : FieldHistoryInvariant pre (field_initial pre).',
            'Proof. cbn [FieldHistoryInvariant field_initial nth].']
        for item in exports:
            lines += [f' split; [exact (history_initial {item["width"]}%nat {item["root"]}%nat pre)|].']
        lines += [' exact I. Qed.',
            'Lemma field_history_step ev pre old : field_event_safe ev ->',
            ' FieldHistoryInvariant pre old ->',
            f' FieldHistoryInvariant (PhaseSemantics {program} ev pre) (field_local_phase ev pre old).',
            'Proof.',
            ' intros ('+' & '.join([f'HE{i}' for i in range(len(exports))]+['_'])+') ('+
                ' & '.join([f'HR{i}' for i in range(len(exports))]+['_'])+').',
            ' cbn [FieldHistoryInvariant field_local_phase nth].']
        for index,item in enumerate(exports):
            lines += [f' split; [exact (root_{item["root"]}_history_step ev pre '
                f'(nth {index} old 0%Z) HE{index} HR{index})|].']
        lines += [' exact I. Qed.',
            'Lemma field_history_sequence events : Forall field_event_safe events ->',
            ' forall pre old, FieldHistoryInvariant pre old ->',
            f' FieldHistoryInvariant (phase_run {program} events pre) (field_replay events pre old).',
            f'Proof. exact (history_invariant_sequence {program} field_event_safe',
            ' FieldHistoryInvariant field_local_phase field_history_step events). Qed.']
        for suffix in ['initial','step','sequence']:
            lines += [f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{count}". exact I. Qed.',
                f'Print Assumptions field_history_{suffix}.']
            count+=1
    return ast,residuals,exports,source+'\n'.join(lines)+'\n',count


def check_profile(profile,output,roots=None,timeout=1200):
    output=Path(output)
    if output.exists():raise ValueError('output must be fresh')
    output.mkdir(parents=True)
    ast,residuals,exports,source,count=proposal(profile,roots)
    file=output/'ScalarHistories.v';file.write_text(source)
    report=dict(accepted=False,ast_sha256=ast['source_sha256'],
        source_sha256=hashlib.sha256(source.encode()).hexdigest(),actual_program=profile['ast']['program'],
        histories=exports,residuals=residuals,audited_exports=count,llm_calls=0,
        arbitrary_event_sequences=True,self_feedback_erased=True,
        input_frames_from_actual_trace=True,architectural_identity_proved=False,
        global_invariant_synthesized=False,progress_proved=False)
    if residuals or not exports:report['status']='unsupported_scalar_history_selection'
    else:
        flags=list(adapter.framework.FLAGS)
        for extra in profile.get('coq_load_paths',[]):flags+=['-R',extra['directory'],extra['namespace']]
        flags+=['-R',str(output.resolve()),'GeneratedScalarHistories']
        start=time.monotonic()
        c,t=run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-q',*flags,str(file.resolve())],output/'coqc.log',timeout)
        report.update(coqc_exit=c.returncode,coqc_timed_out=t,coqc_seconds=time.monotonic()-start)
        if c.returncode==0:
            report['assumptions_closed']=scalar.audit_output(c.stdout,count)
            start=time.monotonic()
            k,t=run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                'GeneratedScalarHistories.ScalarHistories'],output/'coqchk.log',timeout)
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,coqchk_seconds=time.monotonic()-start)
            report['accepted']=report['assumptions_closed'] and k.returncode==0
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--profile',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--roots',type=int,nargs='+');p.add_argument('--timeout',type=float,default=1200)
    a=p.parse_args()
    if not 0<a.timeout<=1200:p.error('timeout must be positive and at most1200 seconds')
    result=check_profile(json.loads(a.profile.read_text()),a.output,a.roots,a.timeout)
    print(json.dumps(result,indent=2));return 0 if result['accepted'] else 1


if __name__=='__main__':raise SystemExit(main())
