"""Generate actual blocking two-stage certificates, not old-state snapshots.

Recognize a closed AST pattern, check dependence exclusions again in Coq, and
instantiate width/root-symbolic algebra. No CPU names, signal IDs or LLM calls.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import time
import cpu_auto_adapter as adapter
import cpu_scalar_captures as scalar
from cpu_certificate_acceptance import run_stage, SYMBOL


def extract(body):
    def seq(node):
        if node.name!='SSeq' or len(node.args)!=1 or node.args[0].name!='list':
            raise ValueError('requires original nested two-stage sequence')
        return node.args[0].args
    outer=seq(body)
    if len(outer)!=1:raise ValueError('requires one nested sequence')
    steps=seq(outer[0])
    if len(steps)!=4:raise ValueError('requires two default/case stages')
    stages=[]
    for default,case in (steps[:2],steps[2:]):
        if default.name!='SAssign' or default.args[0].name!='false':
            raise ValueError('requires blocking default assignment')
        _,fallback,lhs=default.args
        if lhs.name!='LVar':raise ValueError('requires whole scalar target')
        width,root=(int(a.name) for a in lhs.args)
        if width<=0 or root<0:raise ValueError('invalid scalar target')
        if case.name!='SCase' or case.args[0]!=adapter.Term('EConst',(adapter.Term('1'),adapter.Term('1'))):
            raise ValueError('requires original priority case of one')
        arms=[]
        for arm in case.args[1].args:
            key,statement=arm.args
            if key.name!='Some' or statement.name!='SAssign' or statement.args[0].name!='false' or statement.args[2]!=lhs:
                raise ValueError('case must write the same whole scalar with explicit keys')
            arms.append((key.args[0],statement.args[1]))
        terms=[fallback]+[t for arm in arms for t in arm]
        reads={int(n.args[1].name) for term in terms for n in adapter.walk(term) if n.name=='EVar'}
        stages.append(dict(width=width,root=root,fallback=fallback,arms=arms,reads=reads))
    first,second=stages
    if first['root']==second['root']:raise ValueError('outputs must be distinct')
    if first['reads']&{first['root'],second['root']}:
        raise ValueError('first stage depends on a previous output')
    if second['root'] in second['reads']:
        raise ValueError('second stage depends on its previous output')
    return stages


def proposal(profile,prove_phase=False):
    if type(prove_phase)is not bool:raise ValueError('prove_phase must be boolean')
    binding=profile['ast']
    extra=binding.get('program_imports',[])
    if not isinstance(extra,list):raise ValueError('imports must be a list')
    imports=[binding['module'],*extra]
    if not all(isinstance(s,str) and SYMBOL.fullmatch(s) for s in [binding['program'],*imports]):
        raise ValueError('imports and program must be Coq symbols')
    ast=adapter.load_ast(adapter.ROOT/binding['file'])
    selected=[];residual=[]
    for index,proc in enumerate(ast['processes']):
        if proc['kind']!='Combinational':continue
        try:stages=extract(proc['body'])
        except ValueError as error:
            residual.append(dict(process=proc['name'],reason=str(error)));continue
        selected.append((index,proc,stages))
    lines=['From Coq Require Import List Bool ZArith.',
        'Require Import Lang.ExtendedSV Lang.ExtendedSVBlocking Lang.ExtendedSVCombIdempotence Lang.ExtendedSVExprAgreement',
        ' Lang.ExtendedSVOverwrittenScalarStages Lang.ExtendedSVTwoStageProducer',
        ' Lang.ExtendedSVCombRuleRegistry Lang.ExtendedSVInferredProducerCertificate Ex.External.CPUCombRuleCatalog',
        ' Lang.ExtendedSVCombRuleAssembly',
        ' Lang.ExtendedSVForeignUpdateTransport Lang.ExtendedSVStaticProcessGroups',
        ' Lang.ExtendedSVPhaseCertificate '+ ' '.join(imports)+'.',
        'Import ListNotations ExtendedSV ExtendedSVBlocking ExtendedSVCombIdempotence ExtendedSVExprAgreement',
        ' ExtendedSVOverwrittenScalarStages ExtendedSVTwoStageProducer',
        ' ExtendedSVCombRuleRegistry ExtendedSVInferredProducerCertificate CPUCombRuleCatalog ExtendedSVForeignUpdateTransport',
        ' ExtendedSVCombRuleAssembly',
        ' ExtendedSVStaticProcessGroups ExtendedSVPhaseCertificate.',
        'Local Opaque chosen_value scalar_write.']
    audits=[]
    p=binding['program']
    for index,proc,stages in selected:
        name=proc['name'];actual=ast['module']+'.'+name
        lines.append('Module '+name+'_Stages.')
        for number,stage in enumerate(stages,1):
            arms='['+';'.join('('+adapter.render(key)+','+adapter.render(rhs)+')' for key,rhs in stage['arms'])+']'
            lines += [f'Definition fallback{number} := {adapter.render(stage["fallback"])}.',
                f'Definition arms{number} : list(Expr*Expr) := {arms}.']
        a,b=stages
        args=f'{a["width"]}%nat {a["root"]}%nat arms1 fallback1 {b["width"]}%nat {b["root"]}%nat arms2 fallback2'
        checks=[('first_self',1,a['root']),('first_second',1,b['root']),('second_self',2,b['root'])]
        for label,stage,root in checks:
            lines += [f'Lemma {label} : avoids_rootb(arm_inputs arms{stage}++expr_inputs fallback{stage}){root}%nat=true.',
                'Proof. vm_compute. reflexivity. Qed.']
        lines += [f'Lemma first_inputs : forall iw,In iw(arm_inputs arms1++expr_inputs fallback1)->',
            f' snd iw<>{a["root"]}%nat /\ snd iw<>{b["root"]}%nat.',
            f'Proof. intros iw HI. exact(conj(avoids_rootb_sound _ _ first_self iw HI)',
            ' (avoids_rootb_sound _ _ first_second iw HI)). Qed.',
            f'Lemma second_inputs : forall iw,In iw(arm_inputs arms2++expr_inputs fallback2)->snd iw<>{b["root"]}%nat.',
            'Proof. exact(avoids_rootb_sound _ _ second_self). Qed.',
            f'Lemma actual_shape : process_body {actual}=',
            f' SSeq[SSeq[SAssign false fallback1(LVar {a["width"]} {a["root"]}%nat);',
            f' SCase(EConst 1 1)(scalar_arms {a["width"]} {a["root"]}%nat arms1);',
            f' SAssign false fallback2(LVar {b["width"]} {b["root"]}%nat);',
            f' SCase(EConst 1 1)(scalar_arms {b["width"]} {b["root"]}%nat arms2)]].',
            'Proof. reflexivity. Qed.',
            f'Lemma actual_statement_fuel : statement_fuel {p}={ast["statement_fuel"]}%nat.',
            'Proof. reflexivity. Qed.',
            f'Lemma actual_output s : run_process {p} s {actual}=two_stage_output {args} s.',
            'Proof.',
            ' rewrite blocking_run_process by(vm_compute;reflexivity).',
            ' rewrite actual_shape,actual_statement_fuel.',
            ' rewrite two_stage_sequence_groups,scalar_stages_connection.',
            ' 2:{ intros iw HI. exact(proj1(first_inputs iw(in_or_app _ _ _(or_introl HI)))). }',
            ' 2:{ intros iw HI. exact(second_inputs iw(in_or_app _ _ _(or_introl HI))). }',
            ' reflexivity.',
            'Qed.',
            f'Theorem actual_idempotent : ProducerIdempotent {p} {actual}.',
            f'Proof. apply(actual_two_stage_producer {args});',
            ' [discriminate|exact first_inputs|exact second_inputs|exact actual_output]. Qed.',
            f'Lemma registered : nth_error(processes {p}){index}%nat=Some {actual}.',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Lemma actual_kind : process_kind {actual}=Combinational.',
            'Proof. reflexivity. Qed.',
            'End '+name+'_Stages.']
        audits += [name+'_Stages.actual_output',name+'_Stages.actual_idempotent',name+'_Stages.registered',name+'_Stages.actual_kind']
    if prove_phase:
        selected_list='['+';'.join(ast['module']+'.'+proc['name']for _,proc,_ in selected)+']'
        lines += [f'Definition original_comb_order := filter is_comb(processes {p}).',
            'Lemma original_residual_shape : residual_order producer_rules original_comb_order='+selected_list+'.',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Lemma actual_fuel_positive : (0<statement_fuel {p})%nat.',
            'Proof. vm_compute. repeat constructor. Qed.',
            f'Local Opaque {p} original_comb_order ProducerIdempotent.',
            f'Lemma original_residual_producers : Forall(ProducerIdempotent {p})(residual_order producer_rules original_comb_order).',
            'Proof.',
            ' rewrite original_residual_shape.']
        for _,proc,_ in selected:
            lines += [' constructor;[exact '+proc['name']+'_Stages.actual_idempotent|].']
        lines += [' constructor.', 'Qed.',
            f'Theorem all_original_producers : Forall(ProducerIdempotent {p})original_comb_order.',
            f'Proof. exact(complete_registry_from_residual producer_rules {p}',
            ' original_comb_order actual_fuel_positive original_residual_producers). Qed.',
            'Lemma original_preservation_check : ordered_preservationb original_comb_order=true.',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Lemma original_fuel_one : lfp_fuel {p}=1%nat.',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Lemma original_sequential_disjoint : sequential_writers_disjointb {p}=true.',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Theorem original_ordered_certificate : OrderedProducerCertificate {p} original_comb_order.',
            f'Proof. exact(ordered_registry_from_residual producer_rules {p} original_comb_order',
            ' actual_fuel_positive original_residual_producers original_preservation_check). Qed.',
            'Local Transparent original_comb_order.',
            f'Theorem original_phase ev pre :',
            f' let driven:=phase_driven_state {p} ev pre in',
            f' CombLFP {p}(write_signal pre(changed_signal ev)(new_value ev))driven /\\',
            f' CombLFP {p}(execute_process_order {p} driven(selected_on_transition {p} pre driven))',
            f' (PhaseSemantics {p} ev pre) /\\ PhaseIndependentAt {p} ev pre.',
            f'Proof. exact(original_phase_from_registry_residual producer_rules {p}',
            ' actual_fuel_positive original_residual_producers original_preservation_check',
            ' original_fuel_one original_sequential_disjoint ev pre). Qed.']
        audits += ['all_original_producers','original_ordered_certificate','original_phase']
    for i,name in enumerate(audits):
        lines += [f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{i}". exact I. Qed.',f'Print Assumptions {name}.']
    metadata=[dict(process=proc['name'],index=index,stages=[dict(width=s['width'],root=s['root'],reads=sorted(s['reads'])) for s in stages])for index,proc,stages in selected]
    return ast,metadata,residual,'\n'.join(lines)+'\n',len(audits)


def emit_library(profile,path,prove_phase=False):
    """Persist exact generated text, without claiming it has been checked."""
    path=Path(path)
    if not path.is_absolute():path=adapter.ROOT/path
    try:path.resolve().relative_to(adapter.ROOT/'src/Ex/Generated')
    except ValueError:raise ValueError('library must stay under src/Ex/Generated')
    if path.suffix!='.v':raise ValueError('library must be a .v')
    _,_,_,text,_=proposal(profile,prove_phase)
    if path.exists() and path.read_text()!=text:
        raise ValueError('refuse to overwrite a different generated library')
    path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
    return path


def check_profile(profile,output,timeout=1200,prove_phase=False):
    output=Path(output)
    if output.exists():raise ValueError('output must be fresh')
    output.mkdir(parents=True)
    ast,selected,residuals,text,count=proposal(profile,prove_phase)
    source=output/'TwoStage.v';source.write_text(text)
    flags=list(adapter.framework.FLAGS)
    for path in profile.get('coq_load_paths',[]):flags+=['-R',path['directory'],path['namespace']]
    flags+=['-R',str(output.resolve()),'GeneratedTwoStage']
    report=dict(accepted=False,selected=selected,residuals=residuals,audited_exports=count,
        has_selected_producers=bool(selected),
        source_sha256=hashlib.sha256(text.encode()).hexdigest(),ast_sha256=ast['source_sha256'],
        requested_original_phase=prove_phase,original_full_phase_proved=False,
        global_invariant_synthesized=False,itree_refinement_proved=False,llm_calls=0)
    start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-time',*flags,str(source.resolve())],output/'coqc.log',max(0.01,deadline-time.monotonic()))
    report.update(coqc_exit=c.returncode,coqc_timed_out=t,coqc_seconds=time.monotonic()-start)
    if c.returncode==0:
        report['assumptions_closed']=scalar.audit_output(c.stdout,count) if count else True
        remaining=deadline-time.monotonic()
        if remaining>0:
            kernel_start=time.monotonic()
            k,t=run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedTwoStage.TwoStage'],output/'coqchk.log',remaining)
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,coqchk_seconds=time.monotonic()-kernel_start)
            report['accepted']=report['assumptions_closed'] and k.returncode==0
            report['original_full_phase_proved']=report['accepted'] and prove_phase
        else:report['kernel_not_run_due_to_overall_deadline']=True
    report['overall_seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--prove-phase',action='store_true')
    args=parser.parse_args()
    report=check_profile(json.loads(args.profile.read_text()),args.output,prove_phase=args.prove_phase)
    print(json.dumps(report,indent=2))
    raise SystemExit(0 if report['accepted'] else 1)
