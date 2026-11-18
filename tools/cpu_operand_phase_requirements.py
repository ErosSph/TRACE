"""Generate sampled/hold value relations from actual scalar phase certificates.

No token identities or reference values are guessed. Unsupported mixed writers
remain residuals, even when the supported subset has checked relations.
"""
import argparse
import hashlib
import json
import time
from pathlib import Path
import cpu_pending_origins as origin
import cpu_operand_routes as routes
import cpu_operand_route_proofs as values
from cpu_certificate_acceptance import run_stage


def capture_paths(expression, destination):
    """Mirror copy_source; unknown terminals are never labelled inactive."""
    rtl=origin.pending.rtl
    if expression.name=='EVar' and expression.args[0].name=='32':
        root=int(expression.args[1].name)
        return dict(kind='self_hold' if root==destination else 'copy',source=root)
    if expression.name=='ECond' and expression.args[0].name=='32':
        _,guard,yes,no=expression.args
        return dict(kind='guard',expression=rtl.render(guard),
            zero=capture_paths(no,destination),nonzero=capture_paths(yes,destination))
    return dict(kind='unsupported_noncopy',expression=rtl.render(expression),
        means_invalid_instruction=False,
        roots=sorted({int(n.args[1].name)for n in rtl.walk(expression)if n.name=='EVar'}))


def proposal(profile, roots):
    ast,residuals,outputs,source,count=origin.expressions.proposal(profile,roots)
    p=profile['ast']['program']
    lines=['Require Import Lang.ExtendedSVPhaseValueRequirements Ex.External.CPUActualSourceCapture Ex.External.CPUReadyOperand Ex.External.CPUReferenceCutTransfer Ex.External.CPUActualCaptureReference Ex.External.CPUSelfHoldReference.',
           'Import ExtendedSVPhaseValueRequirements CPUActualSourceCapture CPUReadyOperand CPUReferenceCuts.CPUReferenceCuts CPUGeneratedJointTemplate.CPUGeneratedJointTemplate CPUReferenceCutTransfer CPUActualCaptureReference CPUSelfHoldReference ExtendedSVInstructionOrigin.ExtendedSVInstructionOrigin.']
    for row in outputs:
        r,w=row['root'],row['width'];proc=ast['module']+'.'+row['process']
        name=f'root_{r}'
        lines += [f'Definition {name}_sample_R ev pre expected : Prop :=',
            f' phase_requirements {p} {proc} {w} {r} {name}_expression ev pre expected.',
            f'Theorem {name}_sample_R_exact ev pre expected : changed_signal ev<>{r}%nat ->',
            f' ({name}_sample_R ev pre expected <->',
            f' norm {w}(read_signal(PhaseSemantics {p} ev pre){r})=expected).',
            f'Proof. intro HE;unfold {name}_sample_R;',
            f' exact(phase_requirements_exact {p} {proc} {w} {r} {name}_expression',
            f' ev pre expected ({name}_expression_phase ev pre HE)). Qed.',
            f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{count}". exact I. Qed.',
            f'Print Assumptions {name}_sample_R_exact.']
        count+=1
        # Retain the exact token/reference cut across a real non-triggered phase.
        # The queue transfer and successful retiring ISA chain remain explicit;
        # this is not a proof that a reachable CPU satisfies those premises.
        lines += [f'Theorem {name}_held_token_transfer {{Architecture Token:Type}}',
            ' (effect:Token->Architecture->option Architecture) (project:Architecture->Z)',
            ' ev pre initial advanced retiring kept added index token :',
            f' changed_signal ev<>{r}%nat ->',
            f' process_matches_states pre(phase_driven_state {p} ev pre){proc}=false ->',
            ' EffectChain effect initial retiring advanced ->',
            f' FieldAtToken effect project initial(retiring++kept)(length retiring+index)token(norm {w}(read_signal pre {r})) ->',
            f' FieldAtToken effect project advanced(kept++added)index token(norm {w}(read_signal(PhaseSemantics {p} ev pre){r})).',
            'Proof. intros HE HF HC HR.',
            f' rewrite ({name}_expression_phase ev pre HE),HF.',
            f' exact(field_cycle effect project initial advanced retiring kept added index token',
            f' (norm {w}(read_signal pre {r})) HC HR). Qed.',
            f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{count}". exact I. Qed.',
            f'Print Assumptions {name}_held_token_transfer.']
        count+=1
        if w==32:
            if has_self_hold(capture_paths(row['expression'],r)):
                lines += [f'Theorem {name}_selected_self_hold_transfer {{Architecture Token:Type}}',
                    ' (effect:Token->Architecture->option Architecture) (project:Architecture->Z)',
                    ' ev pre initial advanced retiring kept added index token :',
                    f' changed_signal ev<>{r}%nat ->',
                    f' copy_source(phase_driven_state {p} ev pre){name}_expression=Some {r}%nat ->',
                    ' EffectChain effect initial retiring advanced ->',
                    f' FieldAtToken effect project initial(retiring++kept)(length retiring+index)token(norm 32(read_signal pre {r})) ->',
                    f' FieldAtToken effect project advanced(kept++added)index token(norm 32(read_signal(PhaseSemantics {p} ev pre){r})).',
                    'Proof. intro HE.',
                    f' exact(self_hold_token_transfer effect project {p} {proc} {r} {name}_expression',
                    ' ev pre initial advanced retiring kept added index token',
                    f' {name}_comb_frame HE ({name}_expression_phase ev pre HE)). Qed.',
                    f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{count}". exact I. Qed.',
                    f'Print Assumptions {name}_selected_self_hold_transfer.']
                count+=1
            lines += [f'Definition {name}_capture_source ev pre :=',
                f' capture_source {p} {proc} {r} {name}_expression ev pre.',
                f'Definition {name}_captured_R ev pre physical address slots :=',
                f' captured_source_R {p} {proc} {r} {name}_expression ev pre physical address slots.',
                f'Theorem {name}_actual_capture_ready ev pre physical address slots input :',
                f' changed_signal ev<>{r}%nat ->',
                f' {name}_captured_R ev pre physical address slots ->',
                f' {name}_capture_source ev pre=Some input ->',
                f' resolve 0%Z physical address slots=Some(norm 32(read_signal(PhaseSemantics {p} ev pre){r})).',
                f'Proof. intro HE;exact(actual_capture_ready {p} {proc} {r} {name}_expression ev pre',
                f' physical address slots input ({name}_expression_phase ev pre HE)). Qed.',
                f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{count}". exact I. Qed.',
                f'Print Assumptions {name}_actual_capture_ready.']
            count+=1
            lines += [f'Theorem {name}_captured_token_transfer {{Architecture Token:Type}}',
                ' (effect:Token->Architecture->option Architecture) (project:Architecture->Z)',
                ' ev pre input initial advanced retiring kept added index token :',
                f' changed_signal ev<>{r}%nat ->',
                f' {name}_capture_source ev pre=Some input ->',
                ' EffectChain effect initial retiring advanced ->',
                f' FieldAtToken effect project initial(retiring++kept)(length retiring+index)token(norm 32(read_signal(phase_driven_state {p} ev pre)input)) ->',
                f' FieldAtToken effect project advanced(kept++added)index token(norm 32(read_signal(PhaseSemantics {p} ev pre){r})).',
                'Proof. intro HE.',
                f' exact(captured_token_transfer effect project {p} {proc} {r} {name}_expression',
                ' ev pre input initial advanced retiring kept added index token',
                f' ({name}_expression_phase ev pre HE)). Qed.',
                f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{count}". exact I. Qed.',
                f'Print Assumptions {name}_captured_token_transfer.']
            count+=1
            lines += [f'Theorem {name}_unready_blocks_capture ev pre physical address slots input :',
                f' address<>0%Z ->lookup address slots=Some None ->',
                f' {name}_captured_R ev pre physical address slots ->',
                f' {name}_capture_source ev pre<>Some input.',
                f'Proof. exact(unready_blocks_actual_capture {p} {proc} {r} {name}_expression ev pre physical address slots input). Qed.',
                f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{count}". exact I. Qed.',
                f'Print Assumptions {name}_unready_blocks_capture.']
            count+=1
    return ast,residuals,outputs,source+'\n'+'\n'.join(lines)+'\n',count


def has_self_hold(plan):
    if plan['kind']=='self_hold':return True
    if plan['kind']=='guard':
        return has_self_hold(plan['zero']) or has_self_hold(plan['nonzero'])
    return False


def check_profile(profile, output, roots, timeout=1200):
    if not 0<timeout<=1200:raise ValueError('budget must be at most 20 minutes')
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    ast,residuals,outputs,source,count=proposal(profile,roots)
    path=output/'ScalarExpressions.v';path.write_text(source)
    exported=[]
    for row in outputs:
        inputs=sorted({tuple(int(a.name)for a in n.args)
            for n in origin.pending.rtl.walk(row['expression'])if n.name=='EVar'})
        exported.append(dict(root=row['root'],width=row['width'],process=row['process'],
            expression=origin.pending.rtl.render(row['expression']),sampled_inputs=inputs,
            trigger='actual process_matches_states at phase_driven_state',
            triggered_requirement=values.requirement_plan(row['expression'],row['width']),
            untriggered_requirement='normalized pre-state field equals reference'))
        if row['width']==32:
            exported[-1]['physical_capture_condition']='actual process trigger AND selected full-word copy AND source != destination'
            exported[-1]['capture_none_means']='no supported non-self copy; not an empty ISA slot'
            exported[-1]['capture_paths']=capture_paths(row['expression'],row['root'])
    (output/'requirements.json').write_text(json.dumps(exported,indent=2)+'\n')
    report=dict(accepted=False,phase_value_relations_checked=False,
        complete_R_generated=False,operand_freshness_proved=False,old_inv_read=False,
        reference_binding_proved=False,ast_sha256=ast['source_sha256'],
        physical_copy_capture_conditions_generated=sum(r['width']==32 for r in outputs),
        architectural_consumption_identified=False,
        held_token_transfer_obligations_generated=len(outputs),
        captured_token_transfer_obligations_generated=sum(r['width']==32 for r in outputs),
        actual_queue_transfer_proved=False,
        generated_source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        outputs=exported,residuals=residuals,audited_exports=count,llm_calls=0)
    if residuals or not outputs:report['status']='unsupported_scalar_expression_selection'
    if outputs:
        flags=list(origin.pending.rtl.framework.FLAGS)
        for extra in profile.get('coq_load_paths',[]):flags+=['-R',extra['directory'],extra['namespace']]
        flags+=['-R',str(output.resolve()),'GeneratedScalarExpressions']
        start=time.monotonic();deadline=start+timeout
        c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],
            output/'coqc.log',deadline-time.monotonic())
        report.update(coqc_exit=c.returncode,coqc_timed_out=t)
        if c.returncode==0 and time.monotonic()<deadline:
            report['assumptions_closed']=origin.captures.audit_output(c.stdout,count)
            k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                'GeneratedScalarExpressions.ScalarExpressions'],output/'coqchk.log',deadline-time.monotonic())
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t)
            report['phase_value_relations_checked']=report['assumptions_closed'] and k.returncode==0
            report['accepted']=report['phase_value_relations_checked'] and not residuals
        report['seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


def check(ast_path, ast_module, output):
    ast,profile,paths=origin.raw_binding(ast_path,ast_module)
    profile['coq_load_paths']=paths
    roots=sorted({r['root']for r in routes.discover(ast)['routes']if r['crossed_sampling_boundary']})
    if roots:return check_profile(profile,output,roots)
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    report=dict(accepted=False,status='no_copy_storage_discovered_not_a_completeness_claim',
        roots=[],old_inv_read=False,complete_R_generated=False)
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ['ast','ast-module','output']:parser.add_argument('--'+name,required=True)
    args=parser.parse_args();result=check(args.ast,args.ast_module,args.output)
    print(json.dumps(result,indent=2))
    raise SystemExit(0 if result['accepted'] else 1)
