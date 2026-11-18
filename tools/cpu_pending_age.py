"""Generate capture-age induction from raw RTL and fresh phase certificates.

Capture order is proved from actual serial allocation and prefix retirement;
it is not inferred from a historical CPU invariant or equated with ISA order.
"""
import argparse,hashlib,json,time
from pathlib import Path
import cpu_pending_rising as normal
from cpu_certificate_acceptance import run_stage
fields=normal.fields;origin=normal.origin;rtl=normal.rtl


def discover(ast):
    data=normal.discover(ast)
    return dict(paths=data['rising_paths'],residuals=data['residuals'],
        age_rule='strict capture serial order across retired plus waiting, with actual prefix consumption',
        old_inv_read=False,old_pending_read=False,old_cpu_proofs_used=False,
        isa_instruction_order_proved=False,original_runtime_ready_proved=False,
        global_inv_proved=False,itree_refinement_proved=False)


def render(ast_path,ast_module,provider,normal_provider):
    ast,profile,paths=origin.raw_binding(ast_path,ast_module);data=discover(ast)
    if len(data['paths'])!=1:raise ValueError('one actual normal phase source path required; capture age cannot replace missing instruction identity')
    nd,ns=normal.render(ast_path,ast_module,provider)
    nr=fields.verify(normal_provider,'RisingQueue.v',nd,ns)
    row=data['paths'][0]['frame']['phase'];birth=row['base']['hold']['birth'];p=profile['ast']['program']
    root=birth['carrier'];valid=birth['valid_root'];reset=row['base']['hold']['reset'];bi=row['base']['hold']['birth_index']
    proc=ast['module']+'.'+birth['process'];sample=f'(phase_driven_state {p} ev pre)';post=f'(PhaseSemantics {p} ev pre)'
    lines=['From Coq Require Import List ZArith Sorting.Sorted.',f'Require Import {ast_module}.',
        'Require Import Lang.ExtendedSV Lang.ExtendedSVCaptureBirth Lang.ExtendedSVCapturedPending Lang.ExtendedSVCaptureAge Lang.ExtendedSVScalarHistory Lang.ExtendedSVCheckedPhaseReplay',
        ' GeneratedRisingQueue.RisingQueue.',
        'Import ListNotations ExtendedSV ExtendedSVCaptureBirth ExtendedSVCapturedPending ExtendedSVCaptureAge ExtendedSVScalarHistory.',
        'Module N:=GeneratedRisingQueue.RisingQueue. Module Q:=N.Q. Module J:=N.J. Module R:=N.R. Module A:=N.A. Module B:=N.B.',
        'Module Shadow:=ExtendedSVCheckedPhaseReplay.',
        f'Local Opaque {p}.',
        'Definition OrderedCandidate pre g a:=Q.QueueCandidate pre g a /\\AgeOrdered(Live a).',
        'Lemma candidate_history_range pre g a:Q.QueueCandidate pre g a ->HistoryRange(serial(J.joint_birth g))(history(J.joint_birth g)).',
        'Proof. intro HI;pose proof(proj1(proj2 HI))as HA;',
        ' pose proof(proj1(proj1(proj1 HA)))as HB;exact(proj1(proj2(proj2 HB))). Qed.',
        'Lemma candidate_accounts pre g a:Q.QueueCandidate pre g a ->A.AccountsFor(history(J.joint_birth g))a.',
        'Proof. intro HI;exact(proj2(proj1(proj2 HI))). Qed.',
        f'Theorem ordered_initialize:OrderedCandidate(initialize {p} [])J.joint_empty A.empty.',
        'Proof. split;[exact Q.queue_candidate_initialize|constructor]. Qed.',
        'Theorem ordered_normal_phase seed0 seed ev pre g a:J.EventAllowed ev ->Q.ClockAllowed ev ->',
        f' CombLFP {p} seed0 pre ->CombLFP {p} seed{sample} ->',
        f' norm 1(read_signal{sample}{reset})<>0%Z ->OrderedCandidate pre g a ->exists next,',
        f' R.accounted_step ev pre g a 0=Some next /\\OrderedCandidate{post}(J.joint_step ev pre g)next.',
        'Proof. intros HJ HE HL0 HL HR[HQ Hage];',
        ' destruct(N.normal_phase_restores_queue_candidate seed0 seed ev pre g a HJ HE HL0 HL HR HQ)as[next[HS Hnext]].',
        ' exists next;split;[exact HS|]. split;[exact Hnext|].',
        ' unfold R.accounted_step in HS;destruct(R.retiring_candidate ev pre g)as[tokens|]eqn:HC;[|discriminate].',
        f' change(A.advance a(observed_births {p} {proc} {root} B.root_{root}_expression B.root_{valid}_expression B.capture_{bi}_pc ev pre(J.joint_birth g))tokens 0=Some next)in HS.',
        f' exact(actual_normal_advance_age {p} {proc} {root} B.root_{root}_expression B.root_{valid}_expression B.capture_{bi}_pc ev pre(J.joint_birth g)a tokens next',
        ' (candidate_history_range pre g a HQ)(candidate_accounts pre g a HQ)Hage HS). Qed.',
        'Theorem retired_older_than_waiting pre g a:OrderedCandidate pre g a ->',
        ' Forall(fun old=>Forall(Before old)(A.waiting a))(A.retired a).',
        'Proof. intros[HQ HS];exact(ordered_separation(A.retired a)(A.waiting a)HS). Qed.',
        'Record Result:Type:={result_rtl:State;result_ghost:J.JointGhost;result_accounts:A.Accounts}.',
        'Definition Packed:Type:=(J.JointGhost*A.Accounts)%type.',
        'Definition packed_inv pre(ghost:Packed):=OrderedCandidate pre(fst ghost)(snd ghost).',
        'Definition observe ev pre(ghost:Packed):option Packed:=match R.accounted_step ev pre(fst ghost)(snd ghost)0 with',
        ' | None=>None|Some next=>Some(J.joint_step ev pre(fst ghost),next)end.',
        f'Definition replay events pre g a:option Result:=match Shadow.run {p} Packed observe events pre(g,a)with',
        ' | None=>None|Some(post,(finalg,finala))=>Some(Build_Result post finalg finala)end.',
        'Definition Allowed ev pre:Prop:=',
        ' J.EventAllowed ev /\\Q.ClockAllowed ev /\\',
        f' (exists seed0,CombLFP {p} seed0 pre) /\\(exists seed,CombLFP {p} seed{sample}) /\\',
        f' norm 1(read_signal{sample}{reset})<>0%Z.',
        f'Definition Ready:=Shadow.Ready {p} Allowed.',
        'Lemma observe_preserves ev pre ghost:Allowed ev pre ->packed_inv pre ghost ->exists next,',
        f' observe ev pre ghost=Some next /\\packed_inv{post}next.',
        'Proof. destruct ghost as[g a];intros[HJ[HE[[seed0 HL0][[seed HL]Hreset]]]]HI;',
        ' destruct(ordered_normal_phase seed0 seed ev pre g a HJ HE HL0 HL Hreset HI)as[next[HS Hnext]].',
        ' exists(J.joint_step ev pre g,next);split;[unfold observe;cbn[fst snd];now rewrite HS|exact Hnext]. Qed.',
        'Theorem replay_restores events:forall pre g a,Ready events pre ->OrderedCandidate pre g a ->',
        ' exists result,replay events pre g a=Some result /\\OrderedCandidate(result_rtl result)(result_ghost result)(result_accounts result).',
        'Proof. intros pre g a HR HI;',
        f' destruct(Shadow.run_preserves {p} Packed observe Allowed packed_inv observe_preserves events pre(g,a)HR HI)',
        ' as[post[[finalg finala][HS Hnext]]].',
        ' exists(Build_Result post finalg finala);split;[unfold replay;now rewrite HS|exact Hnext]. Qed.',
        'Theorem replay_erases events:forall pre g a result,replay events pre g a=Some result ->',
        f' result_rtl result=phase_run {p} events pre.',
        'Proof. intros pre g a result HS;unfold replay in HS;',
        f' destruct(Shadow.run {p} Packed observe events pre(g,a))as[[post[finalg finala]]|]eqn:HR;[|discriminate].',
        ' inversion HS;subst result;',
        f' exact(Shadow.run_erases {p} Packed observe events pre(g,a)post(finalg,finala)HR). Qed.',
        f'Theorem replay_initial events:Ready events(initialize {p} []) ->exists result,',
        f' replay events(initialize {p} [])J.joint_empty A.empty=Some result /\\',
        f' result_rtl result=phase_run {p} events(initialize {p} []) /\\',
        ' OrderedCandidate(result_rtl result)(result_ghost result)(result_accounts result).',
        'Proof. intro HR;destruct(replay_restores events _ _ _ HR ordered_initialize)as[result[HS HI]].',
        ' exists result;split;[exact HS|]. split;[exact(replay_erases events _ _ _ result HS)|exact HI]. Qed.']
    exports=['candidate_history_range','ordered_initialize','ordered_normal_phase','retired_older_than_waiting','replay_restores','replay_erases','replay_initial']
    lines+=['Print Assumptions '+name+'.'for name in exports]
    return dict(**data,ast_sha256=ast['source_sha256'],coq_load_paths=paths,provider_hash=nr['object_sha256'],audited_exports=len(exports)),'\n'.join(lines)+'\n'


def check(ast_path,ast_module,provider,normal_provider,output,timeout=1200):
    if not 0<timeout<=1200:raise ValueError('native budget must be <=1200 seconds')
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    try:data,source=render(ast_path,ast_module,provider,normal_provider)
    except ValueError as error:
        result=dict(accepted=False,native_started=False,residual=str(error),old_inv_read=False,old_pending_read=False,
            old_cpu_proofs_used=False,capture_age_preservation_proved=False,isa_instruction_order_proved=False,
            original_runtime_ready_proved=False,global_inv_proved=False,itree_refinement_proved=False)
        (output/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result
    path=output/'CaptureAge.v';path.write_text(source);(output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    flags=list(rtl.framework.FLAGS)
    for binding in data['coq_load_paths']:flags+=['-R',binding['directory'],binding['namespace']]
    for folder,namespace in [('capture-birth','GeneratedCaptureBirth'),('coverage','GeneratedRecipeCoverage'),('value','GeneratedConnectedProjections'),('copies','GeneratedMetadataCopies'),('joint','GeneratedCoveredFields'),('joint-history','GeneratedJointHistory'),('stall-flush','GeneratedStallFlush'),('source-hold','GeneratedSourceHold'),('source-transfer','GeneratedSourceTransfer'),('pipeline-transfer','GeneratedPipelineTransfer'),('retirement-cut','GeneratedRetirementCandidate'),('retirement-phase','GeneratedRetirementPhase'),('clock-frame','GeneratedClockFrame')]:
        flags+=['-R',str((Path(provider)/folder).resolve()),namespace]
    flags+=['-R',str(Path(normal_provider).resolve()),'GeneratedRisingQueue','-R',str(output.resolve()),'GeneratedCaptureAge']
    start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',timeout)
    result=dict(accepted=False,native_started=True,scope='actual captured retirement/waiting age and normal history induction under explicit runtime readiness; not ISA age or infinite refinement',
        coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        old_inv_read=False,old_pending_read=False,old_cpu_proofs_used=False,capture_age_preservation_proved=False,
        isa_instruction_order_proved=False,original_runtime_ready_proved=False,global_inv_proved=False,itree_refinement_proved=False)
    if c.returncode==0:
        closed=c.stdout.count('Closed under the global context')==data['audited_exports']and'Axioms:'not in c.stdout;result['assumptions_closed']=closed
        if closed and time.monotonic()<deadline:
            k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedCaptureAge.CaptureAge'],output/'coqchk.log',deadline-time.monotonic())
            result.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0)
    result['overall_seconds']=time.monotonic()-start
    if result['accepted']:result.update(object_sha256=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest(),capture_age_preservation_proved=True)
    (output/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in ['ast','provider','output']:p.add_argument('--'+name,type=Path,required=True)
    p.add_argument('--normal-provider',type=Path);p.add_argument('--ast-module',required=True);a=p.parse_args()
    result=check(a.ast,a.ast_module,a.provider,a.normal_provider or a.provider/'normal-phase',a.output)
    print(json.dumps(result,indent=2));raise SystemExit(0 if result['accepted']else 1)
