"""Synthesize an ordered wire-cone certificate and restore falling QueueCandidate.

The post clock is derived from actual comb rounds, not post-state LFP assumed
as another premise. No old CPU invariant or manually specified clock IDs enter.
"""
import argparse,hashlib,json,time
from pathlib import Path
import cpu_pending_retirement_phase as phase
from cpu_certificate_acceptance import run_stage
origin=phase.origin;fields=phase.fields;rtl=phase.rtl


def compile_trace(ast,input_root,target,dependencies):
    if any(input_root in p['writers']for p in ast['processes']):raise ValueError('clock input has an RTL writer')
    known=[input_root];steps=[]
    for p in ast['processes']:
        if p['kind']!='Combinational':continue
        b=p['body'];copy=None
        if b.name=='SAssign'and b.args[0].name=='false'and b.args[1].name=='EVar'and b.args[2].name=='LVar':
            rhs,lhs=b.args[1:]
            if rhs.args[0].name==lhs.args[0].name=='1':
                src=int(rhs.args[1].name);dst=int(lhs.args[1].name)
                if dst in dependencies and src in known and dst!=input_root:copy=(dst,src)
        item=dict(process=p['name'],before=list(known))
        if copy is not None:
            dst,src=copy;item.update(kind='copy',dst=dst,src=src);known=[dst]+known
        elif any(root in p['writers']for root in [input_root]+known):
            raise ValueError('known clock dependency overwritten outside checked copy grammar')
        else:item['kind']='frame'
        steps.append(item)
    if target not in known:raise ValueError('clock not established in one actual ordered comb round')
    return dict(input=input_root,target=target,dependencies=sorted(dependencies),steps=steps,final_known=known)


def discover(ast):
    pd=phase.discover(ast);rows=[];residuals=[]
    for row in pd['phases']:
        route=row['base']['routes']['source_clock'];target=row['base']['source_clock']
        try:trace=compile_trace(ast,route['terminal'],target,{e['root']for e in route['edges']})
        except ValueError as error:residuals.append(str(error));continue
        rows.append(dict(phase=row,trace=trace))
    return dict(clock_frames=rows,residuals=residuals,old_inv_read=False,old_pending_read=False,old_cpu_proofs_used=False,
        post_lfp_hypothesis_required=False,full_cycle_preservation_proved=False,global_inv_proved=False,itree_refinement_proved=False)


def render(ast_path,ast_module,provider):
    provider=Path(provider);ast,profile,paths=origin.raw_binding(ast_path,ast_module);data=discover(ast)
    if len(data['clock_frames'])!=1:raise ValueError('one checked raw clock cone required; unsupported order is not a fixed-point assumption')
    qd,qs=phase.render(ast_path,ast_module,provider)
    qr=fields.verify(provider/'retirement-phase','RetirementPhase.v',qd,qs)
    row=data['clock_frames'][0];trace=row['trace'];input_root=trace['input'];target=trace['target'];p=profile['ast']['program']
    def member(root,items):
        proof='or_introl eq_refl'
        for _ in range(items.index(root)):proof='or_intror('+proof+')'
        return '('+proof+')'
    order='['+';'.join(ast['module']+'.'+x['process']for x in trace['steps'])+']'
    lines=['From Coq Require Import List ZArith Bool Lia.',f'Require Import {ast_module}.',
        'Require Import Lang.ExtendedSV Lang.ExtendedSVConstantRoot Lang.ExtendedSVRootProjection Lang.ExtendedSVWireClockFrame GeneratedRetirementPhase.RetirementPhase.',
        'Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVWireClockFrame.',
        'Module Q:=GeneratedRetirementPhase.RetirementPhase. Module J:=Q.J. Module A:=Q.A.',
        f'Definition wire_order:list Process:={order}.',
        f'Lemma wire_order_checked:filter is_comb(processes {p})=wire_order.',
        'Proof. vm_compute;reflexivity. Qed.',
        f'Lemma statement_positive:(0<statement_fuel {p})%nat.',
        'Proof. vm_compute;lia. Qed.',
        f'Lemma lfp_positive:(0<lfp_fuel {p})%nat.',
        'Proof. vm_compute;lia. Qed.',
        f'Lemma input_unwritten:ExtendedSVConstantRoot.roots_unwrittenb {input_root}(processes {p})=true.',
        'Proof. vm_compute;reflexivity. Qed.',f'Local Opaque {p}.',
        f'Lemma checked_wire_trace:WireTrace {p} {input_root}[{input_root}]wire_order {phase.r.joint.roots_coq(trace["final_known"])}.',
        'Proof. unfold wire_order.']
    for step in trace['steps']:
        if step['kind']=='copy':
            lines += [f' eapply TraceCopy with(dst:={step["dst"]})(src:={step["src"]});',
                f' [reflexivity|exact {member(step["src"],step["before"])}|intro H;discriminate|].']
        else:lines+=[' eapply TraceFrame;[vm_compute;reflexivity|].']
    lines+=[' constructor. Qed.',
        'Theorem clock_round_norm s:',
        f' norm 1(read_signal(comb_round {p} s){target})=norm 1(read_signal s {input_root}).',
        f'Proof. assert(HK:Known {input_root}[{input_root}]s).',
        ' { intros root[H|H];[now subst root|contradiction]. }',
        f' pose proof(trace_sound {p} {input_root}[{input_root}]wire_order {phase.r.joint.roots_coq(trace["final_known"])}',
        ' checked_wire_trace statement_positive s HK)as HP;unfold comb_round;rewrite wire_order_checked;',
        f' etransitivity;[exact(HP {target}{member(target,trace["final_known"])})|].',
        ' rewrite <-wire_order_checked;',
        f' change(norm 1(read_signal(comb_round {p} s){input_root})=norm 1(read_signal s {input_root}));',
        f' rewrite(comb_round_preserves_unwritten_root {p} {input_root}(all_unwritten_comb {p} {input_root} input_unwritten)s);reflexivity. Qed.',
        'Theorem clock_phase_norm ev pre:',
        f' norm 1(read_signal(PhaseSemantics {p} ev pre){target})=',
        f' norm 1(read_signal(phase_driven_state {p} ev pre){target}).',
        f'Proof. exact(phase_clock_stable {p} {input_root} {target} input_unwritten clock_round_norm lfp_positive ev pre). Qed.',
        'Theorem falling_post_low ev pre:Q.Falling ev pre=true ->',
        f' norm 1(read_signal(PhaseSemantics {p} ev pre){target})=0%Z.',
        'Proof. intro HF;unfold Q.Falling,edge_fires in HF;apply andb_true_iff in HF as[HO HN];',
        ' apply Z.eqb_eq in HN;rewrite clock_phase_norm,HN;reflexivity. Qed.',
        'Theorem falling_restores_queue_candidate seed0 seed ev pre g a:J.EventAllowed ev ->Q.ClockAllowed ev ->',
        f' CombLFP {p} seed0 pre ->CombLFP {p} seed(phase_driven_state {p} ev pre) ->',
        f' norm 1(read_signal(phase_driven_state {p} ev pre){row["phase"]["base"]["hold"]["reset"]})<>0%Z ->',
        ' Q.Falling ev pre=true ->Q.QueueCandidate pre g a ->exists next,',
        ' Q.R.accounted_step ev pre g a 0=Some next /\\',
        f' Q.QueueCandidate(PhaseSemantics {p} ev pre)(J.joint_step ev pre g)next /\\',
        ' A.retired next=A.retired a++Q.retire_view pre g /\\A.cancelled next=A.cancelled a.',
        'Proof. intros HJ HE HL0 HL HR HF HI;',
        ' destruct(Q.actual_falling_accounting seed0 seed ev pre g a HJ HE HL0 HL HR HF HI)',
        ' as[next[HS[HA[HP[HW[HQ[Hret Hcancel]]]]]]].',
        ' exists next;split;[exact HS|]. split.',
        ' - split;[exact HP|]. split;[exact HA|]. split;[exact HW|].',
        '   unfold Q.waiting_view;rewrite(falling_post_low ev pre HF);exact HQ.',
        ' - split;assumption. Qed.']
    exports=['checked_wire_trace','clock_round_norm','clock_phase_norm','falling_post_low','falling_restores_queue_candidate']
    for name in exports:lines+=['Print Assumptions '+name+'.']
    return dict(**data,ast_sha256=ast['source_sha256'],coq_load_paths=paths,provider_hash=qr['object_sha256'],audited_exports=len(exports)),'\n'.join(lines)+'\n'


def check(ast_path,ast_module,provider,output,timeout=1200):
    if not 0<timeout<=1200:raise ValueError('native budget must be <=1200 seconds')
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    try:data,source=render(ast_path,ast_module,provider)
    except ValueError as error:
        result=dict(accepted=False,native_started=False,residual=str(error),old_inv_read=False,global_inv_proved=False,itree_refinement_proved=False)
        (output/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result
    path=output/'ClockFrame.v';path.write_text(source);(output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    flags=list(rtl.framework.FLAGS)
    for binding in data['coq_load_paths']:flags+=['-R',binding['directory'],binding['namespace']]
    for folder,namespace in [('capture-birth','GeneratedCaptureBirth'),('coverage','GeneratedRecipeCoverage'),('value','GeneratedConnectedProjections'),('copies','GeneratedMetadataCopies'),('joint','GeneratedCoveredFields'),('joint-history','GeneratedJointHistory'),('stall-flush','GeneratedStallFlush'),('source-hold','GeneratedSourceHold'),('source-transfer','GeneratedSourceTransfer'),('pipeline-transfer','GeneratedPipelineTransfer'),('retirement-cut','GeneratedRetirementCandidate'),('retirement-phase','GeneratedRetirementPhase')]:
        flags+=['-R',str((Path(provider)/folder).resolve()),namespace]
    flags+=['-R',str(output.resolve()),'GeneratedClockFrame'];start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',timeout)
    result=dict(accepted=False,native_started=True,scope='actual post-clock frame and same QueueCandidate restoration on normal falling phases only',
        coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest(),old_inv_read=False,
        old_pending_read=False,old_cpu_proofs_used=False,post_lfp_hypothesis_required=False,falling_candidate_restored=False,
        full_cycle_preservation_proved=False,global_inv_proved=False,itree_refinement_proved=False)
    if c.returncode==0:
        closed=c.stdout.count('Closed under the global context')==data['audited_exports']and'Axioms:'not in c.stdout;result['assumptions_closed']=closed
        if closed and time.monotonic()<deadline:
            k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedClockFrame.ClockFrame'],output/'coqchk.log',deadline-time.monotonic())
            result.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0)
    result['overall_seconds']=time.monotonic()-start
    if result['accepted']:result.update(object_sha256=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest(),falling_candidate_restored=True)
    (output/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ['ast','provider','output']:parser.add_argument('--'+name,type=Path,required=True)
    parser.add_argument('--ast-module',required=True);args=parser.parse_args()
    result=check(args.ast,args.ast_module,args.provider,args.output);print(json.dumps(result,indent=2));raise SystemExit(0 if result['accepted']else 1)
