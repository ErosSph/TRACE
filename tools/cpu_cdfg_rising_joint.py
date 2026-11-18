"""Join real rising prefill, valid admission and stall under the same R.

The chosen ISA class is still ADD. Actual enable/flush, post validity, idle RF,
queue changes and PC changes are outputs of the proof, not environment facts.
The original program-domain conditions and reference model are unchanged.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time

import cpu_cdfg_prefill_frontier as prefill
from cpu_add_admission_ledger import checked_provider
from cpu_certificate_acceptance import run_stage, ALLOWED_AXIOMS
from check_reference_value_rules import audit_all_exports


def gate_shape(rtl,cone):
    """Recognize a one-bit AND through exact one-bit aliases/casts.

    This proposes a template only. The native original-phase equation remains
    the acceptance condition; unknown operators or widths are not ignored.
    """
    by={node['root']:node for node in cone['nodes']}
    def visit(term,seen):
        if term.name=='EVar'and term.args[0].name=='1':
            root=int(term.args[1].name)
            if root not in by:return root
            if root in seen:raise ValueError('cyclic validity gate aliases')
            if by[root]['width']!=1:raise ValueError('validity gate alias width mismatch')
            return visit(rtl.Parser(by[root]['expression']).complete(),seen|{root})
        if term.name=='EExtend'and term.args[0].name=='1'and term.args[1].name=='false':
            return visit(term.args[2],seen)
        if term.name=='EBinary'and[term.args[i].name for i in [0,1]]==['1','BAnd']:
            return ['and',visit(term.args[2],seen),visit(term.args[3],seen)]
        raise ValueError('unsupported actual validity gate operator or width')
    return visit(rtl.Term('EVar',(rtl.Term('1'),rtl.Term(str(cone['root'])))),set())


def discover(c,raw,profile,graph):
    plan=prefill.bubble.discover(c,raw,profile,graph);pc=prefill.bubble.invalid.fetch.pc
    root=plan['pc_plan']['valid']
    found=pc.scalar.scalar.analyze(raw,{root})
    writers=[(p,nb)for p,nb in found['analysis']['plans']if root in p['writers']]
    if found['residuals']or len(writers)!=1:raise ValueError('one actual head validity update required')
    _,nb=writers[0]
    e=pc.scalar.compile_expression(pc.scalar.slices.slice_plan(nb,root),root,1,
        pc.rtl.Term('EVar',(pc.rtl.Term('1'),pc.rtl.Term(str(root)))))
    reset=plan['pc_plan']['timing']['head_reset']['source']
    if e is None:raise ValueError('unsupported actual head validity expression')
    if(e.name!='ECond'or pc.rtl.render(e.args[1])!=f'(EVar 1 {reset})'
        or e.args[2].name!='EVar'or e.args[2].args[0].name!='1'
        or pc.rtl.render(e.args[3])!='(EConst 1 0)'):
        raise ValueError('unsupported actual normal head valid update')
    source=int(e.args[2].args[1].name)
    cone=pc.admission.fetch.cdfg.cone.cone(raw,1,source)
    symbols=pc.unique_symbols(graph)
    query=pc.admission.fetch.cdfg.backward_slice(graph,symbols[source]['path'])
    cuts=pc.agree_open_cone(graph,query,cone)
    expected={(1,plan['pair']['valid_root']),(1,plan['enable_root'])}
    if {(b['width'],b['root'])for b in cone['boundaries']}!=expected:
        raise ValueError('head validity must depend on the same source validity and real enable')
    shape=gate_shape(pc.rtl,cone)
    if shape!=['and',plan['pair']['valid_root'],plan['enable_root']]:
        raise ValueError('unsupported source-valid/enable gate ordering')
    plan.update(valid_gate=dict(root=root,input=source,scalar=pc.rtl.render(e),cone=cone,
        query=query,open_cuts=cuts,shape=shape,not_a_replacement_evaluator=True))
    return plan


def render(c,raw,profile,plan):
    p,am=profile['ast']['program'],raw['module'];pair=plan['pair'];head=plan['pc_plan']
    h='GeneratedCapturedHistoryBoot.CapturedHistoryBoot';cap=h+'.C';aq='GeneratedAdmissionQueue.AdmissionQueue'
    q='GeneratedPhasePendingCommit.PhasePendingCommit';b=aq+'.N.B'
    pa='GeneratedPCAdmission.PCAdmission';fa='GeneratedFetchAdmission.FetchAdmission'
    pf='GeneratedPrefillFrontier.PrefillFrontier';ps='GeneratedPCStep.PCStep'
    ds='GeneratedDerivedSources.DerivedSources';l='GeneratedAdmissionLedger.AdmissionLedger'
    o='GeneratedOperandResultJoint.OperandResultJoint';wr='GeneratedWritebackRF.WritebackRF'
    af='GeneratedAdmissionFrontier.AdmissionFrontier';f='GeneratedFetchReference.FetchReference'
    r='GeneratedAdmissionReference.AdmissionReference'
    cat='GeneratedDependencyCatalog.Catalog.actual_catalog';cert='GeneratedBoundedPhase.Phase.actual_certificate'
    packed=f'({h}.boot_history image events)';pre=f'(phase_run {p} events({h}.F.boot image))'
    sample=f'(phase_driven_state {p} ev pre)';post=f'(PhaseSemantics {p} ev pre)'
    after=f'({cap}.advance_capture_fields ev pre {packed} tt)'
    rf=json.loads((Path(c['normal_write'])/'plan.json').read_text())['rf']
    match=f'process_matches_states pre {sample}{am}.{head["head_process"]}=true'
    normal=f'norm 1(read_signal {sample}{head["timing"]["head_reset"]["source"]}%nat)=1%Z'
    srcvalid=f'norm 1(read_signal pre {pair["valid_root"]}%nat)'
    postvalid=f'norm 1(read_signal {post}{head["valid"]}%nat)'
    enable=f'norm 1(read_signal {sample}{plan["enable_root"]}%nat)'
    decision=f'(phase_decision {p} {am}.{pair["process"]} {pair["carrier"]}%nat {b}.root_{pair["carrier"]}_expression {b}.root_{pair["valid_root"]}_expression ev pre)'
    source=f'''From Coq Require Import List ZArith Bool Lia.
Require Import {c['ast_module']} Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVScalarHistory
 Lang.ExtendedSVScalarExpression Lang.ExtendedSVCaptureBirth Lang.ExtendedSVCapturedPending Lang.ExtendedSVInstructionOrigin
 Lang.ExtendedSVPackedROM Lang.ExtendedSVBootstrap Lang.ExtendedSVBoundedCatalogPhase Lang.ExtendedSVStallFlush
 Ex.External.CPUGeneratedJointTemplate Ex.External.CPUOriginalISAReference Ex.External.CPUReferenceLedgerExtension
 Ex.RvCore.FormalSpec coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte
 GeneratedPrefillFrontier.PrefillFrontier GeneratedAdmissionFrontier.AdmissionFrontier GeneratedWritebackRF.WritebackRF.
Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVScalarHistory ExtendedSVScalarExpression ExtendedSVCaptureBirth
 ExtendedSVCapturedPending ExtendedSVInstructionOrigin ExtendedSVBootstrap ExtendedSVBoundedCatalogPhase CPUGeneratedJointTemplate CPUReferenceLedgerExtension.
Local Open Scope Z_scope.
Local Opaque {p} PhaseSemantics phase_run {cat} {cert}.
Theorem actual_normal_rising_interfaces image events ev:
 let pre:={pre}in
 Forall {h}.W.Environment events ->{h}.W.Environment ev ->{match} ->{normal} ->
 process_matches_states pre {sample}{am}.{pair['process']}=true /\\
 process_matches_states pre {sample}{am}.{head['process']}=true /\\
 norm 1(read_signal {sample}{plan['chains']['reset']['source']}%nat)=1%Z /\\
 norm 1(read_signal {sample}{head['reset']}%nat)=1%Z /\\
 process_matches_states pre {sample}{am}.{rf['process']}=false.
Proof. intros pre HE HEv HM HR.
 destruct({q}.E.runtime_evidence image events HE)as[HS[seed0 HL0]];fold pre in HS,HL0.
 destruct(GeneratedCapturedReads.CapturedReadAddresses.sample_evidence image events ev HE HEv)as[seed HL];fold pre in HL.
 pose proof(candidate_shape {p} {cat} {cert} _(input_shape {p} {cat} ev pre(proj1 HEv)HS))as HSS.
 split;[exact(eq_trans({fa}.same_fetch_match seed0 seed pre {sample} HL0 HS HL HSS)HM)|].
 split;[exact(eq_trans({pa}.same_process_match seed0 seed pre {sample} HL0 HS HL HSS)HM)|].
 split;[exact(eq_trans({fa}.reset_wire seed _ HL)(eq_trans(eq_sym({pa}.head_reset_normalized seed _ HL))HR))|].
 split;[exact(eq_trans({pa}.pc_reset_normalized seed _ HL)(eq_trans(eq_sym({pa}.head_reset_normalized seed _ HL))HR))|].
 assert(HRG:Z.eqb(eval_expr {sample}(EVar 1 {rf['reset']}%nat))0%Z=false).
 {{ change(Z.eqb(norm 1(read_signal {sample}{rf['reset']}%nat))0%Z=false).
    rewrite({q}.E.rf_reset_alias seed _ HL),<-({q}.E.pipe_reset_alias seed _ HL),HR;reflexivity. }}
 destruct(process_matches_states pre {sample}{am}.{rf['process']})eqn:HF;[|reflexivity].
 pose proof({q}.E.actual_rf_write_excludes_capture image events ev HE HEv HRG HF)as HX;fold pre in HX;congruence. Qed.
Theorem actual_normal_rising_valid image events ev:
 let pre:={pre}in
 Forall {h}.W.Environment events ->{h}.W.Environment ev ->{match} ->{normal} ->
 {postvalid}=norm 1(Z.land ({srcvalid}) ({enable})).
Proof. intros pre HE HEv HM HR.
 destruct(GeneratedCapturedReads.CapturedReadAddresses.sample_evidence image events ev HE HEv)as[seed HL];fold pre in HL.
 rewrite(history_phase_projection _ _ _ _ _ {cap}.V.root_{head['valid']}_valid_certificate ev pre
  ({aq}.internal_event ev {head['valid']}%nat HEv ltac:(lia))),HM,
  ({ds}.expanded_valid seed {sample} HL).
 unfold {cap}.V.coverage_0_expanded;cbn[eval_expr];rewrite HR;cbn[Z.eqb];repeat rewrite norm_idempotent.
 rewrite(sampled_root_preserved {p} ev pre {pair['valid_root']}%nat
  (history_comb_frame _ _ _ _ _ {b}.root_{pair['valid_root']}_birth_certificate)
  ({aq}.internal_event ev {pair['valid_root']}%nat HEv ltac:(lia)));reflexivity. Qed.
Theorem actual_stall_facts image events ev:
 let pre:={pre}in
 Forall {h}.W.Environment events ->{h}.W.Environment ev ->{match} ->{normal} ->
 {srcvalid}=1%Z ->{postvalid}=0%Z ->
 {enable}=0%Z /\\{aq}.admitted ev pre {packed}=[] /\\
 serial(fst {after})=serial(fst {packed}) /\\
 process_matches_states pre {sample}{am}.{rf['process']}=false /\\
 norm 32(read_signal {post}{head['pc']}%nat)=norm 32(read_signal pre {head['pc']}%nat) /\\
 {q}.actual_pending {post}{after}={q}.actual_pending pre {packed}.
Proof. intros pre HE HEv HM HR HV HInvalid.
 destruct(GeneratedCapturedReads.CapturedReadAddresses.sample_evidence image events ev HE HEv)as[seed HL];fold pre in HL.
 pose proof(actual_normal_rising_valid image events ev HE HEv HM HR)as HGate;fold pre in HGate.
 assert(HEnable:{enable}=0%Z).
 {{ destruct(ExtendedSVStallFlush.one_bit_cases {sample}{plan['enable_root']}%nat)as[HZ|HZ];[exact HZ|].
    rewrite HInvalid,HV,HZ in HGate;discriminate. }}
 destruct(actual_normal_rising_interfaces image events ev HE HEv HM HR)as[HF[HP[HFR[HPR HIdle]]]];fold pre in HF,HP,HFR,HPR,HIdle.
 assert(HNoBirth:NewTokens {decision}(serial(fst {packed})){sample}{b}.capture_0_pc=[] /\\
   next_serial {decision}(serial(fst {packed}))=serial(fst {packed})).
 {{ unfold phase_decision;rewrite HF;unfold decide,{b}.root_{pair['carrier']}_expression,{b}.root_{pair['valid_root']}_expression.
    cbn[eval_expr copy_source];repeat rewrite norm_idempotent.
    rewrite HFR,({fa}.enable_wire seed _ HL),HEnable.
    repeat first[progress cbn[Z.eqb Nat.eqb]|progress rewrite norm_idempotent|
      match goal with|-context[if ?flag then _ else _]=>destruct flag eqn:? end];split;reflexivity. }}
 assert(HAdmitted:{aq}.admitted ev pre {packed}=[])by(rewrite {l}.admitted_form;exact(proj1 HNoBirth)).
 assert(HSerial:serial(fst {after})=serial(fst {packed}))by(rewrite {l}.actual_post_serial;exact(proj2 HNoBirth)).
 assert(HPC:norm 32(read_signal {post}{head['pc']}%nat)=norm 32(read_signal pre {head['pc']}%nat)).
 {{ rewrite({ps}.Scalar.root_{head['pc']}_expression_phase ev pre({aq}.internal_event ev {head['pc']}%nat HEv ltac:(lia))),HP.
    unfold {ps}.Scalar.root_{head['pc']}_expression;cbn[eval_expr].
    rewrite HPR,({ps}.enable_wire seed _ HL),HEnable;cbn[Z.eqb];repeat rewrite norm_idempotent.
    rewrite(sampled_root_preserved {p} ev pre {head['pc']}%nat {ps}.Scalar.root_{head['pc']}_comb_frame
      ({aq}.internal_event ev {head['pc']}%nat HEv ltac:(lia)));reflexivity. }}
 pose proof({pf}.actual_normal_rising_queue image events ev HE HEv HM HR)as HQ;fold pre in HQ;rewrite HAdmitted,app_nil_r in HQ.
 exact(conj HEnable(conj HAdmitted(conj HSerial(conj HIdle(conj HPC HQ))))). Qed.
Section OriginalISA.
Context {{word:Interface.word 32}}{{BW:Bitwidth 32}}{{Registers:map.map Z word}}{{Mem:map.map word byte}}
 {{word_ok:word.ok word}}{{registers_ok:map.ok Registers}}{{mem_ok:map.ok Mem}}.
Theorem actual_stall_restores_frontier_joint words i initial retired committed events ev:
 let image:=ExtendedSVPackedROM.pack words in let pre:={pre}in
 Forall {h}.W.Environment events ->{h}.W.Environment ev ->{match} ->{normal} ->
 {srcvalid}=1%Z ->{postvalid}=0%Z ->
 {af}.FrontierJoint words i initial retired committed pre {packed} ->
 {af}.FrontierJoint words i initial retired committed {post}{after}.
Proof. intros image pre HE HEv HM HR HV HInvalid[HCurrent[frontier[HChain[HF HNext]]]].
 destruct(actual_stall_facts image events ev HE HEv HM HR HV HInvalid)as[HEna[HA[HSerial[HIdle[HPC HQ]]]]];fold pre in HIdle,HPC,HQ,HSerial.
 destruct HCurrent as[HCurrent HRange];destruct HCurrent as[HData[other HOther]].
 destruct HData as[HN[[HCommitted[HRF HResults]]HOperands]].
 pose proof({o}.actual_result_phase_from_joint {f}.recorded_pc initial retired({q}.actual_pending pre {packed})image events ev
   HE HEv(conj HN(conj HResults HOperands)))as HResultsPost;fold pre in HResultsPost.
 pose proof({wr}.actual_no_write_preserves_RF image events ev committed HEv(or_introl HIdle)HRF)as HRFPost;fold pre in HRFPost.
 assert(HDataOld:{o}.RFJoint {f}.recorded_pc initial retired({q}.actual_pending pre {packed})committed {post}{after}).
 {{ split;[exact HN|];split;[exact(conj HCommitted(conj HRFPost HResultsPost))|].
    intro HBad;exfalso;exact(HBad HInvalid). }}
 assert(HDataPost:{o}.RFJoint {f}.recorded_pc initial retired({q}.actual_pending {post}{after})committed {post}{after}).
 {{ exact(eq_rect _ (fun pending=>{o}.RFJoint {f}.recorded_pc initial retired pending committed {post}{after})HDataOld _ (eq_sym HQ)). }}
 assert(HChainPost:EffectChain(CPUOriginalISAReference.instruction_effect {f}.recorded_pc token_word)committed({q}.actual_pending {post}{after})frontier).
 {{ exact(eq_rect _ (fun pending=>EffectChain(CPUOriginalISAReference.instruction_effect {f}.recorded_pc token_word)committed pending frontier)HChain _ (eq_sym HQ)). }}
 assert(HRangePost:{l}.LedgerRange {post}{after}retired).
 {{ unfold {l}.LedgerRange;rewrite HSerial,HQ;exact HRange. }}
 split;[exact(conj(conj HDataPost(ex_intro _ frontier HChainPost))HRangePost)|].
 exists frontier;split;[exact HChainPost|];split;[|exact HNext].
 destruct HF as[HPCOld[HAddress HImage]];exact(conj(eq_trans HPC HPCOld)(conj HAddress HImage)). Qed.
Theorem actual_normal_rising_restores_frontier_joint words i initial retired committed events ev rd rs1 rs2:
 let image:=ExtendedSVPackedROM.pack words in let pre:={pre}in
 Forall(Word 32)words ->Z.of_nat(length words)<=2^30 ->(i<{plan['capacity']})%nat ->Z.of_nat i<2^25 ->32*Z.of_nat i<2^Z.of_nat {plan['offset_width']} ->
 Forall {h}.W.Environment events ->{h}.W.Environment ev ->{match} ->{normal} ->
 ({srcvalid}<>0%Z ->forall token,current(fst {packed})=Some token ->exists d s1 s2,
   Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Add d s1 s2)) ->
 {af}.FrontierJoint words i initial retired committed pre {packed} ->
 Decode.decode Decode.RV32I({f}.R.lookup image(4*Z.of_nat i))=Decode.IInstruction(Decode.Add rd rs1 rs2) ->
 {af}.FrontierJoint words(if Z.eqb ({enable}) 0%Z then i else S i)initial retired committed {post}{after}.
Proof. intros image pre HW HLen HC HI HO HE HEv HM HR HClass HJ HD.
 destruct(ExtendedSVStallFlush.one_bit_cases pre {pair['valid_root']}%nat)as[HV|HV].
 - destruct({pf}.actual_prefill_controls image events ev HE HEv HV)as[HS[HF HEnable]];fold pre in HEnable.
   rewrite HEnable;exact({pf}.actual_prefill_restores_frontier_joint words i initial retired committed events ev rd rs1 rs2
     HW HLen HC HI HO HE HEv HM HR HV HJ HD).
 - destruct(ExtendedSVStallFlush.one_bit_cases {post}{head['valid']}%nat)as[HInvalid|HValid].
   + destruct(actual_stall_facts image events ev HE HEv HM HR HV HInvalid)as[HEnable _];fold pre in HEnable.
     rewrite HEnable;exact(actual_stall_restores_frontier_joint words i initial retired committed events ev HE HEv HM HR HV HInvalid HJ).
   + assert(HVNonzero:{srcvalid}<>0%Z)by congruence.
     assert(HPostNonzero:{postvalid}<>0%Z)by congruence.
     assert(HEnable:{enable}=1%Z).
     {{ destruct(ExtendedSVStallFlush.one_bit_cases {sample}{plan['enable_root']}%nat)as[HZ|HZ];[|exact HZ].
        pose proof(actual_normal_rising_valid image events ev HE HEv HM HR)as HG;fold pre in HG.
        rewrite HValid,HV,HZ in HG;discriminate. }}
     rewrite HEnable;exact({af}.actual_admission_restores_frontier_joint words i initial retired committed events ev rd rs1 rs2
       HW HLen HC HI HO HE HEv(HClass HVNonzero)HJ HD HM HPostNonzero). Qed.
End OriginalISA.
Goal True. idtac "RISING_JOINT_AUDIT". exact I. Qed.
Print Assumptions actual_normal_rising_interfaces.
Print Assumptions actual_normal_rising_valid.
Print Assumptions actual_stall_facts.
Print Assumptions actual_stall_restores_frontier_joint.
Print Assumptions actual_normal_rising_restores_frontier_joint.
'''
    return source


def check(c,output):
    out=Path(output);out.mkdir(parents=True,exist_ok=False);pc=prefill.bubble.invalid.fetch.pc
    graph=pc.admission.fetch.cdfg.checked_graph(c['graph'],c['ast'],out/'replayed')
    raw,profile,_=pc.admission.fetch.cdfg.raw_binding(c['ast'],c['ast_module']);plan=discover(c,raw,profile,graph)
    paths=checked_provider(c['prefill_frontier'],'PrefillFrontier.v',raw['source_sha256'],['actual_prefill_restores_same_frontier_joint'])
    paths +=[dict(namespace='GeneratedPrefillFrontier',directory=str(Path(c['prefill_frontier']).resolve()))]
    source=render(c,raw,profile,plan);file=out/'RisingJoint.v';file.write_text(source)
    for key,value in [('plan',plan),('providers',paths)]:
        (out/(key+'.json')).write_text(json.dumps(value,indent=2)+'\n')
    flags=list(pc.rtl.framework.FLAGS)
    for row in paths:flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(out.resolve()),'GeneratedRisingJoint'];start=time.monotonic()
    cc,timed=run_stage(['/usr/bin/time','-v','-o',str((out/'coqc.resources').resolve()),str(pc.rtl.ROOT/'_opam/bin/coqc'),
        '-time',*flags,str(file.resolve())],out/'coqc.log',1200)
    report=dict(accepted=False,coqc_exit=cc.returncode,coqc_timed_out=timed,source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        ast_sha256=raw['source_sha256'],graph_sha256=hashlib.sha256(Path(c['graph']).read_bytes()).hexdigest(),old_inv_read=False,
        all_normal_ADD_rising_branches_preserve_same_joint=False,caller_post_valid_or_controller_correctness_required=False,
        original_instruction_class_and_address_domain_still_required=True,full_R_generated=False,full_cycle_preservation_proved=False,
        itree_refinement_proved=False,external_llm_api_calls=0)
    if cc.returncode==0:
        axioms=audit_all_exports(cc.stdout.split('RISING_JOINT_AUDIT')[-1],5)
        baseline=set(json.loads((Path(c['prefill_frontier'])/'report.json').read_text())['baseline_assumptions'])
        audit=not(axioms-baseline)and not(axioms-ALLOWED_AXIOMS)
        kk,timed=run_stage(['/usr/bin/time','-v','-o',str((out/'coqchk.resources').resolve()),str(pc.rtl.ROOT/'_opam/bin/coqchk'),
            '-silent',*flags,'-norec','GeneratedRisingJoint.RisingJoint'],out/'coqchk.log',max(.1,1200-(time.monotonic()-start)))
        ok=audit and kk.returncode==0
        report.update(accepted=ok,coqchk_exit=kk.returncode,coqchk_timed_out=timed,assumptions_audit_passed=audit,
            isa_assumptions=sorted(axioms),baseline_assumptions=sorted(baseline),all_normal_ADD_rising_branches_preserve_same_joint=ok)
    report['seconds']=time.monotonic()-start
    if report['accepted']:report['object_sha256']=hashlib.sha256(file.with_suffix('.vo').read_bytes()).hexdigest()
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for key in ['inputs','output']:p.add_argument('--'+key,required=True)
    a=p.parse_args()
    try:r=check(json.loads(Path(a.inputs).read_text()),a.output)
    except Exception as exc:
        out=Path(a.output)
        if out.is_dir()and not(out/'report.json').exists():
            (out/'report.json').write_text(json.dumps(dict(accepted=False,stage='preflight',error=str(exc),cli_exit=1),indent=2)+'\n')
        raise
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
