"""Recover the same generated joint relation when the IF/ID slot is empty.

Uses real reset-reachable bubble data, real controller observations, actual
normal rising queue conservation, original ISA admission and unchanged R.
Neither post-EX validity nor controller correctness is a caller assumption.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time

import cpu_cdfg_bubble_control as bubble
from cpu_add_admission_ledger import checked_provider
from cpu_certificate_acceptance import run_stage, ALLOWED_AXIOMS
from check_reference_value_rules import audit_all_exports


def render(c,raw,profile,plan):
    p,am=profile['ast']['program'],raw['module'];pair=plan['pair'];head=plan['pc_plan']
    h='GeneratedCapturedHistoryBoot.CapturedHistoryBoot';cap=h+'.C'
    aq='GeneratedAdmissionQueue.AdmissionQueue';q='GeneratedPhasePendingCommit.PhasePendingCommit'
    pa='GeneratedPCAdmission.PCAdmission';fa='GeneratedFetchAdmission.FetchAdmission'
    inf='GeneratedInvalidFetch.InvalidFetch';bc='GeneratedBubbleControl.BubbleControl'
    l='GeneratedAdmissionLedger.AdmissionLedger';r='GeneratedAdmissionReference.AdmissionReference'
    f='GeneratedFetchReference.FetchReference';af='GeneratedAdmissionFrontier.AdmissionFrontier'
    o='GeneratedOperandResultJoint.OperandResultJoint';wr='GeneratedWritebackRF.WritebackRF'
    cat='GeneratedDependencyCatalog.Catalog.actual_catalog';cert='GeneratedBoundedPhase.Phase.actual_certificate'
    packed=f'({h}.boot_history image events)';pre=f'(phase_run {p} events({h}.F.boot image))'
    sample=f'(phase_driven_state {p} ev pre)';post=f'(PhaseSemantics {p} ev pre)'
    after=f'({cap}.advance_capture_fields ev pre {packed} tt)'
    rf_plan=json.loads((Path(c['normal_write'])/'plan.json').read_text())['rf']
    process=am+'.'+head['head_process'];rf=am+'.'+rf_plan['process']
    normal=f'norm 1(read_signal {sample}{head["timing"]["head_reset"]["source"]}%nat)=1%Z'
    matches=f'process_matches_states pre {sample}{process}=true'
    empty=f'norm 1(read_signal pre {pair["valid_root"]}%nat)=0%Z'
    b=aq+'.N.B'
    decision=f'(phase_decision {p} {am}.{pair["process"]} {pair["carrier"]}%nat {b}.root_{pair["carrier"]}_expression {b}.root_{pair["valid_root"]}_expression ev pre)'
    source=f'''From Coq Require Import List ZArith Bool Lia.
Require Import {c['ast_module']} Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVScalarHistory
 Lang.ExtendedSVScalarExpression Lang.ExtendedSVCaptureBirth Lang.ExtendedSVCapturedPending Lang.ExtendedSVInstructionOrigin
 Lang.ExtendedSVPackedROM Lang.ExtendedSVBootstrap Lang.ExtendedSVBoundedCatalogPhase Lang.ExtendedSVStallFlush
 Ex.External.CPUGeneratedJointTemplate Ex.External.CPUOriginalISAReference Ex.External.CPUReferenceLedgerExtension
 Ex.RvCore.FormalSpec coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte
 GeneratedInvalidFetch.InvalidFetch GeneratedBubbleControl.BubbleControl GeneratedAdmissionFrontier.AdmissionFrontier
 GeneratedWritebackRF.WritebackRF.
Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVScalarHistory ExtendedSVScalarExpression ExtendedSVCaptureBirth
 ExtendedSVCapturedPending ExtendedSVInstructionOrigin ExtendedSVBootstrap ExtendedSVBoundedCatalogPhase
 CPUGeneratedJointTemplate CPUReferenceLedgerExtension.
Local Open Scope Z_scope.
Local Opaque {p} PhaseSemantics {cat} {cert}.
Theorem actual_prefill_controls image events ev:
 let pre:={pre}in
 Forall {h}.W.Environment events ->{h}.W.Environment ev ->{empty} ->
 norm 2(read_signal {sample}{head['chains']['select']['terminal']}%nat)=0%Z /\\
 norm 1(read_signal {sample}{plan['flush_root']}%nat)=0%Z /\\
 norm 1(read_signal {sample}{plan['enable_root']}%nat)=1%Z.
Proof. intros pre HE HEv HV.
 destruct(GeneratedCapturedReads.CapturedReadAddresses.sample_evidence image events ev HE HEv)as[seed HL];fold pre in HL.
 pose proof({inf}.actual_sampled_invalid_word image events ev HE HEv HV)as HWord;fold pre in HWord.
 assert(HValid:norm 1(read_signal {sample}{pair['valid_root']}%nat)=0%Z).
 {{ exact(eq_trans(f_equal(norm 1)(sampled_root_preserved {p} ev pre {pair['valid_root']}%nat
   (history_comb_frame _ _ _ _ _ {b}.root_{pair['valid_root']}_birth_certificate)
   ({aq}.internal_event ev {pair['valid_root']}%nat HEv ltac:(lia))))HV). }}
 exact(conj({bc}.actual_bubble_pcsource seed _ HL HWord HValid)
  (conj({bc}.actual_bubble_flush seed _ HL HWord HValid)({bc}.actual_bubble_enable seed _ HL HWord HValid))). Qed.
Theorem actual_normal_rising_queue image events ev:
 let pre:={pre}in
 Forall {h}.W.Environment events ->{h}.W.Environment ev ->{matches} ->{normal} ->
 {q}.actual_pending {post}{after}={q}.actual_pending pre {packed}++{aq}.admitted ev pre {packed}.
Proof. intros pre HE HEv HM HR.
 destruct({q}.E.runtime_evidence image events HE)as[HS[seed0 HL0]];fold pre in HS,HL0.
 destruct(GeneratedCapturedReads.CapturedReadAddresses.sample_evidence image events ev HE HEv)as[seed HL];fold pre in HL.
 destruct({aq}.actual_events ev HEv)as[HJ HA];pose proof({aq}.actual_clock_words pre HS)as HW.
 assert(HRone:norm 1(read_signal {sample}{plan['chains']['reset']['source']}%nat)=1%Z).
 {{ exact(eq_trans({aq}.N.Q.base_reset_alias seed _ HL)(eq_trans(eq_sym({aq}.N.T.target_reset_alias seed _ HL))HR)). }}
 assert(HNormal:norm 1(read_signal {sample}{plan['chains']['reset']['source']}%nat)<>0%Z)by congruence.
 assert(HRising:{aq}.N.Q.Rising ev pre=true).
 {{ rewrite <-({aq}.N.Q.source_matches_rising ev pre HA HW HNormal),
   <-({aq}.N.Q.node_1_clocks seed0 seed ev pre HA HW HL0 HL);exact HM. }}
 pose proof({aq}.N.rising_waiting_conserved seed0 seed ev pre({aq}.repack {packed})HJ HA HW HL0 HL HNormal HRising)as HQ.
 destruct(catalog_phase_evidence {p} {cat} {cert} ev pre(proj1 HEv)HS)as[HLsample[[seed1 HLpost]HSpost]].
 rewrite <-({aq}.repack_step ev pre {packed})in HQ.
 rewrite <-({aq}.view_agreement seed1 _ _ HSpost HLpost),<-({aq}.view_agreement seed0 _ _ HS HL0)in HQ;exact HQ. Qed.
Theorem actual_prefill_facts image events ev:
 let pre:={pre}in
 Forall {h}.W.Environment events ->{h}.W.Environment ev ->{matches} ->{normal} ->{empty} ->
 {decision}=Accept {pair['word_input']}%nat /\\
 norm 1(read_signal {post}{head['valid']}%nat)=0%Z /\\
 process_matches_states pre {sample}{rf}=false /\\
 norm 32(read_signal {post}{head['pc']}%nat)=norm 32(norm 32(read_signal pre {head['pc']}%nat)+4) /\\
 {q}.actual_pending {post}{after}={q}.actual_pending pre {packed}++{aq}.admitted ev pre {packed}.
Proof. intros pre HE HEv HM HR HV.
 destruct({q}.E.runtime_evidence image events HE)as[HS[seed0 HL0]];fold pre in HS,HL0.
 destruct(GeneratedCapturedReads.CapturedReadAddresses.sample_evidence image events ev HE HEv)as[seed HL];fold pre in HL.
 pose proof(candidate_shape {p} {cat} {cert} _(input_shape {p} {cat} ev pre(proj1 HEv)HS))as HSampleShape.
 destruct(actual_prefill_controls image events ev HE HEv HV)as[HSelect[HFlush HEnable]];fold pre in HSelect,HFlush,HEnable.
 assert(HFetch:process_matches_states pre {sample}{am}.{pair['process']}=true).
 {{ exact(eq_trans({fa}.same_fetch_match seed0 seed pre {sample} HL0 HS HL HSampleShape)HM). }}
 assert(HPC:process_matches_states pre {sample}{am}.{head['process']}=true).
 {{ exact(eq_trans({pa}.same_process_match seed0 seed pre {sample} HL0 HS HL HSampleShape)HM). }}
 assert(HFReset:norm 1(read_signal {sample}{plan['chains']['reset']['source']}%nat)=1%Z).
 {{ exact(eq_trans({fa}.reset_wire seed _ HL)(eq_trans(eq_sym({pa}.head_reset_normalized seed _ HL))HR)). }}
 assert(HPCReset:norm 1(read_signal {sample}{head['reset']}%nat)=1%Z).
 {{ exact(eq_trans({pa}.pc_reset_normalized seed _ HL)(eq_trans(eq_sym({pa}.head_reset_normalized seed _ HL))HR)). }}
 assert(HRG:Z.eqb(eval_expr {sample}(EVar 1 {rf_plan['reset']}%nat))0%Z=false).
 {{ change(Z.eqb(norm 1(read_signal {sample}{rf_plan['reset']}%nat))0%Z=false).
    rewrite({q}.E.rf_reset_alias seed _ HL),<-({q}.E.pipe_reset_alias seed _ HL),HR;reflexivity. }}
 assert(HRF:process_matches_states pre {sample}{rf}=false).
 {{ destruct(process_matches_states pre {sample}{rf})eqn:HF;[|reflexivity].
    pose proof({q}.E.actual_rf_write_excludes_capture image events ev HE HEv HRG HF)as HX;fold pre in HX;congruence. }}
 assert(HPostInvalid:norm 1(read_signal {post}{head['valid']}%nat)=0%Z).
 {{ destruct(ExtendedSVStallFlush.one_bit_cases {post}{head['valid']}%nat)as[HZ|HZ];[exact HZ|].
    assert(HVPost:norm 1(read_signal {post}{head['valid']}%nat)<>0%Z)by congruence.
    pose proof(GeneratedDerivedSources.DerivedSources.admitted_source_valid seed ev pre HEv HL HM HVPost)as HX;contradiction. }}
 split.
 - exact({fa}.normal_capture_decision ev pre HFetch HFReset
    (eq_trans({fa}.flush_wire seed _ HL)HFlush)(eq_trans({fa}.enable_wire seed _ HL)HEnable)).
 - split;[exact HPostInvalid|];split;[exact HRF|];split.
   + exact(GeneratedPCStep.PCStep.actual_sequential_pc_phase seed ev pre
     ({aq}.internal_event ev {head['pc']}%nat HEv ltac:(lia))HL HPC HPCReset HEnable HSelect).
   + exact(actual_normal_rising_queue image events ev HE HEv HM HR). Qed.
Section OriginalISA.
Context {{word:Interface.word 32}}{{BW:Bitwidth 32}}{{Registers:map.map Z word}}{{Mem:map.map word byte}}
 {{word_ok:word.ok word}}{{registers_ok:map.ok Registers}}{{mem_ok:map.ok Mem}}.
Local Open Scope Z_scope.
Theorem actual_prefill_register_data token_pc initial retired committed image events ev:
 let pre:={pre}in
 Forall {h}.W.Environment events ->{h}.W.Environment ev ->{matches} ->{normal} ->{empty} ->
 {l}.CurrentWithRange token_pc initial retired committed pre {packed} ->
 {o}.RFJoint token_pc initial retired({q}.actual_pending {post}{after})committed {post}{after} /\\
 {l}.LedgerRange {post}{after} retired.
Proof. intros pre HE HEv HM HR HV[HCurrent HRange].
 destruct(actual_prefill_facts image events ev HE HEv HM HR HV)as[HDecision[HInvalid[HIdle[HPC HQ]]]];fold pre in HInvalid,HIdle,HQ.
 destruct HCurrent as[[HN[[HCommitted[HRF HResults]]HOperands]][frontier HChain]].
 pose proof({o}.actual_result_phase_from_joint token_pc initial retired({q}.actual_pending pre {packed})image events ev
 HE HEv(conj HN(conj HResults HOperands)))as HResultsPost;fold pre in HResultsPost.
 pose proof({wr}.actual_no_write_preserves_RF image events ev committed HEv(or_introl HIdle)HRF)as HRFPost;fold pre in HRFPost.
 assert(HNewUnique:NoDup(map token_id(retired++({q}.actual_pending pre {packed}++{aq}.admitted ev pre {packed})))).
 {{ rewrite app_assoc,{l}.admitted_form.
    exact(actual_births_preserve_unique_ledger {decision}(serial(fst {packed})){sample}{b}.capture_0_pc
      (retired++{q}.actual_pending pre {packed})HRange HN). }}
 assert(HNewRange:HistoryRange(serial(fst {after}))(retired++({q}.actual_pending pre {packed}++{aq}.admitted ev pre {packed}))).
 {{ rewrite {l}.actual_post_serial,app_assoc,{l}.admitted_form.
    exact(actual_births_preserve_ledger_range {decision}(serial(fst {packed})){sample}{b}.capture_0_pc
      (retired++{q}.actual_pending pre {packed})HRange). }}
 assert(HNewData:{o}.RFJoint token_pc initial retired({q}.actual_pending pre {packed}++{aq}.admitted ev pre {packed})committed {post}{after}).
 {{ split;[exact HNewUnique|];split.
    - exact(conj HCommitted(conj HRFPost({l}.reference_results_survive_append token_pc initial retired({q}.actual_pending pre {packed})
      ({aq}.admitted ev pre {packed}){post}{after}HResultsPost))).
    - intro HBad;exfalso;exact(HBad HInvalid). }}
 split.
 - exact(eq_rect _ (fun pending=>{o}.RFJoint token_pc initial retired pending committed {post}{after})HNewData _ (eq_sym HQ)).
 - unfold {l}.LedgerRange;exact(eq_rect _ (fun pending=>HistoryRange(serial(fst {after}))(retired++pending))HNewRange _ (eq_sym HQ)). Qed.
Theorem actual_prefill_extends_frontier words i events ev(frontier:FormalSpec.State)rd rs1 rs2:
 let image:=ExtendedSVPackedROM.pack words in let pre:={pre}in
 Forall(Word 32)words ->Z.of_nat(length words)<=2^30 ->(i<{plan['capacity']})%nat ->Z.of_nat i<2^25 ->32*Z.of_nat i<2^Z.of_nat {plan['offset_width']} ->
 Forall {h}.W.Environment events ->{h}.W.Environment ev ->{matches} ->{normal} ->{empty} ->
 {r}.FrontierAt pre frontier i words ->{af}.NextPCAligned frontier ->
 Decode.decode Decode.RV32I({f}.R.lookup image(word.unsigned(getPc frontier)))=Decode.IInstruction(Decode.Add rd rs1 rs2) ->
 exists next,EffectChain(CPUOriginalISAReference.instruction_effect {f}.recorded_pc token_word)frontier({aq}.admitted ev pre {packed})next /\\
 {r}.FrontierAt {post} next(S i)words /\\{af}.NextPCAligned next.
Proof. intros image pre HW HLen HC HI HO HE HEv HM HR HV HF HNext HD.
 destruct(actual_prefill_facts image events ev HE HEv HM HR HV)as[HDecision[HInvalid[HIdle[HRealPC HQ]]]];fold pre in HDecision,HRealPC.
 assert(HList:{aq}.admitted ev pre {packed}=[fresh(serial(fst {packed})){sample}{pair['word_input']}%nat {b}.capture_0_pc]).
 {{ rewrite {r}.admitted_as_births,HDecision;reflexivity. }}
 set(token:=fresh(serial(fst {packed})){sample}{pair['word_input']}%nat {b}.capture_0_pc).
 assert(HT:In token({aq}.admitted ev pre {packed}))by(rewrite HList;now left).
 pose proof({af}.actual_new_token_original_ADD words events ev token frontier i rd rs1 rs2 HE HEv HF HT HD)as HDecode;fold image in HDecode;fold pre in HDecode.
 destruct({r}.actual_admitted_ADD_step words events ev token frontier i rd rs1 rs2 HW HLen HC HI HO HE HEv HF HD HT)
 as[next[HStep HRun]];fold image in HStep,HRun;fold pre in HStep,HRun.
 destruct({af}.original_ADD_after_frontier token frontier next rd rs1 rs2 HStep HDecode)as[HPCnext[HNextAfter HMem]].
 destruct HF as[HPC[HAddress HImage]].
 assert(HPCpost:norm 32(read_signal {post}{head['pc']}%nat)=word.unsigned(getPc next)).
 {{ exact(eq_trans HRealPC(eq_trans(f_equal(fun z=>norm 32(z+4))HPC)
   (eq_trans(eq_sym HNext)(eq_sym(f_equal word.unsigned HPCnext))))). }}
 assert(HAddressPost:word.unsigned(getPc next)=4*Z.of_nat(S i)).
 {{ rewrite HPCnext,HNext,HAddress,ExtendedSVPackedROM.norm32_mod,Nat2Z.inj_succ.
    assert(HBound:0<=4*Z.of_nat i+4<2^32)by(pose proof(Nat2Z.is_nonneg i);lia).
    rewrite Z.mod_small by exact HBound;lia. }}
 exists next;split.
 - rewrite HList;change(EffectChain(CPUOriginalISAReference.instruction_effect {f}.recorded_pc token_word)frontier[token]next).
   econstructor;[exact HStep|constructor].
 - exact(conj(conj HPCpost(conj HAddressPost(eq_trans HMem HImage)))HNextAfter). Qed.
Theorem actual_prefill_restores_frontier_joint words i initial retired committed events ev rd rs1 rs2:
 let image:=ExtendedSVPackedROM.pack words in let pre:={pre}in
 Forall(Word 32)words ->Z.of_nat(length words)<=2^30 ->(i<{plan['capacity']})%nat ->Z.of_nat i<2^25 ->32*Z.of_nat i<2^Z.of_nat {plan['offset_width']} ->
 Forall {h}.W.Environment events ->{h}.W.Environment ev ->{matches} ->{normal} ->{empty} ->
 {af}.FrontierJoint words i initial retired committed pre {packed} ->
 Decode.decode Decode.RV32I({f}.R.lookup image(4*Z.of_nat i))=Decode.IInstruction(Decode.Add rd rs1 rs2) ->
 {af}.FrontierJoint words(S i)initial retired committed {post}{after}.
Proof. intros image pre HW HLen HC HI HO HE HEv HM HR HV[HCurrent[frontier[HOld[HF HNext]]]]HDecode.
 destruct(actual_prefill_register_data {f}.recorded_pc initial retired committed image events ev HE HEv HM HR HV HCurrent)
 as[HData HRange];fold pre in HData,HRange.
 assert(HD:Decode.decode Decode.RV32I({f}.R.lookup image(word.unsigned(getPc frontier)))=Decode.IInstruction(Decode.Add rd rs1 rs2)).
 {{ rewrite(proj1(proj2 HF));exact HDecode. }}
 destruct(actual_prefill_extends_frontier words i events ev frontier rd rs1 rs2 HW HLen HC HI HO HE HEv HM HR HV HF HNext HD)
 as[next[HNew[HFPost HNextPost]]];fold image in HNew,HFPost,HNextPost;fold pre in HNew,HFPost,HNextPost.
 pose proof(chain_append(CPUOriginalISAReference.instruction_effect {f}.recorded_pc token_word)committed
  ({q}.actual_pending pre {packed})frontier({aq}.admitted ev pre {packed})next HOld HNew)as HCombined.
 pose proof(actual_normal_rising_queue image events ev HE HEv HM HR)as HQ;fold pre in HQ.
 assert(HChainPost:EffectChain(CPUOriginalISAReference.instruction_effect {f}.recorded_pc token_word)committed({q}.actual_pending {post}{after})next).
 {{ exact(eq_rect _ (fun pending=>EffectChain(CPUOriginalISAReference.instruction_effect {f}.recorded_pc token_word)committed pending next)HCombined _ (eq_sym HQ)). }}
 split;[exact(conj(conj HData(ex_intro _ next HChainPost))HRange)|].
 exists next;exact(conj HChainPost(conj HFPost HNextPost)). Qed.
End OriginalISA.
Goal True. idtac "PREFILL_FRONTIER_AUDIT". exact I. Qed.
Print Assumptions actual_prefill_controls.
Print Assumptions actual_normal_rising_queue.
Print Assumptions actual_prefill_facts.
Print Assumptions actual_prefill_register_data.
Print Assumptions actual_prefill_extends_frontier.
Print Assumptions actual_prefill_restores_frontier_joint.
'''
    return source


def check(c,output):
    out=Path(output);out.mkdir(parents=True,exist_ok=False);pc=bubble.invalid.fetch.pc
    graph=pc.admission.fetch.cdfg.checked_graph(c['graph'],c['ast'],out/'replayed')
    raw,profile,_=pc.admission.fetch.cdfg.raw_binding(c['ast'],c['ast_module']);plan=bubble.discover(c,raw,profile,graph)
    paths=checked_provider(c['normal_write'],'NormalWrite.v',raw['source_sha256'],['all_normal_ADD_RF_phase_branches_proved'])
    for key,file,ns in [('invalid_fetch','InvalidFetch','GeneratedInvalidFetch'),('bubble_control','BubbleControl','GeneratedBubbleControl')]:
        folder=Path(c[key]);receipt=json.loads((folder/'report.json').read_text())
        if not(receipt['accepted']and receipt['coqc_exit']==receipt['coqchk_exit']==0 and receipt['assumptions_closed']
            and receipt['ast_sha256']==raw['source_sha256']and receipt['source_sha256']==hashlib.sha256((folder/(file+'.v')).read_bytes()).hexdigest()):
            raise ValueError('same-source closed native prefill input required: '+key)
        paths +=[dict(namespace=ns,directory=str(folder.resolve()))]
    paths +=[dict(namespace='GeneratedNormalWrite',directory=str(Path(c['normal_write']).resolve()))]
    source=render(c,raw,profile,plan);file=out/'PrefillFrontier.v';file.write_text(source)
    for name,data in [('plan',plan),('providers',paths)]:
        (out/(name+'.json')).write_text(json.dumps(data,indent=2)+'\n')
    flags=list(pc.rtl.framework.FLAGS)
    for row in paths:flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(out.resolve()),'GeneratedPrefillFrontier'];start=time.monotonic()
    cc,timed=run_stage(['/usr/bin/time','-v','-o',str((out/'coqc.resources').resolve()),str(pc.rtl.ROOT/'_opam/bin/coqc'),
        '-time',*flags,str(file.resolve())],out/'coqc.log',1200)
    report=dict(accepted=False,coqc_exit=cc.returncode,coqc_timed_out=timed,source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        ast_sha256=raw['source_sha256'],graph_sha256=hashlib.sha256(Path(c['graph']).read_bytes()).hexdigest(),old_inv_read=False,
        actual_prefill_restores_same_frontier_joint=False,caller_controller_conditions_or_ISA_success_required=False,
        full_R_generated=False,full_cycle_preservation_proved=False,itree_refinement_proved=False,external_llm_api_calls=0)
    if cc.returncode==0:
        axioms=audit_all_exports(cc.stdout.split('PREFILL_FRONTIER_AUDIT')[-1],6)
        baseline=set(json.loads((Path(c['normal_write'])/'report.json').read_text())['baseline_assumptions'])
        audit=not(axioms-baseline)and not(axioms-ALLOWED_AXIOMS)
        kk,timed=run_stage(['/usr/bin/time','-v','-o',str((out/'coqchk.resources').resolve()),str(pc.rtl.ROOT/'_opam/bin/coqchk'),
            '-silent',*flags,'-norec','GeneratedPrefillFrontier.PrefillFrontier'],out/'coqchk.log',max(.1,1200-(time.monotonic()-start)))
        ok=audit and kk.returncode==0
        report.update(accepted=ok,coqchk_exit=kk.returncode,coqchk_timed_out=timed,assumptions_audit_passed=audit,
            isa_assumptions=sorted(axioms),baseline_assumptions=sorted(baseline),actual_prefill_restores_same_frontier_joint=ok)
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
