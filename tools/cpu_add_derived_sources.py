"""Derive ADD source/capture correctness from the SAME generated queue/R.

Actual producer records are extracted with failure on unknown valid identity.
Original ISA batches and ready-slot correspondence are proof outputs, not inputs.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time

import cpu_add_ready_controls as controls
import cpu_pending_recipe_coverage as coverage
from cpu_certificate_acceptance import run_stage, ALLOWED_AXIOMS
from check_reference_value_rules import audit_all_exports
rtl=controls.rtl


def required_bit_proof(expression, root):
    """Same checked constructors, with explicit focus at every branch."""
    if coverage.validity.is_var(expression,1,root):return 'apply RequiresSource.'
    if coverage.validity.is_const(expression,1,0):return 'apply RequiresZero.'
    n,a=expression.name,expression.args
    if n=='EExtend'and a[:2]==(rtl.Term('1'),rtl.Term('false')):
        child=required_bit_proof(a[2],root)
        return None if child is None else'apply RequiresExtend. '+child
    if n=='EBinary'and a[:2]==(rtl.Term('1'),rtl.Term('BAnd')):
        left,right=required_bit_proof(a[2],root),required_bit_proof(a[3],root)
        if left is not None:return 'apply RequiresAndLeft. '+left
        if right is not None:return 'apply RequiresAndRight. '+right
    if n=='ECond'and a[0].name=='1':
        yes,no=required_bit_proof(a[2],root),required_bit_proof(a[3],root)
        if yes is not None and no is not None:return 'apply RequiresChoice. { '+yes+' } { '+no+' }'
    return None


def discover(raw, ready_plan, queue_plan, c):
    physical,_=controls.history.admission.ready.discover(raw)
    data={code:{next(p['data']['terminal']for p in r['row']['paths']if p['code']==code)
                for r in physical['rows']}for code in [1,2,3]}
    if any(len(x)!=1 for x in data.values()):raise ValueError('forwarding ports do not share producer data identity')
    result=dict(rows=ready_plan['rows'],young_value=next(iter(data[1])),old_value=next(iter(data[2])),
        memory_value=next(iter(data[3])),bank=physical['rows'][0]['port']['bank'],
        birth=next(n for n in queue_plan['nodes']if n['index']is None),
        head=next(n for n in queue_plan['nodes']if n['index']==0),
        ast_sha256=raw['source_sha256'])
    if result['head']['event']['clock']!=queue_plan['capture_clock']:
        raise ValueError('source admission clock differs from original queue clock')
    operand_plan=json.loads((Path(c['operands'])/'plan.json').read_text())
    result['ports']=[]
    for r in physical['rows']:
        row=r['row'];output=next(p['output']for p in row['paths']if p['code']==0)
        matches=[p for p in operand_plan['rows']if p['stage']==0 and p['route']and p['route']['terminal']==output]
        if len(matches)!=1:raise ValueError('no unique actual operand capture')
        result['ports'].append(dict(selector=row['selector']['root'],source=row['binding']['first']['rs'],
            field=r['port']['field'],operand=matches[0]['root']))
    if {p['field']for p in result['ports']}!={'Rs1','Rs2'}:raise ValueError('both actual source roles required')
    return result


def render(c,raw,profile,plan,cov):
    p,am=profile['ast']['program'],raw['module']
    q='GeneratedPhasePendingCommit.PhasePendingCommit'
    o='GeneratedOperandResultJoint.OperandResultJoint'
    v='GeneratedValidResult.ValidResult'
    sample=f'(phase_driven_state {p} ev pre)';post=f'(PhaseSemantics {p} ev pre)'
    packed='(Runtime.boot_history image events)'
    clock,reset=plan['head']['event']['clock'],plan['head']['event']['reset']
    headvalid,birthvalid=plan['head']['valid'],plan['birth']['valid']
    protected=sorted({headvalid,birthvalid,plan['old_value']})
    req=required_bit_proof(rtl.Parser(cov['coverage']['covered_fields'][0]['expanded']).complete(),birthvalid)
    if req is None:raise ValueError('admission valid does not require the actual source valid bit')
    source=f'''From Coq Require Import List ZArith Bool Lia.
Require Import {c['ast_module']} Lang.ExtendedSV Lang.ExtendedSVScalarExpression Lang.ExtendedSVScalarHistory
 Lang.ExtendedSVWordInvariant Lang.ExtendedSVRootProjection Lang.ExtendedSVProjectionConnection
 Lang.ExtendedSVRecipeCoverage Lang.ExtendedSVCaptureBirth Lang.ExtendedSVCapturedPending Lang.ExtendedSVCompanionField
 Lang.ExtendedSVProjectionOrigin
 Lang.ExtendedSVRegisterBank Ex.External.CPUGeneratedJointTemplate Ex.External.CPUOriginalISAReference
 Ex.External.CPUReferenceProducerBatches Ex.External.CPUISAAddReferenceValues Ex.External.CPUReferenceValues
 Ex.External.CPUReferenceCuts Ex.External.CPUComputedReferenceCut Ex.External.CPUComputedResultCut
 Ex.External.CPUISAOwnedEffects Ex.External.CPUISAReadyBatches Ex.External.CPUReadyOperand
 Ex.External.CPUReadySlotCompaction Ex.External.CPUTwoStageReadySelection Ex.External.CPURegisterEffectRelation
 Ex.External.CPUISAInstructionExecution Ex.External.CPUISAExecutionEffects
 Ex.RvCore.FormalSpec Ex.RvCore.Machine coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth
 coqutil.Map.Interface coqutil.Byte GeneratedReadyControls.ReadyControls
 GeneratedPhasePendingCommit.PhasePendingCommit GeneratedCapturedReads.CapturedReadAddresses
 GeneratedReadyCapture.ReadyCapture GeneratedAdmissionWrite.AdmissionWrite.
Import ListNotations ExtendedSV ExtendedSVScalarExpression ExtendedSVScalarHistory ExtendedSVWordInvariant
 ExtendedSVRootProjection ExtendedSVProjectionConnection ExtendedSVRecipeCoverage ExtendedSVCaptureBirth ExtendedSVCapturedPending
 ExtendedSVCompanionField ExtendedSVRegisterBank CPUGeneratedJointTemplate CPUOriginalISAReference
 ExtendedSVProjectionOrigin
 CPUISAOwnedEffects CPUISAReadyBatches CPUReadyOperand CPUReadySlotCompaction CPUTwoStageReadySelection
 CPURegisterEffectRelation CPUReferenceCuts CPUComputedReferenceCut CPUComputedResultCut CPUISAInstructionExecution CPUISAExecutionEffects.
Module Ref:=CPUReferenceProducerBatches.
Module Runtime:=GeneratedCapturedReads.CapturedReadAddresses.H.
Module Captured:=Runtime.C.
Local Opaque {p} PhaseSemantics.
'''
    source+='Lemma protect ev root:Runtime.W.Environment ev ->In root ['+';'.join(str(x)+'%nat'for x in protected)+'] ->changed_signal ev<>root.\n'
    source+='''Proof. intros[_ HE]HI;unfold Runtime.W.ExternalEvent in HE;apply existsb_exists in HE;
 destruct HE as[x[HX HE]];apply Nat.eqb_eq in HE;rewrite HE;unfold Runtime.W.external_roots in HX;
 cbn in HX,HI;repeat destruct HX as[<-|HX];try contradiction;
 repeat destruct HI as[<-|HI];try contradiction;discriminate. Qed.
'''
    for root in protected:
        source+=f'Lemma frame_{root}:comb_root_unwrittenb {p} {root}=true. Proof. vm_compute;reflexivity. Qed.\n'
    source+=f'''Lemma source_required:RequiresBit {birthvalid} Captured.V.coverage_0_expanded.
Proof. unfold Captured.V.coverage_0_expanded. {req} Qed.
Lemma expanded_valid seed sampled:CombLFP {p} seed sampled ->
 norm 1(eval_expr sampled Captured.V.root_{headvalid}_expression)=norm 1(eval_expr sampled Captured.V.coverage_0_expanded).
Proof. intro HL;pose proof(bindings_substitute_sound Captured.V.coverage_0_bindings Captured.V.root_{headvalid}_expression sampled
 (Captured.V.coverage_0_bindings_agree seed sampled HL))as HX;
 rewrite Captured.V.coverage_0_expansion_checked in HX;exact(f_equal(norm 1)(eq_sym HX)). Qed.
Lemma admitted_source_valid seed ev pre:
 Runtime.W.Environment ev ->CombLFP {p} seed {sample} ->
 process_matches_states pre {sample}{am}.{plan['head']['process']}=true ->
 norm 1(read_signal {post}{headvalid})<>0%Z ->norm 1(read_signal pre {birthvalid})<>0%Z.
Proof. intros HE HL HM HV.
 pose proof(history_phase_projection _ _ _ _ _ Captured.V.root_{headvalid}_valid_certificate ev pre
 (protect ev {headvalid} HE ltac:(simpl;tauto)))as HP;rewrite HM in HP.
 assert(HExpanded:norm 1(eval_expr {sample} Captured.V.coverage_0_expanded)<>0%Z).
 {{ intro HZ;apply HV;exact(eq_trans HP(eq_trans(expanded_valid seed _ HL)HZ)). }}
 pose proof(requires_bit_sound {birthvalid} Captured.V.coverage_0_expanded source_required {sample} HExpanded)as HH.
 rewrite(sampled_root_preserved {p} ev pre {birthvalid} frame_{birthvalid}(protect ev {birthvalid} HE ltac:(simpl;tauto)))in HH;exact HH.
Qed.
Lemma admission_old_clock_zero ev pre:
 Runtime.W.Environment ev ->process_matches_states pre {sample}{am}.{plan['head']['process']}=true ->
 norm 1(read_signal {post}{headvalid})<>0%Z ->norm 1(read_signal pre {clock})=0%Z.
Proof. intros HE HM HV.
 pose proof(GeneratedAdmissionWrite.AdmissionWrite.actual_capture_reset ev pre
 (protect ev {headvalid} HE ltac:(simpl;tauto))HM HV)as HR.
 assert(HR0:Z.eqb(read_signal {sample}{reset})0%Z=false).
 {{ apply Z.eqb_neq;intro HZ;rewrite HZ in HR;discriminate. }}
 change((edge_fires Posedge(read_signal pre {clock})(read_signal {sample}{clock})||
  (edge_fires Negedge(read_signal pre {reset})(read_signal {sample}{reset})||false))%bool=true)in HM.
 unfold edge_fires in HM;rewrite HR0,andb_false_r,!orb_false_r in HM.
 apply Bool.andb_true_iff in HM as[HC _];apply Z.eqb_eq in HC;rewrite HC;reflexivity. Qed.
'''
    bits=lambda s,r:f'(GeneratedReadySelector.ReadySelector.bit {s} {r})'
    for row in plan['rows']:
        i=row['stage'];rd=row['routes']['rd']['input'];wr=row['routes']['write']['input'];ld=row['routes']['load']['input']
        value=plan['young_value']if i==0 else plan['old_value']
        source+=f'''Definition collect_{i} pre sampled(packed:Captured.Packed):option(list(@Ref.Producer Token)):=
 Ref.collect(norm 1(read_signal pre {row['valid']}))(Captured.C.chain_tag{i}(snd packed))
 (norm 5(read_signal sampled {rd}))(norm 32(read_signal sampled {value})).
'''
        actualvalue=f'(norm 32(read_signal sampled {value}))'if i==0 else f'(if {bits("sampled",ld)}then norm 32(read_signal sampled {plan["memory_value"]})else norm 32(read_signal sampled {value}))'
        source+=f'Definition hardware_slot_{i} sampled:=slot {bits("sampled",wr)}(norm 5(read_signal sampled {rd}))'+('(negb '+bits('sampled',ld)+')'if i==0 else'true')+actualvalue+'.\n'
    source+=f'''Definition producers pre sampled packed:=match collect_1 pre sampled packed with
 |None=>None|Some older=>match collect_0 pre sampled packed with None=>None|Some younger=>Some(older++younger)end end.
Definition hardware_slots sampled:=[hardware_slot_1 sampled;hardware_slot_0 sampled].
Section OriginalISA.
Context {{word:Interface.word 32}}{{BW:Bitwidth 32}}{{Registers:map.map Z word}}{{Mem:map.map word byte}}
 {{word_ok:word.ok word}}{{registers_ok:map.ok Registers}}.
Definition ledger(retired:list Token)pre packed:=retired++{q}.actual_pending pre packed.
Definition Current(token_pc:Token->Z)(initial:FormalSpec.State)retired current pre packed:=
 {q}.QueueRegisterInv token_pc initial retired current pre packed.
'''
    unpack='[[HN[[HC[HR[HCov[HMem HWb]]]]HOp]][frontier HChain]]'
    for row in plan['rows']:
        i,valid=row['stage'],row['valid'];rd=row['routes']['rd']['input'];value=plan['young_value']if i==0 else plan['old_value']
        source+=f'''Lemma reference_{i} token_pc initial retired current image events ev token:
 let pre:=phase_run {p} events(Runtime.F.boot image)in
 Forall Runtime.W.Environment events ->Runtime.W.Environment ev ->Current token_pc initial retired current pre {packed} ->
 norm 1(read_signal pre {valid})<>0%Z ->Captured.C.chain_tag{i}(snd {packed})=Some token ->
 CPUISAAddReferenceValues.values token_pc token_word token_id initial(ledger retired pre {packed})token=
 Some(norm 32(read_signal {sample}{value})).
Proof. intros pre HE HEv HJ HV HT;destruct HJ as{unpack}.
'''
        if i==1:
            source+=f'''pose proof(HMem HV token HT)as HH.
 exact(eq_trans HH(f_equal(@Some Z)(f_equal(norm 32)(eq_sym(sampled_root_preserved {p} ev pre {value}
 frame_{value}(protect ev {value} HEv ltac:(simpl;tauto))))))). Qed.
'''
        else:
            source+=f'''pose proof({o}.head_from_operand_clause token_pc initial(ledger retired pre {packed})image events ev HE HEv HN HOp)as HH.
 exact({v}.Previous.head_from_original_ISA token_pc _ image events ev HE HEv(HH HV)token HT). Qed.
'''
        source+=f'''Lemma compatible_{i} token_pc initial retired current image events ev token:
 let pre:=phase_run {p} events(Runtime.F.boot image)in
 Forall Runtime.W.Environment events ->Runtime.W.Environment ev ->Current token_pc initial retired current pre {packed} ->
 norm 1(read_signal pre {clock})=0%Z ->norm 1(read_signal pre {valid})<>0%Z ->Captured.C.chain_tag{i}(snd {packed})=Some token ->
 Ref.AddCompatible token_pc token_word token_id initial(ledger retired pre {packed})
 (Ref.Build_Producer token(norm 5(read_signal {sample}{rd}))(norm 32(read_signal {sample}{value}))).
Proof. intros pre HE HEv HJ HClock HV HT;pose proof HJ as{unpack}.
 eapply Ref.reference_result_add_compatible.
 - exact HN.
 - exact(chain_append(instruction_effect token_pc token_word)initial retired current _ frontier HC HChain).
 - apply in_or_app;right;rewrite({q}.pending_low pre {packed} HClock);unfold {q}.lower_pending.
'''
        source+=('   apply in_or_app;left.\n'if i==1 else'   apply in_or_app;right;apply in_or_app;left.\n')
        source+=f'''   rewrite({q}.slot_nonempty pre {valid} _ token HV HT);left;reflexivity.
 - exact(GeneratedReadyControls.ReadyControls.sampled_token_destination_{i} image events ev token HE HEv HV HT).
 - exact(reference_{i} token_pc initial retired current image events ev token HE HEv HJ HV HT). Qed.
Lemma collect_{i}_compatible token_pc initial retired current image events ev ps:
 let pre:=phase_run {p} events(Runtime.F.boot image)in
 Forall Runtime.W.Environment events ->Runtime.W.Environment ev ->Current token_pc initial retired current pre {packed} ->
 norm 1(read_signal pre {clock})=0%Z ->collect_{i} pre {sample}{packed}=Some ps ->
 Forall(Ref.AddCompatible token_pc token_word token_id initial(ledger retired pre {packed}))ps.
Proof. intros pre HE HEv HJ HClock HCollect;apply(Ref.collect_forall _ _ _ _ _ _ HCollect).
 intros token HV HT;exact(compatible_{i} token_pc initial retired current image events ev token HE HEv HJ HClock HV HT). Qed.
Lemma collect_{i}_slots token_pc initial retired current image events ev ps:
 let pre:=phase_run {p} events(Runtime.F.boot image)in
 Forall Runtime.W.Environment events ->Runtime.W.Environment ev ->Current token_pc initial retired current pre {packed} ->
 norm 1(read_signal pre {clock})=0%Z ->collect_{i} pre {sample}{packed}=Some ps ->
 compact[hardware_slot_{i} {sample}]=compact(map Ref.ready_slot ps).
Proof. intros pre HE HEv HJ HClock HCollect;eapply Ref.collect_slot;[exact HCollect| |].
 - intro HV;exact(GeneratedReadyControls.ReadyControls.invalid_sampled_slot_{i} image events ev _ _ HE HEv HV).
 - intros token HV HT;pose proof(compatible_{i} token_pc initial retired current image events ev token HE HEv HJ HClock HV HT)as[[rs1[rs2 HD]]HValue].
   destruct(GeneratedReadyControls.ReadyControls.actual_add_sampled_controls_{i} image events ev token _ rs1 rs2 HE HEv HV HT HD)as[HWrite[HLoad HRd]].
   fold pre in HWrite,HLoad,HRd;unfold hardware_slot_{i};rewrite HWrite,HLoad.
   unfold slot,Ref.ready_slot;cbn[Ref.producer_rd Ref.producer_value];
   destruct(Z.eqb(norm 5(read_signal {sample}{rd}))0%Z);repeat rewrite norm_idempotent;reflexivity. Qed.
'''
    source+=f'''Theorem actual_producer_bundle token_pc initial retired current image events ev:
 let pre:=phase_run {p} events(Runtime.F.boot image)in
 Forall Runtime.W.Environment events ->Runtime.W.Environment ev ->Current token_pc initial retired current pre {packed} ->
 norm 1(read_signal pre {clock})=0%Z ->exists ps,
 producers pre {sample}{packed}=Some ps /\\
 map Ref.producer_token ps={q}.slot pre {plan['rows'][1]['valid']}(Captured.C.chain_tag1(snd {packed}))++
 {q}.slot pre {plan['rows'][0]['valid']}(Captured.C.chain_tag0(snd {packed})) /\\
 Forall(Ref.AddCompatible token_pc token_word token_id initial(ledger retired pre {packed}))ps /\\
 compact(hardware_slots {sample})=compact(map Ref.ready_slot ps).
Proof. intros pre HE HEv HJ HClock;pose proof HJ as{unpack}.
'''
    for i in [1,0]:
        row=plan['rows'][i];rd=row['routes']['rd']['input'];value=plan['old_value']if i else plan['young_value']
        # The explicit option failure is discharged by physical validity coverage.
        source+=f'''assert(HCover{i}:norm 1(read_signal pre {row['valid']})<>0%Z ->exists t,Captured.C.chain_tag{i}(snd {packed})=Some t).
 {{ intro HV;destruct(Captured.valid_field_{i}_has_value pre {packed} HCov HV)as[t[HT _]];exists t;exact HT. }}
 destruct(Ref.collect_exists(norm 1(read_signal pre {row['valid']}))(Captured.C.chain_tag{i}(snd {packed}))
 (norm 5(read_signal {sample}{rd}))(norm 32(read_signal {sample}{value}))HCover{i})as[ps{i} HC{i}].
'''
    source+=f'''exists(ps1++ps0);split;[unfold producers,collect_1,collect_0;rewrite HC1,HC0;reflexivity|];split.
 - rewrite map_app;exact(f_equal2(@app Token)(Ref.collect_tokens _ _ _ _ _ HC1)(Ref.collect_tokens _ _ _ _ _ HC0)).
 - split.
   + apply Forall_app;split;[exact(collect_1_compatible token_pc initial retired current image events ev ps1 HE HEv HJ HClock HC1)|
     exact(collect_0_compatible token_pc initial retired current image events ev ps0 HE HEv HJ HClock HC0)].
   + change(compact([hardware_slot_1 {sample}]++[hardware_slot_0 {sample}])=compact(map Ref.ready_slot(ps1++ps0))).
     rewrite map_app,!Ref.compact_append.
     exact(f_equal2(@app(@Slot Z))(collect_1_slots token_pc initial retired current image events ev ps1 HE HEv HJ HClock HC1)
       (collect_0_slots token_pc initial retired current image events ev ps0 HE HEv HJ HClock HC0)). Qed.
'''
    source+=f'''Theorem actual_admitted_add_operand_relation token_pc initial retired current image events ev token dest rs1 rs2:
 let pre:=phase_run {p} events(Runtime.F.boot image)in
 Forall Runtime.W.Environment events ->Runtime.W.Environment ev ->
 ExtendedSVCaptureBirth.current(fst {packed})=Some token ->
 process_matches_states pre {sample}{am}.{plan['head']['process']}=true ->
 norm 1(read_signal {post}{headvalid})<>0%Z ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Add dest rs1 rs2) ->
 Current token_pc initial retired current pre {packed} ->
 computed_result_R(instruction_effect token_pc token_word)token_eq_dec
 ({o}.OperandProjection token {post})token initial(ledger retired pre {packed}).
Proof. intros pre HE HEv HT HM HV HD HJ.
 destruct(GeneratedCapturedReads.CapturedReadAddresses.sample_evidence image events ev HE HEv)as[seed HL];fold pre in HL.
 pose proof(admitted_source_valid seed ev pre HEv HL HM HV)as HSource.
 pose proof(admission_old_clock_zero ev pre HEv HM HV)as HClock.
 destruct(actual_producer_bundle token_pc initial retired current image events ev HE HEv HJ HClock)as[ps[HCollect[HTokens[HCompatible HSlots]]]].
 fold pre in HCollect,HTokens,HCompatible,HSlots.
 pose proof HJ as{unpack}.
 assert(HPending:{q}.actual_pending pre {packed}=map Ref.producer_token ps++[token]).
 {{ rewrite({q}.pending_low pre {packed} HClock);unfold {q}.lower_pending.
    rewrite({q}.slot_nonempty pre {birthvalid} _ token HSource HT),app_assoc.
    exact(f_equal(fun tokens=>tokens++[token])(eq_sym HTokens)). }}
 rewrite HPending in HChain.
 destruct(chain_split(instruction_effect token_pc token_word)(map Ref.producer_token ps)current[token]frontier HChain)as[before[HOlder HSingle]].
 assert(HB:CertifiedBatches token_pc token_word current(map Ref.batch ps)before).
 {{ apply(Ref.certify_reference_producers token_pc token_word token_id initial retired current ps[token]before HC).
    - rewrite <-HPending;exact HN.
    - unfold ledger in HCompatible;rewrite HPending in HCompatible;exact HCompatible.
    - exact HOlder. }}
 assert(HRelated:forall address,Forall2 SlotRelated(compact(hardware_slots {sample}))(batch_writes 32 address(map Ref.batch ps))).
 {{ intro address;exact(eq_rect _ (fun slots=>Forall2 SlotRelated slots(batch_writes 32 address(map Ref.batch ps)))
     (Ref.summaries_slots_related address ps)_(eq_sym HSlots)). }}
 inversion HSingle as[|a t after rest last HStep HNil];subst;inversion HNil;subst.
 destruct(token_execute token_pc token_word token before frontier _ HStep HD)as[middle[HExec HEnd]].
 destruct(original_add_effect before middle dest rs1 rs2 HExec)as[x[y[HX[HY HEffect]]]].
'''
    for port in plan['ports']:
        s=port['selector'];val='x'if port['field']=='Rs1'else'y';read='HX'if port['field']=='Rs1'else'HY'
        source+=f'''pose proof(GeneratedReadyCapture.ReadyCapture.captured_source_add_{s} token_pc image events ev token dest rs1 rs2
 current(map Ref.batch ps)before {val} HE HEv HT(protect ev {headvalid} HEv ltac:(simpl;tauto))HM HV HD HB HR {read}
 (HRelated(norm 5(read_signal {sample}{port['source']}))))as HCaptured{s};fold pre in HCaptured{s}.
'''
    source+=f'''assert(HLedger:ledger retired pre {packed}=(retired++map Ref.producer_token ps)++[token]).
 {{ unfold ledger;rewrite HPending;apply app_assoc. }}
 assert(HBefore:BeforeToken(instruction_effect token_pc token_word)initial(ledger retired pre {packed})
 (length(retired++map Ref.producer_token ps))token before).
 {{ rewrite HLedger;apply Ref.before_prefix;eapply chain_append;[exact HC|exact HOlder]. }}
 assert(HND:NoDup(ledger retired pre {packed}))by(eapply NoDup_map_inv;exact HN).
 apply(proj2(computed_result_R_exact(instruction_effect token_pc token_word)token_eq_dec
 ({o}.OperandProjection token {post})token initial(ledger retired pre {packed}))).
 exists(length(retired++map Ref.producer_token ps)),before,frontier;split.
 - exact(lookup_before_complete(instruction_effect token_pc token_word)token_eq_dec token
    (ledger retired pre {packed})initial _ before HND HBefore).
 - split;[exact HStep|];exists dest,rs1,rs2;split;[exact HD|].
   intros x' y' HX' HY';assert(x'=x)by congruence;assert(y'=y)by congruence;subst;split.
'''
    for port in sorted(plan['ports'],key=lambda p:p['field']):
        source+=f'   + exact HCaptured{port["selector"]}.\n'
    source+=f'''Qed.
Lemma actual_admitted_tag ev pre packed:
 Runtime.W.Environment ev ->process_matches_states pre {sample}{am}.{plan['head']['process']}=true ->
 norm 1(read_signal {post}{headvalid})<>0%Z ->
 Captured.C.chain_tag0(snd(Captured.advance_capture_fields ev pre packed tt))=current(fst packed).
Proof. intros HE HM HV.
 pose proof(GeneratedAdmissionWrite.AdmissionWrite.actual_capture_reset ev pre
 (protect ev {headvalid} HE ltac:(simpl;tauto))HM HV)as HR.
 cbn[Captured.advance_capture_fields snd Captured.C.advance_tags Captured.C.chain_tag0].
 unfold Captured.C.projection_0_origin,projection_phase_origin;rewrite HM.
 unfold Captured.C.projection_0_recipe;cbn[recipe_origin eval_expr];rewrite HR;reflexivity.
Qed.
Theorem actual_add_operand_clause_phase token_pc initial retired current_state image events ev:
 let pre:=phase_run {p} events(Runtime.F.boot image)in
 Forall Runtime.W.Environment events ->Runtime.W.Environment ev ->
 (forall token,current(fst {packed})=Some token ->exists rd rs1 rs2,
  Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Add rd rs1 rs2)) ->
 Current token_pc initial retired current_state pre {packed} ->
 {o}.OperandClause token_pc initial(ledger retired pre {packed})
 {post}(Captured.advance_capture_fields ev pre {packed} tt).
Proof. intros pre HE HEv HClass HJ.
 destruct(process_matches_states pre {sample}{am}.{plan['head']['process']})eqn:HM.
 - intros HV token HT.
   pose proof(actual_admitted_tag ev pre {packed} HEv HM HV)as HTag;rewrite HT in HTag.
   destruct(HClass token(eq_sym HTag))as[rd[rs1[rs2 HD]]].
   exact(actual_admitted_add_operand_relation token_pc initial retired current_state image events ev token rd rs1 rs2
     HE HEv(eq_sym HTag)HM HV HD HJ).
 - destruct HJ as[[HN[[HC[HR[HCov[HMem HWb]]]]HOp]]HChain].
   exact({o}.operand_clause_idle token_pc initial(ledger retired pre {packed})image events ev HEv HM HOp).
Qed.
Theorem actual_add_operand_clause_with_new_tokens token_pc initial retired current_state image events ev added:
 let pre:=phase_run {p} events(Runtime.F.boot image)in
 Forall Runtime.W.Environment events ->Runtime.W.Environment ev ->
 (forall token,current(fst {packed})=Some token ->exists rd rs1 rs2,
  Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Add rd rs1 rs2)) ->
 Current token_pc initial retired current_state pre {packed} ->
 {o}.OperandClause token_pc initial(ledger retired pre {packed}++added)
 {post}(Captured.advance_capture_fields ev pre {packed} tt).
Proof. intros pre HE HEv HClass HJ HV token HT.
 apply Ref.computed_result_append.
 exact(actual_add_operand_clause_phase token_pc initial retired current_state image events ev HE HEv HClass HJ HV token HT).
Qed.
End OriginalISA.
'''
    source+='Goal True. idtac "DERIVED_SOURCE_LOCAL_AUDIT". exact I. Qed.\nPrint Assumptions admitted_source_valid. Print Assumptions admission_old_clock_zero.\n'
    source+='Goal True. idtac "DERIVED_SOURCE_ISA_AUDIT". exact I. Qed.\n'
    exports=[f'{name}_{i}'for i in [0,1]for name in ['reference','compatible']]+[f'collect_{i}_{name}'for i in[0,1]for name in ['compatible','slots']]
    exports+=['actual_producer_bundle','actual_admitted_add_operand_relation','actual_admitted_tag',
              'actual_add_operand_clause_phase','actual_add_operand_clause_with_new_tokens']
    source+=''.join(f'Print Assumptions {name}.\n'for name in exports)
    return source,len(exports)


def check(c,context,ready,output):
    out=Path(output);out.mkdir(parents=True,exist_ok=False)
    raw,profile,_=controls.history.admission.observation.origin.raw_binding(c['ast'],c['ast_module'])
    rp=controls.history.admission.checked(ready,'ReadyControls',raw['source_sha256'])
    qp=json.loads((Path(context)/'plan.json').read_text())
    if qp['ast_sha256']!=raw['source_sha256']:raise ValueError('queue configuration differs')
    qreport=json.loads((Path(context)/'report.json').read_text())
    if not(qreport.get('accepted')and qreport.get('coqc_exit')==qreport.get('coqchk_exit')==0 and
           hashlib.sha256((Path(context)/'PhasePendingCommit.v').read_bytes()).hexdigest()==qreport['source_sha256']):
        raise ValueError('checked current queue/R provider required')
    paths=json.loads((Path(context)/'providers.json').read_text())
    environment_hashes=controls.history.admission.verify_environment_paths(paths)
    baseline=set(qreport['baseline_assumptions'])
    if baseline-ALLOWED_AXIOMS or not qreport.get('assumptions_audit_passed'):
        raise ValueError('original ISA baseline assumption audit required')
    covpath=next(r['directory']for r in paths if r['namespace']=='GeneratedCoveredCapture')
    cov=json.loads((Path(covpath)/'plan.json').read_text())
    plan=discover(raw,rp,qp,c)
    graph=controls.history.admission.checked_graph(c['graph'],c['ast'],out/'replayed')
    # Both actual producer data paths are selected from this fresh graph.
    from cpu_pyslang_cdfg import backward_slice
    symbols={s['coq_root']:s for s in graph['symbols']}
    queries=[backward_slice(graph,symbols[x]['path'])for x in [plan['young_value'],plan['old_value']]]
    (out/'graph-queries.json').write_text(json.dumps(queries,indent=2)+'\n')
    source,count=render(c,raw,profile,plan,cov);file=out/'DerivedSources.v';file.write_text(source)
    (out/'plan.json').write_text(json.dumps(plan,indent=2)+'\n')
    paths+=json.loads((Path(ready)/'providers.json').read_text())
    paths.append(dict(directory=str(Path(ready).resolve()),namespace='GeneratedReadyControls'))
    paths=list({(r['namespace'],r['directory']):r for r in paths}.values())
    (out/'providers.json').write_text(json.dumps(paths,indent=2)+'\n')
    flags=list(rtl.framework.FLAGS)
    for row in paths:flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(out.resolve()),'GeneratedDerivedSources'];start=time.monotonic()
    cc,timed=run_stage(['/usr/bin/time','-v','-o',str((out/'coqc.resources').resolve()),
        str(controls.history.admission.observation.origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],out/'coqc.log',1200)
    report=dict(accepted=False,coqc_exit=cc.returncode,coqc_timed_out=timed,source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        ast_sha256=raw['source_sha256'],old_inv_read=False,complete_R_generated=False,
        caller_batch_correctness_eliminated=False,caller_slot_correspondence_eliminated=False,external_llm_api_calls=0,
        baseline_assumptions=sorted(baseline),original_environment_hashes=environment_hashes,
        actual_post_operand_clause_proved=False,post_ledger_queue_equation_proved=False)
    if cc.returncode==0:
        local=cc.stdout.split('DERIVED_SOURCE_LOCAL_AUDIT')[-1].split('DERIVED_SOURCE_ISA_AUDIT')[0]
        tail=cc.stdout.split('DERIVED_SOURCE_ISA_AUDIT')[-1]
        closed=local.count('Closed under the global context')==2 and 'Axioms:'not in local
        axioms=audit_all_exports(tail,count);audit=closed and not(axioms-ALLOWED_AXIOMS)and not(axioms-baseline)
        kk,timed=run_stage(['/usr/bin/time','-v','-o',str((out/'coqchk.resources').resolve()),
            str(controls.history.admission.observation.origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
            'GeneratedDerivedSources.DerivedSources'],out/'coqchk.log',max(.1,1200-(time.monotonic()-start)))
        accepted=audit and kk.returncode==0
        report.update(coqchk_exit=kk.returncode,coqchk_timed_out=timed,local_assumptions_closed=closed,
            isa_assumptions=sorted(axioms),assumptions_audit_passed=audit,accepted=accepted,
            caller_batch_correctness_eliminated=accepted,caller_slot_correspondence_eliminated=accepted,
            actual_post_operand_clause_proved=accepted)
    report['seconds']=time.monotonic()-start;(out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for x in ['inputs','context','ready','output']:p.add_argument('--'+x,required=True)
    a=p.parse_args()
    try:r=check(json.loads(Path(a.inputs).read_text()),a.context,a.ready,a.output)
    except Exception as e:
        out=Path(a.output)
        if out.is_dir()and not(out/'report.json').exists():
            (out/'report.json').write_text(json.dumps(dict(accepted=False,stage='preflight',error=str(e),cli_exit=1),indent=2)+'\n')
        raise
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
