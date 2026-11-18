(** Original-ISA ADD/ADDI producer certificates; generic summaries are reused. *)
From Coq Require Import List ZArith Bool.
Require Import Ex.External.CPUReferenceProducerBatches
 Ex.External.CPUGeneratedJointTemplate
 Ex.External.CPUISAAddFamilyReferenceValues Ex.External.CPUISAAddiEffects
 Ex.External.CPUISAAddiFields Ex.External.CPUReferenceValues Ex.External.CPUReferenceCuts
 Ex.External.CPUOriginalISAReference Ex.External.CPUInstructionFields
 Ex.External.CPUISAAddOperandFields Ex.External.CPUISAInstructionExecution
 Ex.External.CPUISAExecutionEffects Ex.External.CPUISARegisterUpdate
 Ex.External.CPUISAOwnedEffects Ex.External.CPUISAReadyBatches
 Ex.External.CPUReadyOperand Ex.External.CPUReadySlotCompaction
 Ex.External.CPURegisterEffectRelation Lang.ExtendedSVRegisterBank
 Ex.RvCore.FormalSpec Ex.RvCore.Machine coqutil.Word.Interface
 coqutil.Word.Properties coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte
 riscv.Utility.Utility.
Import ListNotations CPUReferenceProducerBatches CPUOriginalISAReference
 CPUGeneratedJointTemplate
 CPUInstructionFields CPUISAAddOperandFields CPUISAAddiFields CPUISAAddiEffects
 CPUISAInstructionExecution CPUISAExecutionEffects CPUISARegisterUpdate
 CPUISAOwnedEffects CPUISAReadyBatches CPUReadyOperand CPUReadySlotCompaction
 CPURegisterEffectRelation CPUReferenceCuts ExtendedSVRegisterBank.
Module CPUReferenceAddFamilyProducers.
Section ISA.
Context {word:Interface.word 32}{BW:Bitwidth 32}{Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}{registers_ok:map.ok Registers}{Token:Type}.
Variables token_pc token_word:Token->Z.
Variable key:Token->nat.

Definition FamilyCompatible(initial:FormalSpec.State)ledger(p:@Producer Token):Prop:=
 ((exists rs1 rs2,Decode.decode Decode.RV32I(token_word(producer_token p))=
   Decode.IInstruction(Decode.Add(producer_rd p)rs1 rs2)) \/
  (exists rs imm,Decode.decode Decode.RV32I(token_word(producer_token p))=
   Decode.IInstruction(Decode.Addi(producer_rd p)rs imm))) /\
 CPUISAAddFamilyReferenceValues.values token_pc token_word key initial ledger(producer_token p)=Some(producer_value p).

Lemma computed_value_implies_family token before value:
 CPUISAAddFamilyReferenceValues.computed_value token_word token before=Some value ->
 (exists rd rs1 rs2,Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Add rd rs1 rs2)) \/
 (exists rd rs imm,Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Addi rd rs imm)).
Proof.
 unfold CPUISAAddFamilyReferenceValues.computed_value;
 destruct(Decode.decode Decode.RV32I(token_word token))eqn:HD;try discriminate;
 destruct iInstruction;try discriminate;intro H;
 first [left;repeat eexists;exact HD|right;repeat eexists;exact HD].
Qed.

Theorem reference_result_family_compatible initial ledger frontier(p:@Producer Token):
 NoDup(map key ledger) ->EffectChain(instruction_effect token_pc token_word)initial ledger frontier ->
 In(producer_token p)ledger ->producer_rd p=field_reference(token_word(producer_token p))Rd ->
 CPUISAAddFamilyReferenceValues.values token_pc token_word key initial ledger(producer_token p)=Some(producer_value p) ->
 FamilyCompatible initial ledger p.
Proof.
 intros HN HC HI HR HV;split;[|exact HV].
 destruct(In_nth_error ledger(producer_token p)HI)as[index HT].
 destruct(token_before_exists(instruction_effect token_pc token_word)initial ledger frontier index(producer_token p)HC HT)as[before HB].
 unfold CPUISAAddFamilyReferenceValues.values in HV.
 rewrite(CPUReferenceValues.at_reference_cut(instruction_effect token_pc token_word)key
  (CPUISAAddFamilyReferenceValues.computed_value token_word)initial ledger index(producer_token p)before HN HB)in HV.
 destruct(computed_value_implies_family _ _ _ HV)as[[rd[rs1[rs2 HD]]]|[rd[rs[imm HD]]]].
 - destruct(original_decode_add_registers _ _ _ _ HD)as[HRD _].
   left;exists rs1,rs2;rewrite HR,HRD;exact HD.
 - destruct(original_decode_addi_fields _ _ _ _ HD)as[_[_[HRD _]]].
   right;exists rs,imm;rewrite HR,HRD;exact HD.
Qed.

Theorem reference_head_effect initial prefix before(p:@Producer Token)rest extra after:
 EffectChain(instruction_effect token_pc token_word)initial prefix before ->
 NoDup(map key(prefix++producer_token p::rest++extra)) ->
 FamilyCompatible initial(prefix++producer_token p::rest++extra)p ->
 instruction_effect token_pc token_word(producer_token p)before=Some after ->
 ISAProjectedRegisterEffects before after(operations p).
Proof.
 intros HC HN[HD HV]HS.
 pose proof(prefix_key_fresh key prefix(producer_token p)(rest++extra)HN)as HF.
 unfold CPUISAAddFamilyReferenceValues.values in HV.
 rewrite(CPUReferenceValues.committed_prefix(instruction_effect token_pc token_word)key
  (CPUISAAddFamilyReferenceValues.computed_value token_word)initial prefix before(producer_token p::rest++extra)
  (producer_token p)HC HF),CPUReferenceValues.at_head in HV.
 destruct HD as[[rs1[rs2 HD]]|[rs[imm HD]]].
 - destruct(token_execute token_pc token_word(producer_token p)before after _ HS HD)as[middle[HE HEnd]].
   destruct(original_add_effect before middle(producer_rd p)rs1 rs2 HE)as[x[y[HX[HY HEffect]]]].
   unfold CPUISAAddFamilyReferenceValues.computed_value in HV;rewrite HD,HX,HY in HV;injection HV as HV.
   assert(HOps:operations p=register_operations(producer_rd p)(Utility.add x y)).
   { unfold operations,register_operations;destruct(Z.eqb(producer_rd p)0);[reflexivity|].
     exact(f_equal(fun value=>[WriteLane(producer_rd p)value])(eq_sym HV)). }
   rewrite HOps;intros address HA;unfold ISAView;rewrite(end_cycle_register_frame middle after HEnd).
   exact(HEffect address HA).
 - destruct(token_execute token_pc token_word(producer_token p)before after _ HS HD)as[middle[HE HEnd]].
   destruct(original_addi_effect before middle(producer_rd p)rs imm HE)as[x[HX HEffect]].
   unfold CPUISAAddFamilyReferenceValues.computed_value in HV;rewrite HD,HX in HV;injection HV as HV.
   assert(HOps:operations p=register_operations(producer_rd p)(Utility.add x(Utility.ZToReg imm))).
   { unfold operations,register_operations;destruct(Z.eqb(producer_rd p)0);[reflexivity|].
     exact(f_equal(fun value=>[WriteLane(producer_rd p)value])(eq_sym HV)). }
   rewrite HOps;intros address HA;unfold ISAView;rewrite(end_cycle_register_frame middle after HEnd).
   exact(HEffect address HA).
Qed.

Theorem certify_reference_producers initial prefix before producers extra final:
 EffectChain(instruction_effect token_pc token_word)initial prefix before ->
 NoDup(map key(prefix++map producer_token producers++extra)) ->
 Forall(FamilyCompatible initial(prefix++map producer_token producers++extra))producers ->
 EffectChain(instruction_effect token_pc token_word)before(map producer_token producers)final ->
 CertifiedBatches token_pc token_word before(map batch producers)final.
Proof.
 revert prefix before;induction producers as[|p rest IH];intros prefix before HP HN HV HC.
 - cbn[map]in HC|-*;inversion HC;constructor.
 - inversion HV as[|head tail HHead HRest];subst.
   cbn[map]in HC;inversion HC as[|a t next ts c HE HChain];subst.
   cbn[map batch];econstructor.
   + exact HE.
   + exact(reference_head_effect initial prefix before p(map producer_token rest)extra next HP HN HHead HE).
   + apply(IH(prefix++[producer_token p])next).
     * eapply chain_append;[exact HP|];econstructor;[exact HE|constructor].
     * rewrite <-app_assoc;cbn[app];exact HN.
     * rewrite <-app_assoc;cbn[app];exact HRest.
     * exact HChain.
Qed.

Theorem automatic_ready_batches initial prefix before producers extra final address:
 EffectChain(instruction_effect token_pc token_word)initial prefix before ->
 NoDup(map key(prefix++map producer_token producers++extra)) ->
 Forall(FamilyCompatible initial(prefix++map producer_token producers++extra))producers ->
 EffectChain(instruction_effect token_pc token_word)before(map producer_token producers)final ->
 exists batches,map fst batches=map producer_token producers /\
 CertifiedBatches token_pc token_word before batches final /\
 Forall2 SlotRelated(compact(map ready_slot producers))(batch_writes 32 address batches).
Proof.
 intros HP HN HV HC;exists(map batch producers);split.
 - rewrite map_map;apply map_ext;intros [];reflexivity.
 - split;[exact(certify_reference_producers initial prefix before producers extra final HP HN HV HC)|].
   apply summaries_slots_related.
Qed.
End ISA.
End CPUReferenceAddFamilyProducers.
Print Assumptions CPUReferenceAddFamilyProducers.computed_value_implies_family.
Print Assumptions CPUReferenceAddFamilyProducers.reference_result_family_compatible.
Print Assumptions CPUReferenceAddFamilyProducers.reference_head_effect.
Print Assumptions CPUReferenceAddFamilyProducers.certify_reference_producers.
Print Assumptions CPUReferenceAddFamilyProducers.automatic_ready_batches.
