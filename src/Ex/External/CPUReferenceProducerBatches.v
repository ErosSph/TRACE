(** Build original-ISA batches and ready-slot proofs from pointwise reference
    results. This is not a CPU invariant and does not assume batch correctness. *)
From Coq Require Import List ZArith Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRegisterBank Lang.ExtendedSVWordInvariant
 Ex.External.CPUGeneratedJointTemplate Ex.External.CPUOriginalISAReference
 Ex.External.CPUISAAddReferenceValues Ex.External.CPUReferenceValues Ex.External.CPUReferenceCuts
 Ex.External.CPUInstructionFields Ex.External.CPUISAAddOperandFields
 Ex.External.CPUISAInstructionExecution Ex.External.CPUISAExecutionEffects
 Ex.External.CPUISARegisterUpdate Ex.External.CPUISAOwnedEffects
 Ex.External.CPUISAReadyBatches Ex.External.CPUReadyOperand Ex.External.CPUReadySlotCompaction
 Ex.External.CPUComputedReferenceCut Ex.External.CPUComputedResultCut
 Ex.External.CPURegisterEffectRelation Ex.RvCore.FormalSpec Ex.RvCore.Machine
 coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte
 riscv.Utility.Utility.
Import ListNotations ExtendedSV ExtendedSVRegisterBank ExtendedSVWordInvariant
 CPUGeneratedJointTemplate CPUOriginalISAReference CPUISAInstructionExecution CPUISAExecutionEffects
 CPUISARegisterUpdate CPUISAOwnedEffects CPUISAReadyBatches CPUReadyOperand CPUReadySlotCompaction
 CPURegisterEffectRelation CPUInstructionFields CPUISAAddOperandFields CPUReferenceCuts.
Module CPUReferenceProducerBatches.

(** Extending the ledger cannot change a cut already found before its end.
    Neither the newly fetched instructions nor their execution are assumed. *)
Lemma lookup_before_append {Architecture Token:Type}
 (effect:Token->Architecture->option Architecture)
 (same:forall x y:Token,{x=y}+{x<>y}) wanted pending initial index before extra:
 CPUComputedReferenceCut.lookup_before effect same wanted initial pending=Some(index,before) ->
 CPUComputedReferenceCut.lookup_before effect same wanted initial(pending++extra)=Some(index,before).
Proof.
 revert initial index before;induction pending as[|head rest IH];intros initial index before;
 cbn[app CPUComputedReferenceCut.lookup_before];[discriminate|].
 destruct(same wanted head);[intro H;exact H|].
 destruct(effect head initial)as[next|];[|discriminate].
 destruct(CPUComputedReferenceCut.lookup_before effect same wanted next rest)as[[pos state]|]eqn:HL;
 [|discriminate].
 intro H;inversion H;subst index before;rewrite(IH next pos state HL);reflexivity.
Qed.

Theorem computed_result_append {Architecture Token:Type}
 (effect:Token->Architecture->option Architecture)
 (same:forall x y:Token,{x=y}+{x<>y}) projection wanted initial pending extra:
 CPUComputedResultCut.computed_result_R effect same projection wanted initial pending ->
 CPUComputedResultCut.computed_result_R effect same projection wanted initial(pending++extra).
Proof.
 intro HR;destruct(proj1(CPUComputedResultCut.computed_result_R_exact effect same projection wanted initial pending)HR)
 as[index[before[after[HL[HE HP]]]]].
 apply(proj2(CPUComputedResultCut.computed_result_R_exact effect same projection wanted initial(pending++extra))).
 exists index,before,after;split;[exact(lookup_before_append effect same wanted pending initial index before extra HL)|].
 exact(conj HE HP).
Qed.

Lemma compact_append(left right:list(@Slot Z)):
 compact(left++right)=compact left++compact right.
Proof. induction left as[|s left IH];[reflexivity|].
 destruct s as[[rd value]|];cbn[compact app];now rewrite IH. Qed.

Lemma before_prefix {Architecture Token:Type}(effect:Token->Architecture->option Architecture)
 initial prefix before token rest:
 EffectChain effect initial prefix before ->
 BeforeToken effect initial(prefix++token::rest)(length prefix)token before.
Proof.
 intro HC;split.
 - rewrite nth_error_app2 by lia;rewrite Nat.sub_diag;reflexivity.
 - split;[rewrite app_length;cbn;lia|].
   rewrite firstn_app,firstn_all,Nat.sub_diag;cbn;rewrite app_nil_r;exact HC.
Qed.

Lemma prefix_key_fresh {T:Type}(key:T->nat)prefix token rest:
 NoDup(map key(prefix++token::rest)) ->Forall(fun earlier=>key earlier<>key token)prefix.
Proof. induction prefix as[|first prefix IH];intro HN;[constructor|].
 cbn[app map]in HN;inversion HN as[|head tail HNot HRest];subst;constructor.
 - intro HE;apply HNot;rewrite HE,map_app;apply in_or_app;right;now left.
 - exact(IH HRest). Qed.

Section Summaries.
Context {Token:Type}.
Record Producer:Type:={producer_token:Token;producer_rd:Z;producer_value:Z}.
Definition operations(p:Producer):list BankOperation:=
 if Z.eqb(producer_rd p)0 then[]else[WriteLane(producer_rd p)(producer_value p)].
Definition batch(p:Producer):Token*list BankOperation:=(producer_token p,operations p).
Definition ready_slot(p:Producer):@Slot Z:=
 if Z.eqb(producer_rd p)0 then None else Some(producer_rd p,Some(norm 32(producer_value p))).

(** Unknown identity in a VALID slot is failure, not an empty producer. *)
Definition collect valid(tag:option Token)rd value:option(list Producer):=
 if Z.eqb valid 0 then Some[]else match tag with
 |Some token=>Some[Build_Producer token rd value]|None=>None end.
Definition token_view valid(tag:option Token):list Token:=
 if Z.eqb valid 0 then[]else match tag with Some token=>[token]|None=>[]end.
Lemma collect_exists valid tag rd value:
 (valid<>0%Z ->exists token,tag=Some token) ->exists producers,collect valid tag rd value=Some producers.
Proof.
 intro HC;unfold collect;destruct(Z.eqb valid 0)eqn:HV;[eexists;reflexivity|].
 apply Z.eqb_neq in HV;destruct(HC HV)as[token HT];rewrite HT;eexists;reflexivity.
Qed.
Lemma collect_tokens valid tag rd value producers:
 collect valid tag rd value=Some producers ->map producer_token producers=token_view valid tag.
Proof.
 unfold collect,token_view;destruct(Z.eqb valid 0);[|destruct tag];intro H;inversion H;reflexivity.
Qed.
Lemma collect_forall(P:Producer->Prop)valid tag rd value producers:
 collect valid tag rd value=Some producers ->
 (forall token,valid<>0%Z ->tag=Some token ->P(Build_Producer token rd value)) ->Forall P producers.
Proof.
 unfold collect;destruct(Z.eqb valid 0)eqn:HV;[|destruct tag as[token|]];
 intros HC HP;try discriminate;inversion HC;subst;[constructor|].
 constructor;[apply(HP token);[now apply Z.eqb_neq|reflexivity]|constructor].
Qed.
Lemma collect_slot valid tag rd value producers(actual:@Slot Z):
 collect valid tag rd value=Some producers ->
 (valid=0%Z ->actual=None) ->
 (forall token,valid<>0%Z ->tag=Some token ->actual=ready_slot(Build_Producer token rd value)) ->
 compact[actual]=compact(map ready_slot producers).
Proof.
 unfold collect;destruct(Z.eqb valid 0)eqn:HV;[|destruct tag as[token|]];
 intros HC HEmpty HActive;try discriminate;inversion HC;subst.
 - rewrite(HEmpty ltac:(now apply Z.eqb_eq));reflexivity.
 - rewrite(HActive token ltac:(now apply Z.eqb_neq)eq_refl);reflexivity.
Qed.

Theorem summaries_slots_related address producers:
 Forall2 SlotRelated(compact(map ready_slot producers))(batch_writes 32 address(map batch producers)).
Proof.
 induction producers as[|p rest IH];[constructor|].
 unfold batch at 1;cbn[map batch_writes flat_map snd];unfold operations,ready_slot.
 destruct(Z.eqb(producer_rd p)0);cbn[compact map app operation_write];[exact IH|].
 constructor;[split;reflexivity|exact IH].
Qed.
End Summaries.

Section ISA.
Context {word:Interface.word 32}{BW:Bitwidth 32}{Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}{registers_ok:map.ok Registers}{Token:Type}.
Variables token_pc token_word:Token->Z.
Variable key:Token->nat.

Definition AddCompatible(initial:FormalSpec.State)ledger(p:@Producer Token):Prop:=
 (exists rs1 rs2,Decode.decode Decode.RV32I(token_word(producer_token p))=
  Decode.IInstruction(Decode.Add(producer_rd p)rs1 rs2)) /\
 CPUISAAddReferenceValues.values token_pc token_word key initial ledger(producer_token p)=Some(producer_value p).

Lemma add_value_implies_add token before value:
 CPUISAAddReferenceValues.add_value token_word token before=Some value ->
 exists rd rs1 rs2,Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Add rd rs1 rs2).
Proof. unfold CPUISAAddReferenceValues.add_value;destruct(Decode.decode Decode.RV32I(token_word token))eqn:HD;
 try discriminate;destruct iInstruction;try discriminate;intros;repeat eexists;exact HD. Qed.

Theorem reference_result_add_compatible initial ledger frontier(p:@Producer Token):
 NoDup(map key ledger) ->EffectChain(instruction_effect token_pc token_word)initial ledger frontier ->
 In(producer_token p)ledger ->producer_rd p=field_reference(token_word(producer_token p))Rd ->
 CPUISAAddReferenceValues.values token_pc token_word key initial ledger(producer_token p)=Some(producer_value p) ->
 AddCompatible initial ledger p.
Proof.
 intros HN HC HI HR HV;split;[|exact HV].
 destruct(In_nth_error ledger(producer_token p)HI)as[index HT].
 destruct(token_before_exists(instruction_effect token_pc token_word)initial ledger frontier index(producer_token p)HC HT)as[before HB].
 unfold CPUISAAddReferenceValues.values in HV.
 rewrite(CPUReferenceValues.at_reference_cut(instruction_effect token_pc token_word)key
   (CPUISAAddReferenceValues.add_value token_word)initial ledger index(producer_token p)before HN HB)in HV.
 destruct(add_value_implies_add _ _ _ HV)as[rd[rs1[rs2 HD]]].
 destruct(original_decode_add_registers _ _ _ _ HD)as[HRD _].
 exists rs1,rs2;rewrite HR,HRD;exact HD.
Qed.

Theorem reference_head_effect initial prefix before(p:@Producer Token)rest extra after:
 EffectChain(instruction_effect token_pc token_word)initial prefix before ->
 NoDup(map key(prefix++producer_token p::rest++extra)) ->
 AddCompatible initial(prefix++producer_token p::rest++extra)p ->
 instruction_effect token_pc token_word(producer_token p)before=Some after ->
 ISAProjectedRegisterEffects before after(operations p).
Proof.
 intros HC HN[[rs1[rs2 HD]]HV]HS.
 pose proof(prefix_key_fresh key prefix(producer_token p)(rest++extra)HN)as HF.
 unfold CPUISAAddReferenceValues.values in HV.
 rewrite(CPUReferenceValues.committed_prefix(instruction_effect token_pc token_word)key
  (CPUISAAddReferenceValues.add_value token_word)initial prefix before(producer_token p::rest++extra)
  (producer_token p)HC HF),CPUReferenceValues.at_head in HV.
 destruct(token_execute token_pc token_word(producer_token p)before after _ HS HD)as[middle[HE HEnd]].
 destruct(original_add_effect before middle(producer_rd p)rs1 rs2 HE)as[x[y[HX[HY HEffect]]]].
 unfold CPUISAAddReferenceValues.add_value in HV;rewrite HD,HX,HY in HV;injection HV as HV.
 assert(HOps:operations p=register_operations(producer_rd p)(Utility.add x y)).
 { unfold operations,register_operations;destruct(Z.eqb(producer_rd p)0);[reflexivity|].
   exact(f_equal(fun value=>[WriteLane(producer_rd p)value])(eq_sym HV)). }
 rewrite HOps;intros address HA;unfold ISAView;rewrite(end_cycle_register_frame middle after HEnd).
 exact(HEffect address HA).
Qed.

Theorem certify_reference_producers initial prefix before producers extra final:
 EffectChain(instruction_effect token_pc token_word)initial prefix before ->
 NoDup(map key(prefix++map producer_token producers++extra)) ->
 Forall(AddCompatible initial(prefix++map producer_token producers++extra))producers ->
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
 Forall(AddCompatible initial(prefix++map producer_token producers++extra))producers ->
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
End CPUReferenceProducerBatches.
Print Assumptions CPUReferenceProducerBatches.lookup_before_append.
Print Assumptions CPUReferenceProducerBatches.computed_result_append.
Print Assumptions CPUReferenceProducerBatches.prefix_key_fresh.
Print Assumptions CPUReferenceProducerBatches.compact_append.
Print Assumptions CPUReferenceProducerBatches.before_prefix.
Print Assumptions CPUReferenceProducerBatches.summaries_slots_related.
Print Assumptions CPUReferenceProducerBatches.collect_exists.
Print Assumptions CPUReferenceProducerBatches.collect_tokens.
Print Assumptions CPUReferenceProducerBatches.collect_forall.
Print Assumptions CPUReferenceProducerBatches.collect_slot.
Print Assumptions CPUReferenceProducerBatches.add_value_implies_add.
Print Assumptions CPUReferenceProducerBatches.reference_result_add_compatible.
Print Assumptions CPUReferenceProducerBatches.reference_head_effect.
Print Assumptions CPUReferenceProducerBatches.certify_reference_producers.
Print Assumptions CPUReferenceProducerBatches.automatic_ready_batches.
