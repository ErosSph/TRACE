(** Owned register effects certified by the original ISA step, not by RTL
    result guesses. The generator must supply both premises for every token. *)
From Coq Require Import List ZArith Lia.
Require Import Lang.ExtendedSVRegisterBank Ex.RvCore.FormalSpec
 Ex.External.CPURegisterEffectRelation Ex.External.CPUOriginalISAReference
 Ex.External.CPUOwnedOperandReference Ex.External.CPUGeneratedJointTemplate
 coqutil.Word.Interface coqutil.Map.Interface coqutil.Word.Bitwidth coqutil.Byte
 riscv.Utility.Utility.
Import ListNotations ExtendedSVRegisterBank CPURegisterEffectRelation
 CPUOriginalISAReference CPUOwnedOperandReference CPUGeneratedJointTemplate.
Local Open Scope Z_scope.
Module CPUISAOwnedEffects.
Section Certificate.
Context {word:coqutil.Word.Interface.word 32}{BW:Bitwidth 32}{MW:MachineWidth word}
 {Registers:map.map Z word}{Mem:map.map word byte}{Token:Type}.
Variable token_pc token_word:Token->Z.

Inductive CertifiedBatches:FormalSpec.State->list(Token*list BankOperation)->FormalSpec.State->Prop:=
| batches_nil a:CertifiedBatches a [] a
| batches_cons a token middle operations rest final:
 instruction_effect token_pc token_word token a=Some middle ->
 ISAProjectedRegisterEffects a middle operations ->
 CertifiedBatches middle rest final ->
 CertifiedBatches a ((token,operations)::rest) final.

Theorem batches_original_chain a batches final:
 CertifiedBatches a batches final ->
 EffectChain(instruction_effect token_pc token_word)a(map fst batches)final.
Proof. intro H;induction H;cbn;[constructor|econstructor;eauto]. Qed.

Theorem batches_register_effects a batches final:
 CertifiedBatches a batches final ->
 ISAProjectedRegisterEffects a final(flat_map snd batches).
Proof.
 intro H;induction H;cbn.
 - intros i HI;unfold project_x0;destruct(i=?0)eqn:HZ.
   + apply Z.eqb_eq in HZ;subst i;apply isa_view_x0.
   + reflexivity.
 - eapply isa_projected_effects_append;eauto.
Qed.

Theorem batches_operand a batches final address:
 CertifiedBatches a batches final ->0<=address<32 ->
 ISAView final address=
 if address=?0 then 0 else owner_value 32(ISAView a)batches address.
Proof.
 intros HC HA;rewrite(batches_register_effects _ _ _ HC address HA).
 unfold project_x0;destruct(address=?0);[reflexivity|].
 apply flatten_preserves_operand.
Qed.

Theorem selected_owner_is_isa_value a batches final address owner index value:
 CertifiedBatches a batches final ->0<address<32 ->
 latest_owner 32 batches address=Some(WriteOf owner index value) ->
 ISAView final address=value.
Proof.
 intros HC HA HS;rewrite(batches_operand a batches final address HC ltac:(lia)).
 assert(HZ:(address=?0)=false)by(apply Z.eqb_neq;lia).
 rewrite HZ;unfold owner_value;now rewrite HS.
Qed.
End Certificate.
End CPUISAOwnedEffects.
Print Assumptions CPUISAOwnedEffects.batches_original_chain.
Print Assumptions CPUISAOwnedEffects.batches_register_effects.
Print Assumptions CPUISAOwnedEffects.selected_owner_is_isa_value.
