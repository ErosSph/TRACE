(** Certified effects must cover exactly the older pending prefix. *)
From Coq Require Import List ZArith Lia.
Require Import Ex.External.CPUReferenceCuts Ex.External.CPUGeneratedJointTemplate
 Ex.External.CPUISAOwnedEffects Ex.External.CPUOriginalISAReference
 Ex.External.CPUISAOperandValue Ex.External.CPURegisterEffectRelation
 Ex.External.CPUOwnedOperandReference Ex.RvCore.FormalSpec Ex.RvCore.Machine
 coqutil.Word.Interface coqutil.Map.Interface coqutil.Word.Bitwidth coqutil.Byte
 riscv.Utility.Utility.
Import CPUReferenceCuts CPUGeneratedJointTemplate CPUISAOwnedEffects
 CPUOriginalISAReference CPUISAOperandValue CPURegisterEffectRelation
 CPUOwnedOperandReference.
Local Open Scope Z_scope.
Module CPUISAOperandCut.
Section Prefix.
Context {word:Interface.word 32}{BW:Bitwidth 32}
 {Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}{Token:Type}.
Variable token_pc token_word:Token->Z.

Theorem certified_prefix_before_token initial pending index token batches before:
 CertifiedBatches token_pc token_word initial batches before ->
 map fst batches=firstn index pending ->nth_error pending index=Some token ->
 BeforeToken(instruction_effect token_pc token_word)initial pending index token before.
Proof.
 intros HC HP HT;split;[exact HT|];split.
 - assert(HL:(index<length pending)%nat).
   { apply nth_error_Some;rewrite HT;discriminate. } lia.
 - rewrite <-HP;exact(batches_original_chain token_pc token_word initial batches before HC).
Qed.

Theorem operand_at_exact_pending_cut initial pending index token batches before
 reference after address value:
 CertifiedBatches token_pc token_word initial batches before ->
 map fst batches=firstn index pending ->
 BeforeToken(instruction_effect token_pc token_word)initial pending index token reference ->
 0<=address<32 ->Machine.getRegister address reference=(Some value,after) ->
 word.unsigned value=
 if address=?0 then 0 else owner_value 32(ISAView initial)batches address.
Proof.
 intros HC HP HB HA HR.
 assert(HS:before=reference).
 { eapply fields_cannot_choose_different_states;[|exact HB].
   eapply certified_prefix_before_token;[exact HC|exact HP|exact(proj1 HB)]. }
 subst reference;eapply read_after_certified_prefix;eassumption.
Qed.
End Prefix.
End CPUISAOperandCut.
Print Assumptions CPUISAOperandCut.certified_prefix_before_token.
Print Assumptions CPUISAOperandCut.operand_at_exact_pending_cut.
