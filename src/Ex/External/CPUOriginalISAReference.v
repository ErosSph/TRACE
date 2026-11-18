(** Pending reference execution is the original run1, with token identity
    checked against the original fetch. It is not a replacement ISA. *)
From Coq Require Import ZArith List.
Require Import Ex.RvCore.FormalSpec Ex.External.CPUGeneratedJointTemplate
 Ex.External.CPUReferenceCuts coqutil.Map.Interface coqutil.Word.Interface
 coqutil.Word.Bitwidth coqutil.Byte riscv.Utility.MkMachineWidth
 riscv.Spec.Machine riscv.Spec.Decode riscv.Utility.Utility.
Import CPUGeneratedJointTemplate CPUReferenceCuts.
Local Open Scope Z_scope.
Module CPUOriginalISAReference.
Section Reference.
Context {word:Interface.word 32}{BW:Bitwidth 32}{MW:MachineWidth word}.
Context {Registers:map.map Decode.Register word}{Mem:map.map word byte}.
Context {Token:Type}.
Variable token_pc token_word:Token->Z.

Definition fetched_word (a:FormalSpec.State) :=
 fst (Machine.loadWord Machine.Fetch (getPc a) a).
Definition original_step (_:Token)(a:FormalSpec.State):option FormalSpec.State:=
 match FormalSpec.run1 a with (Some tt,a')=>Some a'|_=>None end.
Definition instruction_effect (t:Token)(a:FormalSpec.State):option FormalSpec.State:=
 if token_pc t =? word.unsigned(getPc a) then
 match fetched_word a with
 | None=>None
 | Some bytes=>if token_word t =? LittleEndian.combine 4 bytes
   then original_step t a else None
 end else None.

Theorem instruction_effect_sound t a a':instruction_effect t a=Some a' ->
 token_pc t=word.unsigned(getPc a) /\
 (exists bytes,fetched_word a=Some bytes /\ token_word t=LittleEndian.combine 4 bytes) /\
 FormalSpec.run1 a=(Some tt,a').
Proof.
 unfold instruction_effect,original_step.
 destruct(token_pc t =? word.unsigned(getPc a))eqn:HP;[|discriminate].
 destruct(fetched_word a)as[bytes|]eqn:HF;[|discriminate].
 destruct(token_word t =? LittleEndian.combine 4 bytes)eqn:HW;[|discriminate].
 destruct(FormalSpec.run1 a)as[[[]|]after]eqn:HR;[|discriminate].
 intro H;inversion H;subst after.
 apply Z.eqb_eq in HP;apply Z.eqb_eq in HW.
 split;[exact HP|]. split;[exists bytes;split;[reflexivity|exact HW]|reflexivity].
Qed.

Theorem instruction_effect_complete t a a' bytes:
 token_pc t=word.unsigned(getPc a) ->fetched_word a=Some bytes ->
 token_word t=LittleEndian.combine 4 bytes ->FormalSpec.run1 a=(Some tt,a') ->
 instruction_effect t a=Some a'.
Proof.
 intros HP HF HW HR. unfold instruction_effect,original_step.
 rewrite HP,Z.eqb_refl,HF,HW,Z.eqb_refl,HR. reflexivity.
Qed.

Theorem wrong_pc_rejected t a:
 token_pc t<>word.unsigned(getPc a) ->instruction_effect t a=None.
Proof.
 intro H. unfold instruction_effect.
 destruct(token_pc t =? word.unsigned(getPc a))eqn:HE;[|reflexivity].
 apply Z.eqb_eq in HE;contradiction.
Qed.

Theorem wrong_word_rejected t a bytes:
 fetched_word a=Some bytes -> token_word t<>LittleEndian.combine 4 bytes ->
 instruction_effect t a=None.
Proof.
 intros HF H. unfold instruction_effect.
 destruct(token_pc t =? word.unsigned(getPc a));[|reflexivity].
 rewrite HF. destruct(token_word t =? LittleEndian.combine 4 bytes)eqn:HE;[|reflexivity].
 apply Z.eqb_eq in HE;contradiction.
Qed.

Theorem chain_is_original_execution a pending final:
 EffectChain instruction_effect a pending final ->
 EffectChain original_step a pending final.
Proof.
 intro H;induction H;[constructor|]. econstructor;[|exact IHEffectChain].
 unfold original_step. rewrite(proj2(proj2(instruction_effect_sound _ _ _ H))). reflexivity.
Qed.

Definition BeforeInstruction := BeforeToken instruction_effect.
Theorem reference_state_unique a pending index t before other:
 BeforeInstruction a pending index t before ->
 BeforeInstruction a pending index t other ->before=other.
Proof. apply(fields_cannot_choose_different_states instruction_effect). Qed.
End Reference.
End CPUOriginalISAReference.
Print Assumptions CPUOriginalISAReference.instruction_effect_sound.
Print Assumptions CPUOriginalISAReference.instruction_effect_complete.
Print Assumptions CPUOriginalISAReference.chain_is_original_execution.
Print Assumptions CPUOriginalISAReference.reference_state_unique.
Print Assumptions CPUOriginalISAReference.wrong_pc_rejected.
Print Assumptions CPUOriginalISAReference.wrong_word_rejected.
