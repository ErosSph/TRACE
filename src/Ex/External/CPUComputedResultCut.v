(** Executable result-state selection. Unlike source selection, this must
    execute the selected instruction successfully. No CPU ownership is assumed. *)
From Coq Require Import List Arith.
Require Import Ex.External.CPUComputedReferenceCut Ex.External.CPUReferenceCuts.
Import CPUComputedReferenceCut CPUReferenceCuts.
Module CPUComputedResultCut.
Section Compute.
Context {Architecture Token:Type}.
Variable effect:Token->Architecture->option Architecture.
Variable same:forall x y:Token,{x=y}+{x<>y}.

Definition lookup_after wanted initial pending
 : option(nat*Architecture*Architecture) :=
 match lookup_before effect same wanted initial pending with
 | None=>None
 | Some(index,before)=>match effect wanted before with
   |None=>None |Some after=>Some(index,before,after) end
 end.

Theorem lookup_after_sound wanted initial pending index before after:
 lookup_after wanted initial pending=Some(index,before,after) ->
 BeforeToken effect initial pending index wanted before /\
 effect wanted before=Some after.
Proof.
 unfold lookup_after.
 destruct(lookup_before effect same wanted initial pending)as[[i b]|]eqn:HB;
 [|discriminate].
 destruct(effect wanted b)as[a|]eqn:HE;[|discriminate].
 intro H;inversion H;subst;split;[eapply lookup_before_sound;exact HB|exact HE].
Qed.

Theorem lookup_after_complete wanted initial pending index before after:
 NoDup pending ->BeforeToken effect initial pending index wanted before ->
 effect wanted before=Some after ->
 lookup_after wanted initial pending=Some(index,before,after).
Proof.
 intros HN HB HE;unfold lookup_after.
 rewrite(lookup_before_complete effect same wanted pending initial index before HN HB).
 now rewrite HE.
Qed.

Definition computed_result_R (projection:Architecture->Architecture->Prop)
 wanted initial pending : Prop :=
 match lookup_after wanted initial pending with
 | None=>False |Some(_,before,after)=>projection before after end.

Theorem computed_result_R_exact projection wanted initial pending:
 computed_result_R projection wanted initial pending <->
 exists index before after,
 lookup_before effect same wanted initial pending=Some(index,before) /\
 effect wanted before=Some after /\ projection before after.
Proof.
 unfold computed_result_R,lookup_after.
 destruct(lookup_before effect same wanted initial pending)as[[i b]|]eqn:HB.
 - destruct(effect wanted b)as[a|]eqn:HE.
   + split.
     * intro H;exists i,b,a;auto.
     * intros[j [c [d [HJ [HD HP]]]]];inversion HJ;subst.
       rewrite HE in HD;inversion HD;subst;exact HP.
   + split;[contradiction|].
     intros[j [c [d [HJ [HD HP]]]]];inversion HJ;subst.
     rewrite HE in HD;discriminate.
 - split;[contradiction|].
   intros[j [c [d [HJ _]]]];discriminate.
Qed.
End Compute.
Print Assumptions lookup_after_sound.
Print Assumptions lookup_after_complete.
Print Assumptions computed_result_R_exact.
End CPUComputedResultCut.

(** Instantiate the algorithm with the unchanged reference model, not a
    separately invented instruction evaluator. *)
From Coq Require Import ZArith.
Require Import Ex.External.CPUOriginalISAReference Ex.RvCore.FormalSpec
 coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte
 riscv.Utility.MkMachineWidth riscv.Utility.Utility riscv.Spec.Decode.
Section OriginalISA.
Context {word:Interface.word 32}{BW:Bitwidth 32}{MW:MachineWidth word}
 {Registers:map.map Decode.Register word}{Mem:map.map word byte}{Token:Type}.
Variable token_pc token_word:Token->Z.
Variable same:forall x y:Token,{x=y}+{x<>y}.

Theorem computed_result_is_original_run1 token initial pending index before after:
 CPUComputedResultCut.lookup_after
 (CPUOriginalISAReference.instruction_effect token_pc token_word)
 same token initial pending=Some(index,before,after) ->
 BeforeToken (CPUOriginalISAReference.instruction_effect token_pc token_word)
 initial pending index token before /\
 token_pc token=word.unsigned(getPc before) /\
 FormalSpec.run1 before=(Some tt,after).
Proof.
 intro H;destruct(CPUComputedResultCut.lookup_after_sound _ _ _ _ _ _ _ _ H)
 as[HB HE].
 destruct(CPUOriginalISAReference.instruction_effect_sound _ _ _ _ _ HE)
 as[HP [_ HR]].
 exact(conj HB(conj HP HR)).
Qed.
End OriginalISA.
Print Assumptions computed_result_is_original_run1.
