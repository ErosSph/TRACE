(** Reference states are obtained from the actual pending prefix, not chosen
    independently per hardware field. No CPU invariant is imported. *)
From Coq Require Import List Arith Lia.
Require Import Ex.External.CPUGeneratedJointTemplate.
Import ListNotations CPUGeneratedJointTemplate.
Module CPUReferenceCuts.
Section Cuts.
Context {Architecture Token : Type}.
Variable effect : Token -> Architecture -> option Architecture.

Definition AtCut initial pending index before : Prop :=
 (index <= length pending)%nat /\
 EffectChain effect initial (firstn index pending) before.

Theorem cut_exists initial pending frontier index :
 EffectChain effect initial pending frontier ->
 (index <= length pending)%nat -> exists before, AtCut initial pending index before.
Proof.
 intros HC HI.
 pose proof (firstn_skipn index pending) as HE.
 rewrite <- HE in HC.
 destruct (chain_split effect (firstn index pending) initial (skipn index pending) frontier HC)
 as [before [HP HS]].
 exists before;split;assumption.
Qed.

Theorem cut_unique initial pending index first second :
 AtCut initial pending index first -> AtCut initial pending index second -> first=second.
Proof. intros [_ HF] [_ HS];eapply chain_deterministic; eassumption. Qed.

Definition BeforeToken initial pending index token before : Prop :=
 nth_error pending index=Some token /\ AtCut initial pending index before.

Theorem token_before_exists initial pending frontier index token :
 EffectChain effect initial pending frontier -> nth_error pending index=Some token ->
 exists before, BeforeToken initial pending index token before.
Proof.
 intros HC HT.
 assert (HI:(index < length pending)%nat).
 { apply nth_error_Some;rewrite HT;discriminate. }
 destruct (cut_exists initial pending frontier index HC ltac:(lia)) as [before HP].
 exists before;split;assumption.
Qed.

Definition FieldAtToken {Value:Type} (project:Architecture->Value)
 initial pending index token value : Prop :=
 exists before, BeforeToken initial pending index token before /\ value=project before.

Theorem field_uses_same_cut {Value:Type}(project:Architecture->Value)
 initial pending index token value before :
 FieldAtToken project initial pending index token value ->
 BeforeToken initial pending index token before -> value=project before.
Proof.
 intros [other [[HT HO] HV]] [HT' HB].
 assert (other=before) by (eapply cut_unique;eassumption).
 now subst other.
Qed.

Theorem fields_cannot_choose_different_states initial pending index token left right :
 BeforeToken initial pending index token left ->
 BeforeToken initial pending index token right ->left=right.
Proof. intros [_ HL] [_ HR];eapply cut_unique;eassumption. Qed.

Theorem empty_pending_has_no_token initial index token before :
 ~ BeforeToken initial [] index token before.
Proof. intros [HT _];destruct index;discriminate. Qed.
End Cuts.
Print Assumptions cut_exists.
Print Assumptions cut_unique.
Print Assumptions token_before_exists.
Print Assumptions field_uses_same_cut.
Print Assumptions fields_cannot_choose_different_states.
Print Assumptions empty_pending_has_no_token.
End CPUReferenceCuts.
