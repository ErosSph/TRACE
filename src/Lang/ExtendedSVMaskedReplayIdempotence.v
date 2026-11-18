(** Replaying a captured update list twice has the same effect when repeated
    writes to a root use the same slice. Values MAY differ: last-write priority
    is preserved. No commutativity between overrides of one root is assumed. *)
From Coq Require Import List PeanoNat.
Require Import Lang.ExtendedSV Lang.ExtendedSVSameSliceReplay.
Import ExtendedSV ExtendedSVSameSliceReplay ListNotations.
Module ExtendedSVMaskedReplayIdempotence.
Definition SameRootSameMask updates:=forall first second,
 In first updates->In second updates->update_signal first=update_signal second->
 update_offset first=update_offset second/\update_width first=update_width second.
Lemma original_updates_absorb_old_write update updates:
 (forall v,In v updates->update_signal v=update_signal update->
  update_offset v=update_offset update/\update_width v=update_width update)->
 (exists v,In v updates/\update_signal v=update_signal update)->forall state,
 apply_updates(apply_update state update)updates=apply_updates state updates.
Proof.
 induction updates as[|u us IH];intros HM HE state;[destruct HE as[v[[] _]]|].
 cbn. destruct(Nat.eq_dec(update_signal u)(update_signal update))as[HR|HR].
 - destruct(HM u(or_introl eq_refl)HR)as[HO HW].
   rewrite(same_slice_overwrite(update_signal update)(update_offset update)(update_width update)
    update u state);[reflexivity|repeat split;reflexivity|repeat split;assumption].
 - rewrite(apply_update_commute state update u)by congruence.
   apply IH.
   + intros v HV. apply HM. now right.
   + destruct HE as[v[HV HRv]]. destruct HV as[<-|HV];[contradiction|].
     exists v. now split.
Qed.
Lemma original_prefix_absorbed_by_last_write_list prefix suffix:
 (forall u,In u prefix->forall v,In v suffix->update_signal v=update_signal u->
  update_offset v=update_offset u/\update_width v=update_width u)->
 (forall u,In u prefix->exists v,In v suffix/\update_signal v=update_signal u)->forall state,
 apply_updates(apply_updates state prefix)suffix=apply_updates state suffix.
Proof.
 induction prefix as[|u us IH];intros HM HE state;cbn;[reflexivity|].
 rewrite IH.
 - apply original_updates_absorb_old_write.
   + apply HM. now left.
   + apply HE. now left.
 - intros v HV. apply HM. now right.
 - intros v HV. apply HE. now right.
Qed.
Theorem original_mask_consistent_replay_is_idempotent updates:
 SameRootSameMask updates->forall state,
 apply_updates(apply_updates state updates)updates=apply_updates state updates.
Proof.
 intro H. apply original_prefix_absorbed_by_last_write_list.
 - intros u HU v HV HR. apply H;[exact HV|exact HU|exact HR].
 - intros u HU. exists u. now split.
Qed.
End ExtendedSVMaskedReplayIdempotence.
Print Assumptions ExtendedSVMaskedReplayIdempotence.original_mask_consistent_replay_is_idempotent.
