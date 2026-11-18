(** Priority-preserving last-write compression of captured updates to exactly
    one slice. Unlike OrderedProducerCertificate, this permits overrides of
    the same root within a process and proves their ORIGINAL execution result. *)
From Coq Require Import List.
Require Import Lang.ExtendedSV Lang.ExtendedSVAssignment.
Import ExtendedSV ExtendedSVAssignment ListNotations.
Module ExtendedSVSameSliceReplay.
Definition SameSlice root offset width update:=
 update_signal update=root /\ update_offset update=offset /\ update_width update=width.
Lemma same_slice_overwrite root offset width first second state:
 SameSlice root offset width first->SameSlice root offset width second->
 apply_update(apply_update state first)second=apply_update state second.
Proof.
 destruct first as[r1 o1 w1 v1],second as[r2 o2 w2 v2].
 unfold SameSlice;cbn;intros[E1[O1 W1]][E2[O2 W2]]. subst.
 unfold apply_update;cbn.
 rewrite read_signal_write_same,write_slice_overwrite,write_signal_write_same. reflexivity.
Qed.
Fixpoint final_update (first:Update) (rest:list Update):Update:=match rest with
 |[]=>first|u::us=>final_update u us end.
Theorem original_captured_same_slice_chain_is_last_write root offset width rest:
 Forall(SameSlice root offset width)rest->forall first state,
 SameSlice root offset width first->
 apply_updates state(first::rest)=apply_update state(final_update first rest).
Proof.
 intro H. induction H as[|u us HU HT IH];intros first state HF;cbn;[reflexivity|].
 rewrite (same_slice_overwrite root offset width first u state HF HU).
 apply IH. exact HU.
Qed.
Lemma final_update_slice root offset width rest:
 Forall(SameSlice root offset width)rest->forall first,
 SameSlice root offset width first->SameSlice root offset width(final_update first rest).
Proof. intro H. induction H;intros first HF;cbn;[exact HF|now apply IHForall]. Qed.
End ExtendedSVSameSliceReplay.
Print Assumptions ExtendedSVSameSliceReplay.original_captured_same_slice_chain_is_last_write.
