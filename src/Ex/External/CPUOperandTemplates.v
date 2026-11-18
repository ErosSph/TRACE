From Coq Require Import List ZArith Bool.
Import ListNotations.

(** A reusable, symbolic forwarding specification. Entries are ordered youngest
    first; the RTL adapter must separately prove this order and the mux binding.
    This file deliberately contains no CPU-specific signal names. *)
Module CPUOperandTemplates.
Record PendingWrite := {
  destination : nat; value : Z; valid : bool; killed : bool
}.
Definition eligible (rs : nat) (w : PendingWrite) : bool :=
  valid w && negb (killed w) && Nat.eqb rs (destination w).
Fixpoint forwarded (rs : nat) (pending : list PendingWrite)
    (rf : nat -> Z) : Z :=
  if Nat.eqb rs 0 then 0 else
  match pending with
  | [] => rf rs
  | w :: ws => if eligible rs w then value w else forwarded rs ws rf
  end.

Theorem x0_never_forwarded : forall pending rf,
  forwarded 0 pending rf = 0%Z.
Proof. destruct pending; reflexivity. Qed.

Theorem youngest_matching_write : forall rs w ws rf,
  rs <> 0 -> eligible rs w = true ->
  forwarded rs (w :: ws) rf = value w.
Proof.
  intros rs w ws rf Hrs Hw. simpl.
  destruct (Nat.eqb rs 0) eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - rewrite Hw. reflexivity.
Qed.

Theorem skip_invalid_or_killed : forall rs w ws rf,
  eligible rs w = false ->
  forwarded rs (w :: ws) rf = forwarded rs ws rf.
Proof.
  intros rs w ws rf Hw. simpl. destruct (Nat.eqb rs 0) eqn:E.
  - destruct ws; simpl; rewrite E; reflexivity.
  - rewrite Hw. reflexivity.
Qed.

Theorem rf_fallback : forall rs pending rf,
  rs <> 0 -> Forall (fun w => eligible rs w = false) pending ->
  forwarded rs pending rf = rf rs.
Proof.
  intros rs pending rf Hrs Hnone. induction Hnone.
  - simpl. destruct (Nat.eqb rs 0) eqn:E; auto.
    apply Nat.eqb_eq in E. contradiction.
  - rewrite skip_invalid_or_killed by assumption. exact IHHnone.
Qed.

(** Certificate for a concrete priority index. No promise of operand freshness:
    that requires the separately checked program-order/token invariant. *)
Fixpoint first_match (rs : nat) (pending : list PendingWrite) : option nat :=
  match pending with
  | [] => None
  | w :: ws => if eligible rs w then Some 0
               else option_map S (first_match rs ws)
  end.
Theorem first_match_sound : forall pending rs k rf w,
  rs <> 0 -> first_match rs pending = Some k ->
  nth_error pending k = Some w -> forwarded rs pending rf = value w.
Proof.
  induction pending as [|a pending IH]; intros rs k rf w Hrs Hmatch Hnth.
  - discriminate Hmatch.
  - simpl in Hmatch. destruct (eligible rs a) eqn:E.
    + inversion Hmatch; subst k. simpl in Hnth. inversion Hnth; subst w.
      apply youngest_matching_write; assumption.
    + rewrite skip_invalid_or_killed by exact E.
      destruct (first_match rs pending) as [j|] eqn:J; simpl in Hmatch;
        try discriminate.
      inversion Hmatch; subst k. simpl in Hnth.
      eapply IH; eauto.
Qed.
End CPUOperandTemplates.
Print Assumptions CPUOperandTemplates.first_match_sound.
