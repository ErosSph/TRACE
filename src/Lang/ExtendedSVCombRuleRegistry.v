(** A proof-producing rule registry. Rule selection is executable syntax
    analysis, but only checked rules can inhabit the registry. No CPU names,
    signal IDs, state invariants or ISA conclusions are part of this API. *)
From Coq Require Import List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVCombIdempotence.
Import ListNotations ExtendedSV ExtendedSVCombIdempotence.
Module ExtendedSVCombRuleRegistry.

Record ProducerRule := {
  producer_test : Process -> bool;
  producer_rule_sound : forall p proc,
    (0 < statement_fuel p)%nat -> producer_test proc = true ->
    ProducerIdempotent p proc
}.
Record TransportRule := {
  transport_test : Process -> Process -> bool;
  transport_rule_sound : forall p first later,
    (0 < statement_fuel p)%nat -> transport_test first later = true ->
    LaterPreservesFixed p first later
}.

Definition producer_accepted rules proc :=
  existsb (fun rule => producer_test rule proc) rules.
Definition transport_accepted rules first later :=
  existsb (fun rule => transport_test rule first later) rules.

Theorem accepted_producer_sound rules p proc :
  (0 < statement_fuel p)%nat -> producer_accepted rules proc = true ->
  ProducerIdempotent p proc.
Proof.
  intros HF HC. unfold producer_accepted in HC.
  apply existsb_exists in HC as [rule [HI HT]].
  exact (producer_rule_sound rule p proc HF HT).
Qed.
Theorem accepted_transport_sound rules p first later :
  (0 < statement_fuel p)%nat -> transport_accepted rules first later = true ->
  LaterPreservesFixed p first later.
Proof.
  intros HF HC. unfold transport_accepted in HC.
  apply existsb_exists in HC as [rule [HI HT]].
  exact (transport_rule_sound rule p first later HF HT).
Qed.

Definition certified_order rules order := filter (producer_accepted rules) order.
Definition residual_order rules order :=
  filter (fun proc => negb (producer_accepted rules proc)) order.

Theorem certified_order_sound rules p order :
  (0 < statement_fuel p)%nat ->
  Forall (ProducerIdempotent p) (certified_order rules order).
Proof.
  intro HF. apply Forall_forall. intros proc HI.
  apply filter_In in HI as [_ HT].
  exact (accepted_producer_sound rules p proc HF HT).
Qed.

Fixpoint ordered_check producers transports order :=
  match order with
  | [] => true
  | first :: rest =>
      producer_accepted producers first &&
      forallb (transport_accepted transports first) rest &&
      ordered_check producers transports rest
  end.

Theorem ordered_check_sound producers transports p order :
  (0 < statement_fuel p)%nat -> ordered_check producers transports order = true ->
  OrderedProducerCertificate p order.
Proof.
  intro HF. induction order as [|first rest IH]; cbn; intro HC; [exact I|].
  apply andb_true_iff in HC as [HC HR].
  apply andb_true_iff in HC as [HP HT].
  split; [exact (accepted_producer_sound producers p first HF HP)|].
  split; [|exact (IH HR)].
  apply Forall_forall. intros later HI.
  apply forallb_forall with (x:=later) in HT; [|exact HI].
  exact (accepted_transport_sound transports p first later HF HT).
Qed.

End ExtendedSVCombRuleRegistry.
Print Assumptions ExtendedSVCombRuleRegistry.accepted_producer_sound.
Print Assumptions ExtendedSVCombRuleRegistry.accepted_transport_sound.
Print Assumptions ExtendedSVCombRuleRegistry.certified_order_sound.
Print Assumptions ExtendedSVCombRuleRegistry.ordered_check_sound.
