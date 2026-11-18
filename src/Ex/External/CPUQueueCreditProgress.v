(** Queue-space ranking for real, non-flushing ordered cycles.
    All four inputs must be proved for the actual transition: queue accounting,
    no retirement, nonempty admission, and the next queue's physical bound.
    In particular this does not postulate that a CPU eventually commits. *)
From Coq Require Import List Arith Lia.
Import ListNotations.

Module CPUQueueCreditProgress.

Definition credit {Token : Type} (capacity : nat) (pending : list Token) : nat :=
  capacity - length pending.

Theorem silent_queue_grows {Token : Type}
  (pending admitted retired next : list Token) :
  pending ++ admitted = retired ++ next ->
  retired = [] -> admitted <> [] ->
  length pending < length next.
Proof.
  intros HQ HR HA; subst retired; cbn in HQ.
  apply (f_equal (@length Token)) in HQ; rewrite app_length in HQ.
  destruct admitted; [contradiction|]; cbn in HQ; lia.
Qed.

Theorem silent_credit_decreases {Token : Type} capacity
  (pending admitted retired next : list Token) :
  pending ++ admitted = retired ++ next ->
  retired = [] -> admitted <> [] -> length next <= capacity ->
  credit capacity next < credit capacity pending.
Proof.
  intros HQ HR HA HB.
  pose proof (silent_queue_grows pending admitted retired next HQ HR HA) as HG.
  unfold credit; lia.
Qed.

Theorem full_queue_commits {Token : Type} capacity
  (pending admitted retired next : list Token) :
  pending ++ admitted = retired ++ next ->
  length pending = capacity -> admitted <> [] -> length next <= capacity ->
  retired <> [].
Proof.
  intros HQ HP HA HB HR.
  pose proof (silent_queue_grows pending admitted retired next HQ HR HA) as HG.
  lia.
Qed.

Print Assumptions silent_queue_grows.
Print Assumptions silent_credit_decreases.
Print Assumptions full_queue_commits.
End CPUQueueCreditProgress.
