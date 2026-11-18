(** A common finite-wait measure for ordered pipelines with one-cycle redirects.
    The premises describe this actual cycle, never a promised future commit. *)
From Coq Require Import List Arith Lia.
Require Import Ex.External.CPUQueueCreditProgress.
Import ListNotations CPUQueueCreditProgress.
Module CPUQueueDeferredProgress.

Definition rank {Token:Type} capacity (pending:list Token) wait :=
 2 * credit capacity pending + wait.

Theorem silent_admission_progress {Token:Type} capacity
 (pending admitted retired next:list Token) wait next_wait :
 pending++admitted=retired++next -> retired=[] -> admitted<>[] ->
 length next<=capacity -> next_wait<=1 ->
 rank capacity next next_wait < rank capacity pending wait.
Proof.
 intros HQ HR HA HC HW.
 pose proof(silent_credit_decreases capacity pending admitted retired next HQ HR HA HC)as HD.
 unfold rank;lia.
Qed.

Theorem silent_deferred_progress {Token:Type} capacity
 (pending next:list Token) wait next_wait :
 pending=next -> wait=1 -> next_wait=0 ->
 rank capacity next next_wait < rank capacity pending wait.
Proof. intros HQ HW HN;subst next wait next_wait;unfold rank;lia. Qed.

Theorem silent_cycle_progress {Token:Type} capacity
 (pending admitted retired next:list Token) wait next_wait :
 pending++admitted=retired++next -> retired=[] -> length next<=capacity ->
 next_wait<=1 ->
 (admitted<>[] \/ (pending=next /\ wait=1 /\ next_wait=0)) ->
 rank capacity next next_wait < rank capacity pending wait.
Proof.
 intros HQ HR HC HW [HA|[HP[HB HN]]].
 - exact(silent_admission_progress capacity pending admitted retired next wait next_wait HQ HR HA HC HW).
 - exact(silent_deferred_progress capacity pending next wait next_wait HP HB HN).
Qed.
End CPUQueueDeferredProgress.
Print Assumptions CPUQueueDeferredProgress.silent_admission_progress.
Print Assumptions CPUQueueDeferredProgress.silent_deferred_progress.
Print Assumptions CPUQueueDeferredProgress.silent_cycle_progress.
