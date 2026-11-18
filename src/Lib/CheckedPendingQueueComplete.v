(** Completeness, not an assumed successful CPU checker result. The caller
    must prove the actual retirement list is exactly the queue prefix. *)
From Coq Require Import List Arith.
Require Import Lib.CheckedPendingQueue.
Import ListNotations.
Module CheckedPendingQueueComplete.
Section Queue.
Context {Token:Type}.
Variable eq_dec:forall x y:Token,{x=y}+{x<>y}.
Theorem no_cancel_complete(queue admitted retiring kept:list Token):
 queue++admitted=retiring++kept ->
 CheckedPendingQueue.step eq_dec queue admitted retiring 0=Some(kept,[]).
Proof.
 intro HE;unfold CheckedPendingQueue.step;rewrite HE.
 rewrite CheckedPendingQueue.consume_complete;cbn[Nat.leb].
 now rewrite Nat.sub_0_r,firstn_all,skipn_all.
Qed.
End Queue.
Example actual_head_is_consumed:
 CheckedPendingQueue.step Nat.eq_dec[3;4][][3]0=Some([4],[]).
Proof. apply no_cancel_complete;reflexivity. Qed.
Example bubble_does_not_consume_the_next_token:
 CheckedPendingQueue.step Nat.eq_dec[4][][]0=Some([4],[]).
Proof. apply no_cancel_complete;reflexivity. Qed.
Example appended_token_cannot_retire_before_the_old_head:
 CheckedPendingQueue.step Nat.eq_dec[3][4][4]0=None.
Proof. vm_compute;reflexivity. Qed.
Print Assumptions no_cancel_complete.
Print Assumptions actual_head_is_consumed.
Print Assumptions bubble_does_not_consume_the_next_token.
Print Assumptions appended_token_cannot_retire_before_the_old_head.
End CheckedPendingQueueComplete.
