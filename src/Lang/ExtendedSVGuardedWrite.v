(** Correlated blocking outputs: a disabled gate cannot authorize a write.
    Prefix, branch and suffix remain complete state-threaded effects. *)
From Coq Require Import List ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVAutoAdapterEffects.
Import ListNotations ExtendedSV ExtendedSVAutoAdapterEffects.
Module ExtendedSVGuardedWrite.
Lemma sequence_single plan es : eval_effect(FSeq[plan])es=eval_effect plan es.
Proof. reflexivity. Qed.
Lemma sequence_group before action after es :
 eval_effect(FSeq(before++action::after))es=
 eval_effect(FSeq[FSeq before;action;FSeq after])es.
Proof. cbn [eval_effect]. rewrite fold_left_app;reflexivity. Qed.
Definition Safe gate write s :=
 norm 1 (read_signal s write) = 0%Z \/ norm 1 (read_signal s gate) = 1%Z.

Theorem guarded_clear prefix guard clear suffix gate write :
 (forall es, norm 1(read_signal(blocking_state(eval_effect prefix es))gate)=1%Z) ->
 (forall es, norm 1(read_signal(blocking_state(eval_effect clear es))write)=0%Z) ->
 (forall es, read_signal(blocking_state(eval_effect suffix es))gate=read_signal(blocking_state es)gate) ->
 (forall es, read_signal(blocking_state(eval_effect suffix es))write=read_signal(blocking_state es)write) ->
 forall es, Safe gate write (blocking_state
   (eval_effect (FSeq [prefix; FIf guard clear FEmpty; suffix]) es)).
Proof.
 intros HP HC HG HW es. unfold Safe.
 change(norm 1(read_signal(blocking_state(eval_effect suffix
   (eval_effect(FIf guard clear FEmpty)(eval_effect prefix es))))write)=0%Z \/
   norm 1(read_signal(blocking_state(eval_effect suffix
   (eval_effect(FIf guard clear FEmpty)(eval_effect prefix es))))gate)=1%Z).
 rewrite HW,HG. cbn [eval_effect].
 destruct(Z.eqb(eval_expr(blocking_state(eval_effect prefix es))guard)0).
 - right;apply HP.
 - left;apply HC.
Qed.

Theorem safe_implies_enabled gate write s : Safe gate write s ->
 norm 1(read_signal s write)<>0%Z ->norm 1(read_signal s gate)<>0%Z.
Proof. intros [HW|HG] H;[contradiction|rewrite HG;discriminate]. Qed.
End ExtendedSVGuardedWrite.
Print Assumptions ExtendedSVGuardedWrite.guarded_clear.
Print Assumptions ExtendedSVGuardedWrite.safe_implies_enabled.
