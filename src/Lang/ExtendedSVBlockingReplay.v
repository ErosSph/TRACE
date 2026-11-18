(** Replay the actual captured blocking updates. Expressions are evaluated at
    their original intra-process state, not reevaluated at the replay state. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVBlocking.
Import ExtendedSV ExtendedSVBlocking ListNotations.
Module ExtendedSVBlockingReplay.
Lemma apply_updates_app state xs ys:
 apply_updates state(xs++ys)=apply_updates(apply_updates state xs)ys.
Proof. induction xs in state|-*;cbn;[reflexivity|apply IHxs]. Qed.
Definition BlockingReplay origin es:=
 blocking_state es=apply_updates origin(emitted_updates es).
Theorem blocking_execution_replays origin fuel st es:
 blocking_onlyb st=true->BlockingReplay origin es->
 BlockingReplay origin(exec_stmt fuel st es).
Proof.
 induction fuel as[|fuel IH]in st,es|-*;[auto|].
 destruct st as[|nba rhs lhs|xs|guard yes no|scrutinee arms];cbn;intros H HR.
 - exact HR.
 - destruct nba;[discriminate|]. unfold BlockingReplay in *. cbn.
   rewrite apply_updates_app. cbn. now rewrite <-HR.
 - induction xs as[|st xs IHr]in es,H,HR|-*;cbn in *;[exact HR|].
   apply andb_true_iff in H as[Hst Hxs]. apply IHr;[exact Hxs|].
   now apply IH.
 - apply andb_true_iff in H as[Hy Hn].
   destruct(Z.eqb(eval_expr(blocking_state es)guard)0);apply IH;assumption.
 - apply IH;[apply selected_blocking;[exact H|reflexivity]|exact HR].
Qed.
Theorem actual_blocking_process_replays p proc state:
 blocking_onlyb(process_body proc)=true->
 run_process p state proc=apply_updates state(process_updates p state proc).
Proof.
 intro H. rewrite blocking_run_process by exact H.
 apply blocking_execution_replays;[exact H|reflexivity].
Qed.
End ExtendedSVBlockingReplay.
Print Assumptions ExtendedSVBlockingReplay.actual_blocking_process_replays.
