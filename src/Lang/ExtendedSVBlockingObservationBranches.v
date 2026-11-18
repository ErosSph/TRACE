(** Narrow LLM-authored: OpenAI Codex. Identical output observations do not
    depend on a branch guard. Original conditional effects remain unchanged. *)
From Coq Require Import List ZArith Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVAutoAdapterEffects Lang.ExtendedSVBlockingObservation.
Import ListNotations ExtendedSV ExtendedSVAutoAdapterEffects ExtendedSVBlockingObservation.
Module ExtendedSVBlockingObservationBranches.
Lemma branch_same g yes no width post before :
 Observes yes width post before -> Observes no width post before ->
 Observes(FIf g yes no)width post before.
Proof.
 intros HY HN es;cbn[eval_effect].
 destruct(Z.eqb(eval_expr(blocking_state es)g)0);[apply HN|apply HY].
Qed.
Lemma case_some_same scr key p rest width post before :
 Observes p width post before -> Observes(FCase scr rest)width post before ->
 Observes(FCase scr((Some key,p)::rest))width post before.
Proof.
 intros HY HN es;cbn[eval_effect].
 destruct(Z.eqb(eval_expr(blocking_state es)scr)(eval_expr(blocking_state es)key));[apply HY|apply HN].
Qed.
End ExtendedSVBlockingObservationBranches.
