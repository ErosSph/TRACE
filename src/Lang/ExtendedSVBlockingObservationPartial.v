(** Narrow LLM-authored: OpenAI Codex. Unread blocking writes may target
    an arbitrary part-select; the observed expression still excludes the root. *)
From Coq Require Import List Bool ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVAutoAdapterEffects
 Lang.ExtendedSVExprAgreement Lang.ExtendedSVRootProjection Lang.ExtendedSVBlockingObservation.
Import ExtendedSV ExtendedSVAutoAdapterEffects ExtendedSVExprAgreement
 ExtendedSVRootProjection ExtendedSVBlockingObservation.
Module ExtendedSVBlockingObservationPartial.
Lemma assignment_unread_lvalue width lv rhs e :
 (forall w x,In(w,x)(expr_inputs e)->x<>lvalue_root lv) ->
 Observes(FAssign false rhs lv)width e e.
Proof.
 intros H es;cbn[eval_effect blocking_state].
 f_equal;apply eval_expr_agree;intros w x HI.
 rewrite read_signal_apply_update_other;[reflexivity|].
 rewrite resolve_update_root;intro HE;apply(H w x HI);congruence.
Qed.
Lemma assignment_unread_lvalue_checked width lv rhs e :
 reads_unwrittenb(lvalue_root lv)e=true ->
 Observes(FAssign false rhs lv)width e e.
Proof.
 intro HC;apply assignment_unread_lvalue;intros w x HI.
 pose proof(proj1(forallb_forall _ _)HC(w,x)HI)as H.
 cbn[fst snd]in H;apply negb_true_iff in H;now apply Nat.eqb_neq.
Qed.
End ExtendedSVBlockingObservationPartial.
