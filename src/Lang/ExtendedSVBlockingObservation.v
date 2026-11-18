(** Backwards, compositional output observations for actual blocking effects. *)
From Coq Require Import List ZArith Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVAutoAdapterEffects
 Lang.ExtendedSVSequentialSubstitution Lang.ExtendedSVProjectionConnection
 Lang.ExtendedSVExprAgreement Lang.ExtendedSVWordInvariant Lang.ExtendedSVBlocking
 Lang.ExtendedSVAssignment Lang.ExtendedSVRootProjection.
Import ListNotations ExtendedSV ExtendedSVAutoAdapterEffects
 ExtendedSVSequentialSubstitution ExtendedSVProjectionConnection
 ExtendedSVExprAgreement ExtendedSVWordInvariant ExtendedSVBlocking ExtendedSVAssignment
 ExtendedSVRootProjection.
Module ExtendedSVBlockingObservation.

Definition Observes plan width post before := forall es,
 norm width(eval_expr(blocking_state(eval_effect plan es))post)=
 norm width(eval_expr(blocking_state es)before).

Lemma empty width e : Observes FEmpty width e e.
Proof. intros es;reflexivity. Qed.
Lemma seq_nil width e : Observes(FSeq [])width e e.
Proof. intros es;reflexivity. Qed.
Lemma assignment width aw root rhs e :
 (forall w x,In(w,x)(expr_inputs e)->x=root->w=aw) ->
 Observes(FAssign false rhs(LVar aw root))width e
 (substitute(assign_substitution aw root rhs)e).
Proof.
 intros HW es;cbn[eval_effect blocking_state].
 rewrite read_after_blocking_assignment by exact HW;reflexivity.
Qed.
Lemma assignment_unread width aw root rhs e :
 (forall w x,In(w,x)(expr_inputs e)->x<>root) ->
 Observes(FAssign false rhs(LVar aw root))width e e.
Proof.
 intros H es;cbn[eval_effect blocking_state].
 f_equal;apply eval_expr_agree;intros w x HI.
 rewrite read_signal_apply_update_other;[reflexivity|].
 rewrite resolve_update_root;cbn[lvalue_root];intro HE;apply(H w x HI);congruence.
Qed.
Definition reads_unwrittenb root e :=
 forallb(fun wr=>negb(Nat.eqb(snd wr)root))(expr_inputs e).
Definition reads_compatibleb aw root e :=
 forallb(fun wr=>negb(Nat.eqb(snd wr)root)||Nat.eqb(fst wr)aw)(expr_inputs e).
Lemma assignment_unread_checked width aw root rhs e :
 reads_unwrittenb root e=true ->
 Observes(FAssign false rhs(LVar aw root))width e e.
Proof.
 intro HC;apply assignment_unread;intros w x HI.
 pose proof(proj1(forallb_forall _ _)HC(w,x)HI)as H.
 cbn[fst snd]in H;apply negb_true_iff in H;now apply Nat.eqb_neq.
Qed.
Lemma assignment_checked width aw root rhs e :
 reads_compatibleb aw root e=true ->
 Observes(FAssign false rhs(LVar aw root))width e
 (substitute(assign_substitution aw root rhs)e).
Proof.
 intro HC;apply assignment;intros w x HI HE;subst x.
 pose proof(proj1(forallb_forall _ _)HC(w,root)HI)as H.
 cbn[fst snd]in H;rewrite Nat.eqb_refl in H;cbn in H;now apply Nat.eqb_eq.
Qed.
Lemma seq_cons p rest width post middle before :
 Observes(FSeq rest)width post middle ->Observes p width middle before ->
 Observes(FSeq(p::rest))width post before.
Proof.
 intros HR HP es;cbn[eval_effect fold_left].
 change(norm width(eval_expr(blocking_state(eval_effect(FSeq rest)(eval_effect p es)))post)=
 norm width(eval_expr(blocking_state es)before)).
 rewrite HR;apply HP.
Qed.
Lemma branch g yes no width post ey en :
 Observes yes width post ey ->Observes no width post en ->
 Observes(FIf g yes no)width post(ECond width g ey en).
Proof.
 intros HY HN es;cbn[eval_effect eval_expr].
 destruct(Z.eqb(eval_expr(blocking_state es)g)0);
 rewrite norm_idempotent;[apply HN|apply HY].
Qed.
Lemma case_nil scr width e : Observes(FCase scr [])width e e.
Proof. intros es;reflexivity. Qed.
Lemma case_default scr p width post before :
 Observes p width post before ->Observes(FCase scr [(None,p)])width post before.
Proof. exact(fun H=>H). Qed.
Lemma case_some scr key p rest width post yes no :
 Observes p width post yes ->Observes(FCase scr rest)width post no ->
 Observes(FCase scr ((Some key,p)::rest))width post
 (ECond width(EBinary 1 BEq scr key)yes no).
Proof.
 intros HY HN es;cbn[eval_effect eval_expr].
 rewrite norm_one_boolz.
 destruct(Z.eqb(eval_expr(blocking_state es)scr)(eval_expr(blocking_state es)key));
 cbn[boolz];rewrite norm_idempotent;[apply HY|apply HN].
Qed.

Theorem actual_output p proc plan width root expression :
 blocking_onlyb(process_body proc)=true ->
 compile_effect(statement_fuel p)(process_body proc)=Some plan ->
 Observes plan width(EVar width root)expression ->
 forall s,norm width(read_signal(run_process p s proc)root)=
 norm width(eval_expr s expression).
Proof.
 intros HB HC HO s;rewrite blocking_run_process by exact HB.
 rewrite(compile_effect_sound _ _ _ _ HC).
 specialize(HO(initial_exec s));cbn[initial_exec blocking_state eval_expr]in HO.
 rewrite norm_idempotent in HO;exact HO.
Qed.
End ExtendedSVBlockingObservation.
Print Assumptions ExtendedSVBlockingObservation.actual_output.
