(** Narrow LLM-authored: OpenAI Codex. Exact 32-bit root[0] = 0 blocking
    observation, used by ISA address alignment without changing RTL. *)
From Coq Require Import List ZArith Bool btauto.Btauto.
Require Import Lang.ExtendedSV Lang.ExtendedSVAutoAdapterEffects
 Lang.ExtendedSVProjectionConnection Lang.ExtendedSVExprAgreement
 Lang.ExtendedSVSequentialSubstitution Lang.ExtendedSVWordInvariant
 Lang.ExtendedSVRootProjection Lang.ExtendedSVRecipeCoverage Lang.ExtendedSVBlockingObservation.
Import ExtendedSV ExtendedSVAutoAdapterEffects ExtendedSVProjectionConnection
 ExtendedSVExprAgreement ExtendedSVSequentialSubstitution ExtendedSVWordInvariant
 ExtendedSVRootProjection ExtendedSVRecipeCoverage ExtendedSVBlockingObservation.
Local Open Scope Z_scope.
Module ExtendedSVBlockingObservationClearLowBit.
Definition cleared root := EBinary 32 BAnd(EVar 32 root)(EConst 32 (-2)).
Lemma clear_low_math old : norm 32(write_slice old 0 1 0)=
 norm 32(Z.land(norm 32 old)(norm 32 (-2))).
Proof.
 change(norm 32(Z.lor(Z.land old (-2))0)=norm 32(Z.land(norm 32 old)(norm 32 (-2)))).
 rewrite Z.lor_0_r. unfold norm. apply Z.bits_inj;intro bit.
 repeat rewrite Z.land_spec. btauto.
Qed.
Lemma clear_low_substitution s root e :
 (forall w x,In(w,x)(expr_inputs e)->x=root->w=32%nat) ->
 eval_expr s(substitute(assign_substitution 32 root(cleared root))e)=
 eval_expr(apply_update s(resolve_update s(LSel 1(LVar 32 root)(EConst 5 0))0))e.
Proof.
 intro HW;apply sequential_substitute_inputs;intros w x HI.
 unfold assign_substitution. destruct(Nat.eqb x root)eqn:HX.
 - apply Nat.eqb_eq in HX;subst x;specialize(HW w root HI eq_refl);subst w.
   change(norm 32(read_signal(write_signal s root(write_slice(read_signal s root)0 1 0))root)=
    norm 32(norm 32(norm 32(Z.land(norm 32(read_signal s root))(norm 32(-2)))))).
   rewrite read_signal_write_same,!norm_idempotent. apply clear_low_math.
 - apply Nat.eqb_neq in HX.
   rewrite read_signal_apply_update_other;[reflexivity|].
   rewrite resolve_update_root;cbn[lvalue_root];congruence.
Qed.
Lemma clear_low_observation width root e :
 reads_compatibleb 32 root e=true ->
 Observes(FAssign false(EConst 1 0)(LSel 1(LVar 32 root)(EConst 5 0)))width e
 (substitute(assign_substitution 32 root(cleared root))e).
Proof.
 intros HC es;cbn[eval_effect blocking_state eval_expr].
 change(norm width(eval_expr(apply_update(blocking_state es)
 (resolve_update(blocking_state es)(LSel 1(LVar 32 root)(EConst 5 0))0))e)=
 norm width(eval_expr(blocking_state es)(substitute(assign_substitution 32 root(cleared root))e))).
 rewrite clear_low_substitution;[reflexivity|].
 intros w x HI HE;subst x.
 pose proof(proj1(forallb_forall _ _)HC(w,root)HI)as H.
 cbn[fst snd]in H;rewrite Nat.eqb_refl in H;cbn in H;now apply Nat.eqb_eq.
Qed.
End ExtendedSVBlockingObservationClearLowBit.
