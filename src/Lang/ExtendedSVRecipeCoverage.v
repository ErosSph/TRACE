(** Non-vacuous origin coverage from real validity expressions.
    AND may add an unknown enable, but may not manufacture source validity.
    Directional coverage is not a proof that every admitted token survives. *)
From Coq Require Import ZArith Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVProjectionOrigin
 Lang.ExtendedSVScalarHistory Lang.ExtendedSVScalarExpression Lang.ExtendedSVWordInvariant.
Import ExtendedSV ExtendedSVProjectionOrigin ExtendedSVScalarHistory
 ExtendedSVScalarExpression ExtendedSVWordInvariant.
Local Open Scope Z_scope.
Module ExtendedSVRecipeCoverage.

Lemma norm_and_left width a b : norm width(Z.land a b)=Z.land(norm width a)b.
Proof.
 unfold norm. rewrite <-Z.land_assoc,(Z.land_comm b(mask width)),Z.land_assoc. reflexivity.
Qed.

Inductive RequiresBit root : Expr -> Prop :=
| RequiresSource : RequiresBit root(EVar 1 root)
| RequiresZero : RequiresBit root(EConst 1 0)
| RequiresExtend : forall e,RequiresBit root e ->RequiresBit root(EExtend 1 false e)
| RequiresAndLeft : forall a b,RequiresBit root a ->RequiresBit root(EBinary 1 BAnd a b)
| RequiresAndRight : forall a b,RequiresBit root b ->RequiresBit root(EBinary 1 BAnd a b)
| RequiresChoice : forall guard a b,RequiresBit root a ->RequiresBit root b ->
 RequiresBit root(ECond 1 guard a b).

Theorem requires_bit_sound root e(certificate:RequiresBit root e)s :
 norm 1(eval_expr s e)<>0 ->norm 1(read_signal s root)<>0.
Proof.
 induction certificate;cbn[eval_expr];rewrite ?norm_idempotent.
 - exact(fun H=>H).
 - cbn[norm];intros H;contradiction.
 - exact IHcertificate.
 - intros H;apply IHcertificate;intro Hzero.
   apply H;rewrite norm_and_left,Hzero,Z.land_0_l;reflexivity.
 - intros H;apply IHcertificate;intro Hzero.
   apply H;rewrite Z.land_comm,norm_and_left,Hzero,Z.land_0_l;reflexivity.
 - destruct(Z.eqb(eval_expr s guard)0);[exact IHcertificate2|exact IHcertificate1].
Qed.

Inductive RecipeCovered oldvalid inputvalid : Expr -> OriginRecipe -> Prop :=
| CoveredHold : forall e,RequiresBit oldvalid e ->RecipeCovered oldvalid inputvalid e Hold
| CoveredCapture : forall e,RequiresBit inputvalid e ->RecipeCovered oldvalid inputvalid e Capture
| CoveredUnknown : RecipeCovered oldvalid inputvalid(EConst 1 0)Unknown
| CoveredSelect : forall guard yes no ry rn,
 RecipeCovered oldvalid inputvalid yes ry ->RecipeCovered oldvalid inputvalid no rn ->
 RecipeCovered oldvalid inputvalid(ECond 1 guard yes no)(Select guard ry rn).

Section Labels.
Context {Label:Type}.
Theorem recipe_coverage oldvalid inputvalid valid recipe
 (certificate:RecipeCovered oldvalid inputvalid valid recipe)s(old incoming:option Label):
 (norm 1(read_signal s oldvalid)<>0 ->exists label,old=Some label) ->
 (norm 1(read_signal s inputvalid)<>0 ->exists label,incoming=Some label) ->
 norm 1(eval_expr s valid)<>0 ->
 exists label,recipe_origin s recipe old incoming=Some label.
Proof.
 intros Hold Hinput;induction certificate;cbn[recipe_origin];intro HV.
 - apply Hold;exact(requires_bit_sound _ _ H s HV).
 - apply Hinput;exact(requires_bit_sound _ _ H s HV).
 - cbn[eval_expr norm]in HV;contradiction.
 - cbn[eval_expr]in HV;rewrite norm_idempotent in HV.
   destruct(Z.eqb(eval_expr s guard)0);[now apply IHcertificate2|now apply IHcertificate1].
Qed.

Theorem actual_recipe_coverage p validroot proc valid expanded recipe inputvalid
 (scalar:ScalarCertificate p validroot 1 proc valid)
 (certificate:RecipeCovered validroot inputvalid expanded recipe)ev pre old incoming:
 changed_signal ev<>validroot ->
 (norm 1(read_signal pre validroot)<>0 ->exists label,old=Some label) ->
 (norm 1(read_signal(phase_driven_state p ev pre)inputvalid)<>0 ->exists label,incoming=Some label) ->
 norm 1(eval_expr(phase_driven_state p ev pre)valid)=
 norm 1(eval_expr(phase_driven_state p ev pre)expanded) ->
 norm 1(read_signal(PhaseSemantics p ev pre)validroot)<>0 ->
 exists label,@projection_phase_origin Label p proc recipe ev pre old incoming=Some label.
Proof.
 intros HE Hold Hinput Hexpand HV.
 rewrite(history_phase_projection _ _ _ _ _ scalar ev pre HE)in HV.
 unfold projection_phase_origin.
 destruct(process_matches_states pre(phase_driven_state p ev pre)proc).
 - rewrite Hexpand in HV.
   eapply recipe_coverage;[exact certificate| |exact Hinput|exact HV].
   rewrite(sampled_root_preserved p ev pre validroot
     (history_comb_frame _ _ _ _ _ scalar)HE);exact Hold.
 - now apply Hold.
Qed.
End Labels.
Print Assumptions requires_bit_sound.
Print Assumptions recipe_coverage.
Print Assumptions actual_recipe_coverage.
End ExtendedSVRecipeCoverage.
