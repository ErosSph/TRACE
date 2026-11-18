(** Data correctness is required only for real valid slots. Coverage and
    value correctness are different obligations; an old tag is not a valid bit. *)
From Coq Require Import ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVScalarHistory Lang.ExtendedSVScalarExpression
 Lang.ExtendedSVProjectionOrigin Lang.ExtendedSVCompanionField Lang.ExtendedSVRecipeCoverage
 Lang.ExtendedSVWordInvariant.
Import ExtendedSV ExtendedSVScalarHistory ExtendedSVScalarExpression ExtendedSVProjectionOrigin
 ExtendedSVCompanionField ExtendedSVRecipeCoverage ExtendedSVWordInvariant.
Module ExtendedSVValidCompanion.
Section Field.
Context {Label:Type}.
Variable value:Label->option Z.
Definition ValidField width root validroot s(tag:option Label):Prop:=
 norm 1(read_signal s validroot)<>0%Z ->FieldRelated value width root s tag.

Theorem valid_recipe_value oldvalid inputvalid valid recipe
 (coverage:RecipeCovered oldvalid inputvalid valid recipe):
 forall width root capture expression,
 RecipeMatches width root capture expression recipe ->forall s old incoming,
 (norm 1(read_signal s oldvalid)<>0%Z ->FieldRelated value width root s old) ->
 (norm 1(read_signal s inputvalid)<>0%Z ->ExpressionRelated value width capture s incoming) ->
 norm 1(eval_expr s valid)<>0%Z ->
 ExpressionRelated value width expression s(recipe_origin s recipe old incoming).
Proof.
 induction coverage;intros width root capture expression HM s old incoming HO HI HV;
 inversion HM;subst.
 - intros label HT;cbn[eval_expr];rewrite norm_idempotent.
   exact(HO(requires_bit_sound _ _ H s HV)label HT).
 - exact(HI(requires_bit_sound _ _ H s HV)).
 - intros label HT;discriminate.
 - cbn[eval_expr]in HV;rewrite norm_idempotent in HV.
   intros label HT;cbn[recipe_origin]in HT;cbn[eval_expr];rewrite norm_idempotent.
   destruct(Z.eqb(eval_expr s guard)0).
   + eapply IHcoverage2;[eassumption|exact HO|exact HI|exact HV|exact HT].
   + eapply IHcoverage1;[eassumption|exact HO|exact HI|exact HV|exact HT].
Qed.

Theorem actual_valid_expression_phase p root width validroot proc capture expression valid expanded recipe inputvalid
 (data_certificate:ScalarCertificate p root width proc expression)
 (valid_certificate:ScalarCertificate p validroot 1 proc valid)
 (matches:RecipeMatches width root capture expression recipe)
 (coverage:RecipeCovered validroot inputvalid expanded recipe)ev pre old incoming:
 changed_signal ev<>root ->changed_signal ev<>validroot ->
 norm 1(eval_expr(phase_driven_state p ev pre)valid)=
 norm 1(eval_expr(phase_driven_state p ev pre)expanded) ->
 ValidField width root validroot pre old ->
 (norm 1(read_signal(phase_driven_state p ev pre)inputvalid)<>0%Z ->
 ExpressionRelated value width capture(phase_driven_state p ev pre)incoming) ->
 ValidField width root validroot(PhaseSemantics p ev pre)
 (projection_phase_origin p proc recipe ev pre old incoming).
Proof.
 intros HE HV HX HO HI HPost label HT.
 rewrite(history_phase_projection _ _ _ _ _ valid_certificate ev pre HV)in HPost.
 rewrite(history_phase_projection _ _ _ _ _ data_certificate ev pre HE).
 unfold projection_phase_origin in HT.
 destruct(process_matches_states pre(phase_driven_state p ev pre)proc).
 - rewrite HX in HPost.
   eapply valid_recipe_value;[exact coverage|exact matches| |exact HI|exact HPost|exact HT].
   intros HOld t HTag.
   rewrite(sampled_root_preserved p ev pre validroot(history_comb_frame _ _ _ _ _ valid_certificate)HV)in HOld.
   rewrite(sampled_root_preserved p ev pre root(history_comb_frame _ _ _ _ _ data_certificate)HE).
   exact(HO HOld t HTag).
 - exact(HO HPost label HT).
Qed.
End Field.
End ExtendedSVValidCompanion.
Print Assumptions ExtendedSVValidCompanion.valid_recipe_value.
Print Assumptions ExtendedSVValidCompanion.actual_valid_expression_phase.
