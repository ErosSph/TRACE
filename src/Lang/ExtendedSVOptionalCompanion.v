(** Valid-slot data correctness only for tokens that HAVE a reference value.
    A token whose original ISA step produces no register result (a branch,
    a store, FENCE.I) imposes no data obligation on a pipeline result field.
    This is the accepted [ExtendedSVValidCompanion] relation applied to a
    filtered tag: the filter keeps a label exactly when its value is defined.
    Because origin recipes only choose the old tag, the incoming tag or none,
    the filter commutes with them, so the accepted transport theorem is reused
    unchanged. A consumer that needs the value (forwarding) must still show the
    value is defined, e.g. from an actual write enable. *)
From Coq Require Import ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVScalarHistory Lang.ExtendedSVScalarExpression
 Lang.ExtendedSVProjectionOrigin Lang.ExtendedSVCompanionField Lang.ExtendedSVRecipeCoverage
 Lang.ExtendedSVWordInvariant Lang.ExtendedSVValidCompanion.
Import ExtendedSV ExtendedSVScalarHistory ExtendedSVScalarExpression ExtendedSVProjectionOrigin
 ExtendedSVCompanionField ExtendedSVRecipeCoverage ExtendedSVWordInvariant ExtendedSVValidCompanion.
Module ExtendedSVOptionalCompanion.
Section Field.
Context {Label:Type}.
Variable value:Label->option Z.

Definition keep(tag:option Label):option Label:=
 match tag with
 |Some label=>match value label with Some _=>Some label|None=>None end
 |None=>None end.

Definition OptionalField width root validroot s(tag:option Label):Prop:=
 ValidField value width root validroot s(keep tag).
Definition OptionalExpression width expression s(tag:option Label):Prop:=
 ExpressionRelated value width expression s(keep tag).

Lemma keep_recipe_origin s recipe old incoming:
 keep(recipe_origin s recipe old incoming)=recipe_origin s recipe(keep old)(keep incoming).
Proof. induction recipe;cbn[recipe_origin];try reflexivity.
 destruct(Z.eqb(eval_expr s guard)0);assumption. Qed.

Lemma keep_projection_phase_origin p proc recipe ev pre old incoming:
 keep(projection_phase_origin p proc recipe ev pre old incoming)=
 projection_phase_origin p proc recipe ev pre(keep old)(keep incoming).
Proof. unfold projection_phase_origin.
 destruct(process_matches_states pre(phase_driven_state p ev pre)proc);
 [apply keep_recipe_origin|reflexivity]. Qed.

(** The accepted valid-field phase theorem, for the optional relation. *)
Theorem optional_valid_expression_phase p root width validroot proc capture expression valid expanded recipe inputvalid
 (data_certificate:ScalarCertificate p root width proc expression)
 (valid_certificate:ScalarCertificate p validroot 1 proc valid)
 (matches:RecipeMatches width root capture expression recipe)
 (coverage:RecipeCovered validroot inputvalid expanded recipe)ev pre old incoming:
 changed_signal ev<>root ->changed_signal ev<>validroot ->
 norm 1(eval_expr(phase_driven_state p ev pre)valid)=
 norm 1(eval_expr(phase_driven_state p ev pre)expanded) ->
 OptionalField width root validroot pre old ->
 (norm 1(read_signal(phase_driven_state p ev pre)inputvalid)<>0%Z ->
 OptionalExpression width capture(phase_driven_state p ev pre)incoming) ->
 OptionalField width root validroot(PhaseSemantics p ev pre)
 (projection_phase_origin p proc recipe ev pre old incoming).
Proof.
 intros HE HV HX HO HI;unfold OptionalField;rewrite keep_projection_phase_origin.
 exact(actual_valid_expression_phase value p root width validroot proc capture expression valid expanded recipe inputvalid
  data_certificate valid_certificate matches coverage ev pre(keep old)(keep incoming)HE HV HX HO HI).
Qed.

(** Every accepted (total) field relation is an optional one. *)
Lemma valid_field_optional width root validroot s tag:
 ValidField value width root validroot s tag ->OptionalField width root validroot s tag.
Proof. intros H HV label HT;unfold keep in HT.
 destruct tag as[l|];[|discriminate].
 destruct(value l)eqn:HL;[injection HT as <-;exact(H HV l eq_refl)|discriminate]. Qed.
Lemma expression_optional width expression s tag:
 ExpressionRelated value width expression s tag ->OptionalExpression width expression s tag.
Proof. intros H label HT;unfold keep in HT.
 destruct tag as[l|];[|discriminate].
 destruct(value l)eqn:HL;[injection HT as <-;exact(H l eq_refl)|discriminate]. Qed.

(** A token with no reference value imposes no obligation. *)
Lemma no_value_optional width root validroot s label:
 value label=None ->OptionalField width root validroot s(Some label).
Proof. intros HN HV l HT;cbn[keep]in HT;rewrite HN in HT;discriminate. Qed.
Lemma no_value_expression width expression s label:
 value label=None ->OptionalExpression width expression s(Some label).
Proof. intros HN l HT;cbn[keep]in HT;rewrite HN in HT;discriminate. Qed.

(** Recover the exact value when the consumer knows one exists. *)
Lemma optional_defined width root validroot s label v:
 OptionalField width root validroot s(Some label) ->value label=Some v ->
 norm 1(read_signal s validroot)<>0%Z ->value label=Some(norm width(read_signal s root)).
Proof. intros H HL HV;apply(H HV);cbn[keep];rewrite HL;reflexivity. Qed.
Lemma optional_field_defined width root validroot s tag:
 OptionalField width root validroot s tag ->
 (forall label,tag=Some label ->exists v,value label=Some v) ->
 ValidField value width root validroot s tag.
Proof. intros H HD HV label HT;destruct(HD label HT)as[v HL];subst tag.
 exact(optional_defined width root validroot s label v H HL HV). Qed.
End Field.
End ExtendedSVOptionalCompanion.
Print Assumptions ExtendedSVOptionalCompanion.keep_projection_phase_origin.
Print Assumptions ExtendedSVOptionalCompanion.optional_valid_expression_phase.
Print Assumptions ExtendedSVOptionalCompanion.valid_field_optional.
Print Assumptions ExtendedSVOptionalCompanion.expression_optional.
Print Assumptions ExtendedSVOptionalCompanion.no_value_optional.
Print Assumptions ExtendedSVOptionalCompanion.no_value_expression.
Print Assumptions ExtendedSVOptionalCompanion.optional_defined.
Print Assumptions ExtendedSVOptionalCompanion.optional_field_defined.
