(** Restrict a DATA assertion to selected instruction classes without changing
    the physical validity bit, original tags, pending list or origin coverage. *)
From Coq Require Import ZArith Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVProjectionOrigin
 Lang.ExtendedSVScalarHistory Lang.ExtendedSVScalarExpression
 Lang.ExtendedSVCompanionField Lang.ExtendedSVValidCompanion Lang.ExtendedSVRecipeCoverage.
Import ExtendedSV ExtendedSVProjectionOrigin ExtendedSVScalarHistory ExtendedSVScalarExpression
 ExtendedSVCompanionField ExtendedSVValidCompanion ExtendedSVRecipeCoverage.
Module ExtendedSVSelectedCompanion.
Section Labels.
Context {Label:Type}.
Variable selected:Label->bool.

Definition selected_tag(tag:option Label):option Label:=match tag with
 |Some label=>if selected label then Some label else None |None=>None end.

Lemma selected_tag_some tag label:
 selected_tag tag=Some label <->tag=Some label /\selected label=true.
Proof.
 destruct tag as[t|];cbn[selected_tag].
 - destruct(selected t)eqn:HS.
   + split.
     * intro H;inversion H;subst;auto.
     * intros[H _];exact H.
   + split.
     * discriminate.
     * intros[H HSelected];inversion H;subst;congruence.
 - split;[discriminate|intros[H _];discriminate].
Qed.

Lemma selected_recipe_origin s recipe old incoming:
 selected_tag(recipe_origin s recipe old incoming)=
 recipe_origin s recipe(selected_tag old)(selected_tag incoming).
Proof.
 induction recipe;cbn[recipe_origin selected_tag];try reflexivity.
 destruct(Z.eqb(eval_expr s guard)0);assumption.
Qed.

Lemma selected_phase_origin p proc recipe ev pre old incoming:
 selected_tag(projection_phase_origin p proc recipe ev pre old incoming)=
 projection_phase_origin p proc recipe ev pre(selected_tag old)(selected_tag incoming).
Proof.
 unfold projection_phase_origin;destruct(process_matches_states pre(phase_driven_state p ev pre)proc);
 [apply selected_recipe_origin|reflexivity].
Qed.

Definition SelectedValidField(value:Label->option Z)width root validroot s tag:Prop:=
 forall label,tag=Some label ->selected label=true ->
 norm 1(read_signal s validroot)<>0%Z ->value label=Some(norm width(read_signal s root)).

Lemma selected_valid_field_exact value width root validroot s tag:
 SelectedValidField value width root validroot s tag <->
 ValidField value width root validroot s(selected_tag tag).
Proof.
 split.
 - intros H HV label HT;apply selected_tag_some in HT as[HT HS];exact(H label HT HS HV).
 - intros H label HT HS HV;apply(H HV label);apply selected_tag_some;auto.
Qed.

Theorem actual_selected_valid_expression_phase value p root width validroot proc capture expression valid expanded recipe inputvalid
 (data_certificate:ScalarCertificate p root width proc expression)
 (valid_certificate:ScalarCertificate p validroot 1 proc valid)
 (matches:RecipeMatches width root capture expression recipe)
 (coverage:RecipeCovered validroot inputvalid expanded recipe)ev pre old incoming:
 changed_signal ev<>root ->changed_signal ev<>validroot ->
 norm 1(eval_expr(phase_driven_state p ev pre)valid)=
 norm 1(eval_expr(phase_driven_state p ev pre)expanded) ->
 SelectedValidField value width root validroot pre old ->
 (norm 1(read_signal(phase_driven_state p ev pre)inputvalid)<>0%Z ->
 forall label,incoming=Some label ->selected label=true ->
 value label=Some(norm width(eval_expr(phase_driven_state p ev pre)capture))) ->
 SelectedValidField value width root validroot(PhaseSemantics p ev pre)
 (projection_phase_origin p proc recipe ev pre old incoming).
Proof.
 intros HE HV HX HO HI;apply selected_valid_field_exact;rewrite selected_phase_origin.
 eapply actual_valid_expression_phase;[exact data_certificate|exact valid_certificate|exact matches|
 exact coverage|exact HE|exact HV|exact HX| |].
 - apply selected_valid_field_exact;exact HO.
 - intros HValid label HT;apply selected_tag_some in HT as[HT HS];exact(HI HValid label HT HS).
Qed.
End Labels.
End ExtendedSVSelectedCompanion.
Print Assumptions ExtendedSVSelectedCompanion.selected_tag_some.
Print Assumptions ExtendedSVSelectedCompanion.selected_recipe_origin.
Print Assumptions ExtendedSVSelectedCompanion.selected_phase_origin.
Print Assumptions ExtendedSVSelectedCompanion.selected_valid_field_exact.
Print Assumptions ExtendedSVSelectedCompanion.actual_selected_valid_expression_phase.
