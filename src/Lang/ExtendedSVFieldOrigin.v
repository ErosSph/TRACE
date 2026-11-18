(** Origin transport for narrow pipeline fields, without assuming ISA ownership. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVExprAgreement
 Lang.ExtendedSVScalarHistory Lang.ExtendedSVWordInvariant Lang.ExtendedSVProjectionOrigin Lang.ExtendedSVScalarExpression.
Import ExtendedSV ExtendedSVExprAgreement ExtendedSVScalarHistory
 ExtendedSVWordInvariant ExtendedSVProjectionOrigin ExtendedSVScalarExpression.
Module ExtendedSVFieldOrigin.
Definition field_inputs_onlyb source_width input expression :=
 forallb(fun pair=>Nat.eqb(fst pair)source_width && Nat.eqb(snd pair)input)(expr_inputs expression).
Lemma field_capture_value_sound source_width input expression s value:
 field_inputs_onlyb source_width input expression=true ->
 norm source_width(read_signal s input)=norm source_width value ->
 eval_expr s expression=capture_value input expression value.
Proof.
 intros HC HW;unfold capture_value;apply eval_expr_agree.
 intros width root HI;unfold field_inputs_onlyb in HC.
 apply forallb_forall with(x:=(width,root))in HC;[|exact HI].
 apply andb_true_iff in HC as[HA HB];apply Nat.eqb_eq in HA,HB.
 cbn in HA,HB;subst width root;now rewrite read_signal_write_same.
Qed.
Section Labels.
Context {Label:Type}.
Variable field_value:Label->Z.
Lemma field_recipe_sound source_width width root input capture expression recipe
 (certificate:RecipeMatches width root capture expression recipe)s old incoming label:
 field_inputs_onlyb source_width input capture=true ->
 (forall l,old=Some l ->norm width(read_signal s root)=norm width(capture_value input capture(field_value l))) ->
 (forall l,incoming=Some l ->norm source_width(read_signal s input)=norm source_width(field_value l)) ->
 recipe_origin s recipe old incoming=Some label ->
 norm width(eval_expr s expression)=norm width(capture_value input capture(field_value label)).
Proof.
 intros HC HO HI;induction certificate;cbn[recipe_origin];intro HT.
 - cbn[eval_expr];rewrite norm_idempotent;now apply HO.
 - rewrite(field_capture_value_sound source_width input capture s(field_value label)HC(HI label HT));reflexivity.
 - discriminate.
 - cbn[eval_expr];rewrite norm_idempotent;
   destruct(Z.eqb(eval_expr s guard)0);[now apply IHcertificate2|now apply IHcertificate1].
Qed.
Theorem actual_field_projection_phase source_width p root width proc expression input capture recipe
 (scalar:ScalarCertificate p root width proc expression)
 (certificate:RecipeMatches width root capture expression recipe)ev pre old incoming label:
 changed_signal ev<>root ->field_inputs_onlyb source_width input capture=true ->
 (forall l,old=Some l ->norm width(read_signal pre root)=norm width(capture_value input capture(field_value l))) ->
 (forall l,incoming=Some l ->norm source_width(read_signal(phase_driven_state p ev pre)input)=norm source_width(field_value l)) ->
 projection_phase_origin p proc recipe ev pre old incoming=Some label ->
 norm width(read_signal(PhaseSemantics p ev pre)root)=norm width(capture_value input capture(field_value label)).
Proof.
 intros HE HC HO HI HT;rewrite(history_phase_projection _ _ _ _ _ scalar ev pre HE).
 unfold projection_phase_origin in HT.
 destruct(process_matches_states pre(phase_driven_state p ev pre)proc).
 - eapply field_recipe_sound;[exact certificate|exact HC| |exact HI|exact HT].
   intros l HL;rewrite(sampled_root_preserved p ev pre root(history_comb_frame _ _ _ _ _ scalar)HE);now apply HO.
 - now apply HO.
Qed.
End Labels.
End ExtendedSVFieldOrigin.
Print Assumptions ExtendedSVFieldOrigin.actual_field_projection_phase.
