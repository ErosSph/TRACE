(** Transport a companion field using the SAME origin recipe as its token. *)
From Coq Require Import ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVScalarHistory Lang.ExtendedSVScalarExpression
 Lang.ExtendedSVWordInvariant Lang.ExtendedSVProjectionOrigin.
Import ExtendedSV ExtendedSVScalarHistory ExtendedSVScalarExpression ExtendedSVWordInvariant ExtendedSVProjectionOrigin.
Module ExtendedSVCompanionField.
Section Field.
Context {Label:Type}.
Variable value:Label->option Z.
(* The capture expression need not be a wire: it can be an ALU result.
   Its ISA interpretation is an explicit obligation at the sampled state. *)
Definition ExpressionRelated width expression s(tag:option Label):=
 forall label,tag=Some label ->
 value label=Some(norm width(eval_expr s expression)).
Definition FieldRelated width root s(tag:option Label):=
 forall label,tag=Some label ->
 value label=Some(norm width(read_signal s root)).

Lemma expression_recipe_sound width root capture expression recipe
 (cert:RecipeMatches width root capture expression recipe)s old incoming:
 FieldRelated width root s old ->ExpressionRelated width capture s incoming ->
 ExpressionRelated width expression s(recipe_origin s recipe old incoming).
Proof.
 intros HO HI;induction cert;intros label HT.
 - cbn[recipe_origin]in HT;cbn[eval_expr];rewrite norm_idempotent;now apply HO.
 - now apply HI.
 - discriminate.
 - cbn[recipe_origin]in HT;cbn[eval_expr];rewrite norm_idempotent.
   destruct(Z.eqb(eval_expr s guard)0);[now apply IHcert2|now apply IHcert1].
Qed.

Theorem actual_expression_phase p root width proc capture expression recipe
 (scalar:ScalarCertificate p root width proc expression)
 (cert:RecipeMatches width root capture expression recipe)ev pre old incoming:
 changed_signal ev<>root ->FieldRelated width root pre old ->
 ExpressionRelated width capture(phase_driven_state p ev pre)incoming ->
 FieldRelated width root(PhaseSemantics p ev pre)
  (projection_phase_origin p proc recipe ev pre old incoming).
Proof.
 intros HE HO HI label HT;rewrite(history_phase_projection _ _ _ _ _ scalar ev pre HE).
 unfold projection_phase_origin in HT;destruct(process_matches_states pre(phase_driven_state p ev pre)proc).
 - eapply expression_recipe_sound;[exact cert| |exact HI|exact HT].
   intros t H;rewrite(sampled_root_preserved p ev pre root(history_comb_frame _ _ _ _ _ scalar)HE);now apply HO.
 - now apply HO.
Qed.

Definition Related root s(tag:option Label):=forall label,tag=Some label ->value label=Some(norm 32(read_signal s root)).

Lemma recipe_sound root input expression recipe
 (cert:RecipeMatches 32 root(EVar 32 input)expression recipe)s old incoming:
 Related root s old ->Related input s incoming ->forall label,
 recipe_origin s recipe old incoming=Some label ->value label=Some(norm 32(eval_expr s expression)).
Proof.
 intros HO HI;induction cert;intros label HT.
 - cbn[recipe_origin]in HT;cbn[eval_expr];rewrite norm_idempotent;now apply HO.
 - cbn[recipe_origin]in HT;cbn[eval_expr];rewrite norm_idempotent;now apply HI.
 - discriminate.
 - cbn[recipe_origin]in HT;cbn[eval_expr];rewrite norm_idempotent.
   destruct(Z.eqb(eval_expr s guard)0);[now apply IHcert2|now apply IHcert1].
Qed.

Theorem actual_phase p root input proc expression recipe
 (scalar:ScalarCertificate p root 32 proc expression)
 (cert:RecipeMatches 32 root(EVar 32 input)expression recipe)ev pre old incoming:
 changed_signal ev<>root ->Related root pre old ->Related input(phase_driven_state p ev pre)incoming ->
 Related root(PhaseSemantics p ev pre)(projection_phase_origin p proc recipe ev pre old incoming).
Proof.
 intros HE HO HI.
 eapply actual_expression_phase;[exact scalar|exact cert|exact HE|exact HO|].
 intros label HT;cbn[eval_expr];rewrite norm_idempotent;now apply HI.
Qed.
End Field.
End ExtendedSVCompanionField.
Print Assumptions ExtendedSVCompanionField.actual_phase.
Print Assumptions ExtendedSVCompanionField.actual_expression_phase.
