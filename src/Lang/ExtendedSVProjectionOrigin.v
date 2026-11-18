(** Instruction-origin transport through computed/decoded scalar fields.
    The reference function is derived from the actual capture expression,
    not from an existing CPU invariant. Unknown is NOT an invalid slot. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVExprAgreement
 Lang.ExtendedSVScalarHistory Lang.ExtendedSVWordInvariant Lang.ExtendedSVScalarExpression.
Import ListNotations ExtendedSV ExtendedSVExprAgreement ExtendedSVScalarHistory ExtendedSVWordInvariant
 ExtendedSVScalarExpression.
Local Open Scope Z_scope.
Module ExtendedSVProjectionOrigin.

Definition capture_inputs_onlyb input expression :=
 forallb (fun pair=>Nat.eqb(fst pair)32 && Nat.eqb(snd pair)input) (expr_inputs expression).
Definition capture_value input expression word :=
 eval_expr (write_signal [] input word) expression.

Theorem capture_value_sound input expression s word :
 capture_inputs_onlyb input expression=true ->
 norm 32(read_signal s input)=norm 32 word ->
 eval_expr s expression=capture_value input expression word.
Proof.
 intros HC HW. unfold capture_value. apply eval_expr_agree.
 intros width root HI. unfold capture_inputs_onlyb in HC.
 apply forallb_forall with(x:=(width,root))in HC;[|exact HI].
 apply andb_true_iff in HC as[Hwidth Hroot].
 apply Nat.eqb_eq in Hwidth,Hroot. cbn in Hwidth,Hroot.
 subst width root. rewrite read_signal_write_same. exact HW.
Qed.

Inductive OriginRecipe := Hold | Capture | Unknown | Select (guard:Expr)(yes no:OriginRecipe).
Inductive RecipeMatches width root capture : Expr -> OriginRecipe -> Prop :=
| MatchesHold : RecipeMatches width root capture (EVar width root) Hold
| MatchesCapture : RecipeMatches width root capture capture Capture
| MatchesUnknown : forall e, RecipeMatches width root capture e Unknown
| MatchesSelect : forall guard yes no ry rn,
 RecipeMatches width root capture yes ry ->RecipeMatches width root capture no rn ->
 RecipeMatches width root capture (ECond width guard yes no)(Select guard ry rn).

Section Labels.
Context {Label:Type}.
Variable instruction_word:Label->Z.
Fixpoint recipe_origin s recipe (old incoming:option Label) := match recipe with
| Hold=>old | Capture=>incoming | Unknown=>None
| Select guard yes no=>if Z.eqb(eval_expr s guard)0
 then recipe_origin s no old incoming else recipe_origin s yes old incoming end.

Theorem recipe_value_sound width root input capture expression recipe
 (certificate:RecipeMatches width root capture expression recipe) s old incoming label :
 capture_inputs_onlyb input capture=true ->
 (forall l,old=Some l ->norm width(read_signal s root)=
   norm width(capture_value input capture(instruction_word l))) ->
 (forall l,incoming=Some l ->norm 32(read_signal s input)=norm 32(instruction_word l)) ->
 recipe_origin s recipe old incoming=Some label ->
 norm width(eval_expr s expression)=norm width(capture_value input capture(instruction_word label)).
Proof.
 intros HC Hold Hinput. induction certificate;cbn[recipe_origin];intro HT.
 - cbn[eval_expr]. rewrite norm_idempotent. now apply Hold.
 - rewrite(capture_value_sound input capture s(instruction_word label) HC(Hinput label HT)). reflexivity.
 - discriminate.
 - cbn[eval_expr]. destruct(Z.eqb(eval_expr s guard)0).
   + rewrite norm_idempotent. now apply IHcertificate2.
   + rewrite norm_idempotent. now apply IHcertificate1.
Qed.

Definition projection_phase_origin p proc recipe ev pre old incoming :=
 if process_matches_states pre(phase_driven_state p ev pre)proc
 then recipe_origin(phase_driven_state p ev pre)recipe old incoming else old.

Theorem actual_projection_phase p root width proc expression input capture recipe
 (scalar:ScalarCertificate p root width proc expression)
 (certificate:RecipeMatches width root capture expression recipe) ev pre old incoming label :
 changed_signal ev<>root ->capture_inputs_onlyb input capture=true ->
 (forall l,old=Some l ->norm width(read_signal pre root)=
   norm width(capture_value input capture(instruction_word l))) ->
 (forall l,incoming=Some l ->norm 32(read_signal(phase_driven_state p ev pre)input)=
   norm 32(instruction_word l)) ->
 projection_phase_origin p proc recipe ev pre old incoming=Some label ->
 norm width(read_signal(PhaseSemantics p ev pre)root)=
 norm width(capture_value input capture(instruction_word label)).
Proof.
 intros HE HC Hold Hinput HT.
 rewrite(history_phase_projection _ _ _ _ _ scalar ev pre HE).
 unfold projection_phase_origin in HT.
 destruct(process_matches_states pre(phase_driven_state p ev pre)proc).
 - eapply recipe_value_sound;[exact certificate|exact HC| |exact Hinput|exact HT].
   intros l Hl. rewrite(sampled_root_preserved p ev pre root
     (history_comb_frame _ _ _ _ _ scalar)HE). now apply Hold.
 - now apply Hold.
Qed.
End Labels.
Print Assumptions capture_value_sound.
Print Assumptions recipe_value_sound.
Print Assumptions actual_projection_phase.
End ExtendedSVProjectionOrigin.
