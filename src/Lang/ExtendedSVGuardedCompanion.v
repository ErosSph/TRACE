From Coq Require Import ZArith Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVProjectionOrigin Lang.ExtendedSVCompanionField
 Lang.ExtendedSVScalarHistory Lang.ExtendedSVScalarExpression Lang.ExtendedSVWordInvariant.
Import ExtendedSV ExtendedSVProjectionOrigin ExtendedSVCompanionField ExtendedSVScalarHistory
 ExtendedSVScalarExpression ExtendedSVWordInvariant.
Module ExtendedSVGuardedCompanion.
Lemma norm_one_nonzero v:norm 1 v<>0%Z ->norm 1 v=1%Z.
Proof.
 change(Z.land v(Z.ones 1)<>0%Z ->Z.land v(Z.ones 1)=1%Z).
 rewrite !Z.land_ones by lia.
 change(v mod 2<>0 ->v mod 2=1)%Z.
 pose proof(Z.mod_pos_bound v 2 ltac:(lia));lia.
Qed.
Fixpoint captures s recipe:=match recipe with
| Capture=>true | Hold | Unknown=>false
| Select guard yes no=>if Z.eqb(eval_expr s guard)0 then captures s no else captures s yes end.
Lemma select_capture_nonzero s guard:
 captures s(Select guard Capture Unknown)=true ->eval_expr s guard<>0%Z.
Proof.
 cbn[captures];destruct(Z.eqb(eval_expr s guard)0)eqn:H;[discriminate|].
 intros _;now apply Z.eqb_neq.
Qed.

Lemma recipe_sound {Label} (value:Label->option Z) width root capture expression recipe
 (cert:RecipeMatches width root capture expression recipe) s old incoming:
 FieldRelated value width root s old ->
 (captures s recipe=true ->ExpressionRelated value width capture s incoming) ->
 ExpressionRelated value width expression s(recipe_origin s recipe old incoming).
Proof.
 intros HO;induction cert;intros HI label HT.
 - cbn[recipe_origin]in HT;cbn[eval_expr];rewrite norm_idempotent;now apply HO.
 - exact(HI eq_refl label HT).
 - discriminate.
 - cbn[captures]in HI;cbn[recipe_origin]in HT;cbn[eval_expr];rewrite norm_idempotent.
   destruct(Z.eqb(eval_expr s guard)0);[exact(IHcert2 HI label HT)|exact(IHcert1 HI label HT)].
Qed.

Theorem actual_phase {Label} (value:Label->option Z) p root width proc capture expression recipe
 (scalar:ScalarCertificate p root width proc expression)
 (cert:RecipeMatches width root capture expression recipe) ev pre old incoming:
 changed_signal ev<>root ->FieldRelated value width root pre old ->
 (captures(phase_driven_state p ev pre)recipe=true ->
 ExpressionRelated value width capture(phase_driven_state p ev pre)incoming) ->
 FieldRelated value width root(PhaseSemantics p ev pre)
 (projection_phase_origin p proc recipe ev pre old incoming).
Proof.
 intros HE HO HI label HT;rewrite(history_phase_projection _ _ _ _ _ scalar ev pre HE).
 unfold projection_phase_origin in HT;destruct(process_matches_states pre(phase_driven_state p ev pre)proc).
 - eapply recipe_sound;[exact cert| |exact HI|exact HT].
   intros t HH;rewrite(sampled_root_preserved p ev pre root(history_comb_frame _ _ _ _ _ scalar)HE);now apply HO.
 - now apply HO.
Qed.
End ExtendedSVGuardedCompanion.
Print Assumptions ExtendedSVGuardedCompanion.actual_phase.
