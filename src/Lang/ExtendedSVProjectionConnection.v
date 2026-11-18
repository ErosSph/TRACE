(** Checked combinational substitution feeding an actual scalar capture.
    This is a dependency connection rule, not an ISA/CPU correctness premise. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVProjectionOrigin
 Lang.ExtendedSVScalarHistory Lang.ExtendedSVScalarExpression Lang.ExtendedSVWordInvariant.
Import ExtendedSV ExtendedSVProjectionOrigin ExtendedSVScalarHistory
 ExtendedSVScalarExpression ExtendedSVWordInvariant.
Module ExtendedSVProjectionConnection.

Fixpoint substitute (sigma:nat->signal->option Expr) e := match e with
| EConst w z=>EConst w z
| EVar w x=>match sigma w x with Some rhs=>EExtend w false rhs|None=>EVar w x end
| ESel w a b=>ESel w(substitute sigma a)(substitute sigma b)
| EConcat w a b=>EConcat w(substitute sigma a)(substitute sigma b)
| EReplicate w n a=>EReplicate w n(substitute sigma a)
| EExtend w sign a=>EExtend w sign(substitute sigma a)
| EUnary w op a=>EUnary w op(substitute sigma a)
| EBinary w op a b=>EBinary w op(substitute sigma a)(substitute sigma b)
| ECond w g a b=>ECond w(substitute sigma g)(substitute sigma a)(substitute sigma b)
end.

Theorem substitute_width sigma e : expr_width(substitute sigma e)=expr_width e.
Proof.
 destruct e as[w z|w x|w a b|w a b|w n a|w sign a|w op a|w op a b|w g a b];
 cbn[substitute expr_width];try reflexivity.
 destruct(sigma w x);reflexivity.
Qed.

Theorem substitute_sound sigma e s :
 (forall w x rhs,sigma w x=Some rhs ->
   norm w(read_signal s x)=norm w(eval_expr s rhs)) ->
 eval_expr s(substitute sigma e)=eval_expr s e.
Proof.
 intros HC;induction e;cbn[substitute eval_expr].
 - reflexivity.
 - destruct(sigma width id)as[rhs|]eqn:HE;cbn[eval_expr];[symmetry;now apply HC|reflexivity].
 - now rewrite IHe1,IHe2.
 - now rewrite substitute_width,IHe1,IHe2.
 - now rewrite substitute_width,IHe.
 - now rewrite substitute_width,IHe.
 - now rewrite IHe.
 - now rewrite !substitute_width,IHe1,IHe2.
 - now rewrite IHe1,IHe2,IHe3.
Qed.

Record Binding := { binding_width:nat; binding_root:signal; binding_expr:Expr }.
Fixpoint lookup_binding (bindings:list Binding) width root := match bindings with
| nil=>None
| entry::rest=>if Nat.eqb width(binding_width entry)&&Nat.eqb root(binding_root entry)
  then Some(binding_expr entry) else lookup_binding rest width root end.
Definition BindingsAgree s bindings := Forall(fun entry=>
 norm(binding_width entry)(read_signal s(binding_root entry))=
 norm(binding_width entry)(eval_expr s(binding_expr entry)))bindings.

Theorem lookup_binding_sound s bindings : BindingsAgree s bindings ->
 forall width root rhs,lookup_binding bindings width root=Some rhs ->
 norm width(read_signal s root)=norm width(eval_expr s rhs).
Proof.
 intros HA;induction HA as[|entry rest Hentry Hrest IH];intros width root rhs HL.
 - discriminate.
 - cbn[lookup_binding]in HL.
   destruct(Nat.eqb width(binding_width entry)&&Nat.eqb root(binding_root entry))eqn:HC.
   + apply andb_true_iff in HC as[HW HR];apply Nat.eqb_eq in HW,HR.
     inversion HL;subst width root rhs;exact Hentry.
   + now apply IH.
Qed.

Corollary bindings_substitute_sound bindings e s : BindingsAgree s bindings ->
 eval_expr s(substitute(lookup_binding bindings)e)=eval_expr s e.
Proof. intro HA;apply substitute_sound;now apply lookup_binding_sound. Qed.

Section Origins.
Context {Label:Type}.
Variable reference:Label->Z.

Theorem connected_recipe_sound width root capture expression recipe
 (certificate:RecipeMatches width root capture expression recipe) s old incoming label :
 (forall l,old=Some l ->norm width(read_signal s root)=reference l) ->
 (forall l,incoming=Some l ->norm width(eval_expr s capture)=reference l) ->
 @recipe_origin Label s recipe old incoming=Some label ->
 norm width(eval_expr s expression)=reference label.
Proof.
 intros Hold Hinput;induction certificate;cbn[recipe_origin];intro HT.
 - cbn[eval_expr]. rewrite norm_idempotent;now apply Hold.
 - now apply Hinput.
 - discriminate.
 - cbn[eval_expr]. destruct(Z.eqb(eval_expr s guard)0).
   + rewrite norm_idempotent;now apply IHcertificate2.
   + rewrite norm_idempotent;now apply IHcertificate1.
Qed.

Theorem connected_actual_phase p root width proc expression capture recipe
 (scalar:ScalarCertificate p root width proc expression)
 (certificate:RecipeMatches width root capture expression recipe) ev pre old incoming label :
 changed_signal ev<>root ->
 (forall l,old=Some l ->norm width(read_signal pre root)=reference l) ->
 (forall l,incoming=Some l ->
   norm width(eval_expr(phase_driven_state p ev pre)capture)=reference l) ->
 @projection_phase_origin Label p proc recipe ev pre old incoming=Some label ->
 norm width(read_signal(PhaseSemantics p ev pre)root)=reference label.
Proof.
 intros HE Hold Hinput HT.
 rewrite(history_phase_projection _ _ _ _ _ scalar ev pre HE).
 unfold projection_phase_origin in HT.
 destruct(process_matches_states pre(phase_driven_state p ev pre)proc).
 - eapply connected_recipe_sound;[exact certificate| |exact Hinput|exact HT].
   intros l Hl;rewrite(sampled_root_preserved p ev pre root
     (history_comb_frame _ _ _ _ _ scalar)HE);now apply Hold.
 - now apply Hold.
Qed.
End Origins.
Print Assumptions substitute_width.
Print Assumptions substitute_sound.
Print Assumptions lookup_binding_sound.
Print Assumptions bindings_substitute_sound.
Print Assumptions connected_recipe_sound.
Print Assumptions connected_actual_phase.
End ExtendedSVProjectionConnection.
