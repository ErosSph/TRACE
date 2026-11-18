(** Exact, guard-sensitive value obligations. This constructs a candidate
    relation, not a proof that reachable states satisfy that relation. *)
From Coq Require Import ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVWordInvariant.
Import ExtendedSV ExtendedSVWordInvariant.
Module ExtendedSVValueRequirements.
Fixpoint requirements (width:nat) (expression:Expr) (s:State) (expected:Z):Prop :=
 match expression with
 | ECond w guard yes no =>
   if Nat.eqb w width then
     (eval_expr s guard=0%Z -> requirements width no s expected) /\
     (eval_expr s guard<>0%Z -> requirements width yes s expected)
   else norm width(eval_expr s expression)=expected
 | _ => norm width(eval_expr s expression)=expected
 end.

Theorem requirements_exact expression width s expected:
 requirements width expression s expected <->
 norm width(eval_expr s expression)=expected.
Proof.
 revert width.
 induction expression as
 [w c|w r|w b IHb l IHl|w h IHh l IHl|w count b IHb|
  w signed b IHb|w op b IHb|w op l IHl r IHr|
  w guard IHg yes IHy no IHn];intro width;
 cbn[requirements];try reflexivity.
 destruct(Nat.eqb w width)eqn:HW;[|reflexivity].
 apply Nat.eqb_eq in HW;subst w.
 cbn[eval_expr];rewrite norm_idempotent.
 rewrite IHy,IHn.
 destruct(Z.eqb(eval_expr s guard)0)eqn:HG.
 - apply Z.eqb_eq in HG;tauto.
 - apply Z.eqb_neq in HG;tauto.
Qed.

Theorem actual_output_requirements width root expression fixed expected:
 norm width(read_signal fixed root)=norm width(eval_expr fixed expression) ->
 (requirements width expression fixed expected <->
  norm width(read_signal fixed root)=expected).
Proof. intro H;rewrite requirements_exact,H;reflexivity. Qed.
End ExtendedSVValueRequirements.
Print Assumptions ExtendedSVValueRequirements.requirements_exact.
Print Assumptions ExtendedSVValueRequirements.actual_output_requirements.
