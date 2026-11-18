From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVExprAgreement.
Import ExtendedSV ExtendedSVExprAgreement ListNotations.
Module ExtendedSVTwoInputExpression.
Definition only_two wx x wy y e := forallb(fun pair=>
 (Nat.eqb(fst pair)wx && Nat.eqb(snd pair)x) ||
 (Nat.eqb(fst pair)wy && Nat.eqb(snd pair)y))(expr_inputs e).
Definition frame x vx y vy := write_signal(write_signal [] x vx)y vy.

Theorem evaluate wx x wy y e s vx vy:
 x<>y ->only_two wx x wy y e=true ->
 norm wx(read_signal s x)=norm wx vx ->
 norm wy(read_signal s y)=norm wy vy ->
 eval_expr s e=eval_expr(frame x vx y vy)e.
Proof.
 intros Hxy HC HX HY;apply eval_expr_agree;intros w r HI.
 unfold only_two in HC;apply forallb_forall with(x:=(w,r))in HC;[|exact HI].
 cbn in HC;apply orb_true_iff in HC;destruct HC as[HC|HC];
 apply andb_true_iff in HC as[HW HR];apply Nat.eqb_eq in HW,HR;subst w r;
 unfold frame.
 - rewrite read_signal_write_other by congruence;rewrite read_signal_write_same;exact HX.
 - rewrite read_signal_write_same;exact HY.
Qed.
End ExtendedSVTwoInputExpression.
Print Assumptions ExtendedSVTwoInputExpression.evaluate.
