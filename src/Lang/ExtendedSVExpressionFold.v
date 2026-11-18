(** Checked expression specialization, including constant and equal-arm cases.
    It changes proof expressions only, never the actual RTL transition. *)
From Coq Require Import List ZArith Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVExprAgreement Lang.ExtendedSVWordInvariant.
Import ListNotations ExtendedSV ExtendedSVExprAgreement ExtendedSVWordInvariant.
Module ExtendedSVExpressionFold.

Definition expression_eq_dec (a b:Expr):{a=b}+{a<>b}.
Proof. decide equality;try apply Z.eq_dec;try apply Nat.eq_dec;decide equality. Defined.

Lemma eval_normalized s e:norm(expr_width e)(eval_expr s e)=eval_expr s e.
Proof. destruct e;cbn[expr_width eval_expr];apply norm_idempotent. Qed.

Definition closed_fold e:=match expr_inputs e with
| []=>EConst(expr_width e)(eval_expr [] e)
| _=>e end.
Lemma closed_fold_width e:expr_width(closed_fold e)=expr_width e.
Proof. unfold closed_fold;destruct(expr_inputs e);reflexivity. Qed.
Lemma closed_fold_sound e s:eval_expr s(closed_fold e)=eval_expr s e.
Proof. unfold closed_fold;destruct(expr_inputs e)eqn:HI;[|reflexivity].
 cbn[eval_expr]. rewrite eval_normalized.
 apply eval_expr_agree;intros w x HX;rewrite HI in HX;contradiction. Qed.

Definition zero_expressionb e:=match e with
| EConst w z=>Z.eqb(norm w z)0|_=>false end.
Lemma zero_expression_sound e s:zero_expressionb e=true ->eval_expr s e=0%Z.
Proof. destruct e;cbn[zero_expressionb];try discriminate.
 intro H;apply Z.eqb_eq in H;exact H. Qed.
Definition logic_fold e:=match e with
| EBinary w BAnd a b=>if zero_expressionb a || zero_expressionb b then EConst w 0 else e
| _=>e end.
Lemma logic_fold_width e:expr_width(logic_fold e)=expr_width e.
Proof. destruct e;try reflexivity. destruct op;try reflexivity.
 cbn[logic_fold];destruct(zero_expressionb e1||zero_expressionb e2);reflexivity. Qed.
Lemma logic_fold_sound e s:eval_expr s(logic_fold e)=eval_expr s e.
Proof. destruct e;try reflexivity. destruct op;try reflexivity.
 cbn[logic_fold]. destruct(zero_expressionb e1||zero_expressionb e2)eqn:HZ;[|reflexivity].
 apply orb_true_iff in HZ as[HZ|HZ];cbn[eval_expr].
 - rewrite(zero_expression_sound e1 s HZ),Z.land_0_l;reflexivity.
 - rewrite(zero_expression_sound e2 s HZ),Z.land_0_r;reflexivity. Qed.

Definition fold_once e:=closed_fold(logic_fold(match e with
| ECond w (EConst gw g) y n=>EExtend w false(if Z.eqb(norm gw g)0 then n else y)
| ECond w _g y n=>if expression_eq_dec y n then EExtend w false y else e
| _=>e end)).
Lemma fold_once_width e:expr_width(fold_once e)=expr_width e.
Proof. unfold fold_once;rewrite closed_fold_width,logic_fold_width.
 destruct e;try reflexivity. destruct e1;try(destruct(expression_eq_dec e2 e3);reflexivity);
 try reflexivity. Qed.
Lemma fold_once_sound e s:eval_expr s(fold_once e)=eval_expr s e.
Proof. unfold fold_once;rewrite closed_fold_sound,logic_fold_sound.
 destruct e;try reflexivity.
 destruct e1;try(destruct(expression_eq_dec e2 e3)as[HE|HE];[subst e3;cbn[eval_expr];destruct(Z.eqb _ _);reflexivity|reflexivity]).
 cbn[eval_expr];destruct(Z.eqb(norm width0 value)0);reflexivity. Qed.

Fixpoint fold_expression e:=fold_once(match e with
| EConst w z=>EConst w z
| EVar w x=>EVar w x
| ESel w a b=>ESel w(fold_expression a)(fold_expression b)
| EConcat w a b=>EConcat w(fold_expression a)(fold_expression b)
| EReplicate w n a=>EReplicate w n(fold_expression a)
| EExtend w sign a=>EExtend w sign(fold_expression a)
| EUnary w op a=>EUnary w op(fold_expression a)
| EBinary w op a b=>EBinary w op(fold_expression a)(fold_expression b)
| ECond w g a b=>ECond w(fold_expression g)(fold_expression a)(fold_expression b)
end).
Lemma fold_expression_width e:expr_width(fold_expression e)=expr_width e.
Proof. destruct e;cbn[fold_expression];rewrite fold_once_width;reflexivity. Qed.
Theorem fold_expression_sound e s:eval_expr s(fold_expression e)=eval_expr s e.
Proof. induction e;cbn[fold_expression];rewrite fold_once_sound;cbn[eval_expr];
 repeat rewrite fold_expression_width;try reflexivity;
 first[now rewrite IHe|now rewrite IHe1,IHe2|now rewrite IHe1,IHe2,IHe3]. Qed.

End ExtendedSVExpressionFold.
Print Assumptions ExtendedSVExpressionFold.closed_fold_sound.
Print Assumptions ExtendedSVExpressionFold.fold_once_sound.
Print Assumptions ExtendedSVExpressionFold.fold_expression_sound.
