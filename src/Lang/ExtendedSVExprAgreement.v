(** Normalized-width dependencies for the actual ExtendedSV evaluator.
    This is a binary evaluator congruence, NOT four-state knownness.
    A guarded branch may ignore only the branch the actual guard does not select. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV.
Import ExtendedSV ListNotations.
Local Open Scope Z_scope.
Module ExtendedSVExprAgreement.

Fixpoint expr_inputs (e : Expr) : list (nat * signal) :=
 match e with
 | EConst _ _ => []
 | EVar w x => [(w,x)]
 | ESel _ a b | EConcat _ a b | EBinary _ _ a b => expr_inputs a ++ expr_inputs b
 | EReplicate _ _ a | EExtend _ _ a | EUnary _ _ a => expr_inputs a
 | ECond _ g a b => expr_inputs g ++ expr_inputs a ++ expr_inputs b
 end.
Definition InputsAgree (s t : State) (inputs : list (nat * signal)) : Prop :=
 forall w x, In (w,x) inputs -> norm w (read_signal s x)=norm w (read_signal t x).

Lemma agree_app_left s t a b : InputsAgree s t (a++b) -> InputsAgree s t a.
Proof. intros H w x Hin. apply H. apply in_or_app. now left. Qed.
Lemma agree_app_right s t a b : InputsAgree s t (a++b) -> InputsAgree s t b.
Proof. intros H w x Hin. apply H. apply in_or_app. now right. Qed.

Theorem eval_expr_agree e s t : InputsAgree s t (expr_inputs e) ->
 eval_expr s e = eval_expr t e.
Proof.
 induction e; cbn [expr_inputs eval_expr]; intro H.
 - reflexivity.
 - apply H. now left.
 - rewrite IHe1, IHe2; [reflexivity| | ];
   eauto using agree_app_left, agree_app_right.
 - rewrite IHe1, IHe2; [reflexivity| | ];
   eauto using agree_app_left, agree_app_right.
 - now rewrite IHe.
 - now rewrite IHe.
 - now rewrite IHe.
 - rewrite IHe1, IHe2; [reflexivity| | ];
   eauto using agree_app_left, agree_app_right.
 - rewrite IHe1, IHe2, IHe3; [reflexivity| | | ];
   eauto using agree_app_left, agree_app_right.
Qed.

Theorem selected_yes_agree w g yes no s t :
 InputsAgree s t (expr_inputs g) ->
 InputsAgree s t (expr_inputs yes) ->
 Z.eqb (eval_expr s g) 0=false ->
 eval_expr s (ECond w g yes no)=eval_expr t (ECond w g yes no).
Proof.
 intros HG HY HC. cbn [eval_expr].
 rewrite <- (eval_expr_agree g s t HG), HC.
 now rewrite (eval_expr_agree yes s t HY).
Qed.
Theorem selected_no_agree w g yes no s t :
 InputsAgree s t (expr_inputs g) ->
 InputsAgree s t (expr_inputs no) ->
 Z.eqb (eval_expr s g) 0=true ->
 eval_expr s (ECond w g yes no)=eval_expr t (ECond w g yes no).
Proof.
 intros HG HN HC. cbn [eval_expr].
 rewrite <- (eval_expr_agree g s t HG), HC.
 now rewrite (eval_expr_agree no s t HN).
Qed.
End ExtendedSVExprAgreement.
Print Assumptions ExtendedSVExprAgreement.eval_expr_agree.
Print Assumptions ExtendedSVExprAgreement.selected_yes_agree.
