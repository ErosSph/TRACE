From Coq Require Import ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVOneBitOrPath.
Import ExtendedSV ExtendedSVOneBitOrPath.
Module ExtendedSVBooleanWitness.
Lemma and_true s a b:eval_expr s a=1%Z ->eval_expr s b=1%Z ->
 eval_expr s(EBinary 1 BAnd a b)=1%Z.
Proof. intros HA HB;cbn[eval_expr];rewrite HA,HB;reflexivity. Qed.
Lemma or_true_left s a b:eval_expr s a=1%Z ->eval_expr s(EBinary 1 BOr a b)=1%Z.
Proof. intro HA;cbn[eval_expr];rewrite HA;apply one_or_left. Qed.
Lemma or_true_right s a b:eval_expr s b=1%Z ->eval_expr s(EBinary 1 BOr a b)=1%Z.
Proof. intro HB;cbn[eval_expr];rewrite HB;apply one_or_right. Qed.
End ExtendedSVBooleanWitness.
Print Assumptions ExtendedSVBooleanWitness.and_true.
