(** Boolean meaning of the actual scalar comparison combination expressions.
    The input equal/greater bits remain explicit until wired to FullCore. *)
From Coq Require Import ZArith Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVBitSlice
  Ex.External.CV32E40PAddiAdderBits Ex.External.CV32E40PCompareCombineCone.
Import ExtendedSV ExtendedSVBitSlice CV32E40PAddiAdderBits CV32E40PCompareCombineCone.
Local Open Scope Z_scope.
Module CV32E40PCompareBooleanCombine.

Definition repeated_bit (b : bool) : Z := if b then 15 else 0.
Lemma boolean_and a b : Z.land (boolz a) (boolz b) = boolz (andb a b).
Proof. destruct a,b; reflexivity. Qed.
Lemma boolean_or a b : Z.lor (boolz a) (boolz b) = boolz (orb a b).
Proof. destruct a,b; reflexivity. Qed.
Lemma boolean_norm b : norm 1 (boolz b) = boolz b.
Proof. destruct b; reflexivity. Qed.
Lemma repeated_boolean b : norm 4 (replicate_bits 4 1 (boolz b)) = repeated_bit b.
Proof. destruct b; reflexivity. Qed.
Lemma four_bit_read x off : 0 <= off < 4 ->
  norm 1 (Z.shiftr (norm 4 x) off) = read_slice x off 1.
Proof.
  intros. change (read_slice (norm 4 x) off 1 = read_slice x off 1).
  apply slice_norm; lia.
Qed.

Lemma equal_expression_boolean s e3 e2 e1 e0 :
  read_slice (read_signal s 1353%nat) 3 1 = boolz e3 ->
  read_slice (read_signal s 1353%nat) 2 1 = boolz e2 ->
  read_slice (read_signal s 1353%nat) 1 1 = boolz e1 ->
  read_slice (read_signal s 1353%nat) 0 1 = boolz e0 ->
  norm 4 (eval_expr s equal_expression) =
    repeated_bit (andb (andb (andb e3 e2) e1) e0).
Proof.
  intros H3 H2 H1 H0. unfold equal_expression.
  cbn [Ex.Generated.CV32E40PExtendedAST.CV32E40PExtendedAST.process_591
    process_body eval_expr expr_width].
  change (norm 2 3) with 3. change (norm 2 2) with 2.
  change (norm 2 1) with 1. change (norm 2 0) with 0.
  rewrite !four_bit_read by lia. rewrite H3,H2,H1,H0.
  repeat first [rewrite boolean_and | rewrite boolean_norm].
  rewrite CV32E40PAddiIDEXAccept.CV32E40PAddiIDEXAccept.norm_twice.
  apply repeated_boolean.
Qed.

Lemma greater_expression_boolean s e3 e2 e1 g3 g2 g1 g0 :
  read_slice (read_signal s 1353%nat) 3 1 = boolz e3 ->
  read_slice (read_signal s 1353%nat) 2 1 = boolz e2 ->
  read_slice (read_signal s 1353%nat) 1 1 = boolz e1 ->
  read_slice (read_signal s 1354%nat) 3 1 = boolz g3 ->
  read_slice (read_signal s 1354%nat) 2 1 = boolz g2 ->
  read_slice (read_signal s 1354%nat) 1 1 = boolz g1 ->
  read_slice (read_signal s 1354%nat) 0 1 = boolz g0 ->
  norm 4 (eval_expr s greater_expression) =
    repeated_bit (orb g3 (andb e3 (orb g2 (andb e2 (orb g1 (andb e1 g0)))))).
Proof.
  intros HE3 HE2 HE1 HG3 HG2 HG1 HG0. unfold greater_expression.
  cbn [Ex.Generated.CV32E40PExtendedAST.CV32E40PExtendedAST.process_591
    process_body eval_expr expr_width].
  change (norm 2 3) with 3. change (norm 2 2) with 2.
  change (norm 2 1) with 1. change (norm 2 0) with 0.
  rewrite !four_bit_read by lia. rewrite HE3,HE2,HE1,HG3,HG2,HG1,HG0.
  repeat first [rewrite boolean_and | rewrite boolean_or | rewrite boolean_norm].
  rewrite CV32E40PAddiIDEXAccept.CV32E40PAddiIDEXAccept.norm_twice.
  apply repeated_boolean.
Qed.
Lemma less_bit_boolean g e :
  read_slice (norm 4 (Z.lnot (Z.lor (repeated_bit g) (repeated_bit e)))) 3 1 =
    boolz (negb (orb g e)).
Proof. destruct g,e; reflexivity. Qed.
Print Assumptions equal_expression_boolean.
Print Assumptions greater_expression_boolean.
End CV32E40PCompareBooleanCombine.
