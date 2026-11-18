(** Exact algebraic identity of the original four byte expression families.
    The sampled-state argument is arbitrary; no CPU comparison result or
    expected ISA operand is a premise. All byte offsets are covered. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVBitSlice
  Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiAdderBits
  Ex.External.CV32E40PAddiIDEXAccept Ex.External.CV32E40PCompareByteCone
  Ex.External.CV32E40PCompareWordPacking Ex.External.CV32E40PCompareByteArithmetic.
Import ListNotations ExtendedSV ExtendedSVBitSlice CV32E40PExtendedAST
  CV32E40PAddiAdderBits CV32E40PAddiIDEXAccept CV32E40PCompareByteCone
  CV32E40PCompareWordPacking CV32E40PCompareByteArithmetic.
Local Open Scope Z_scope.
Local Opaque read_signal.
Module CV32E40PCompareExpressionIdentity.
Lemma norm_bool_bit b : norm 1 (boolz b) = boolz b.
Proof. destruct b; reflexivity. Qed.
Lemma normalize_word_slice x w off : 0 <= off -> off+Z.of_nat w <= 32 ->
  norm w (Z.shiftr (norm 32 x) off) = norm w (Z.shiftr x off).
Proof.
  intros HO HW. change (read_slice (norm 32 x) off (Z.of_nat w) =
    read_slice x off (Z.of_nat w)). apply slice_norm; lia.
Qed.
Lemma normalize_mode_slice x off : 0 <= off -> off+1 <= 4 ->
  norm 1 (Z.shiftr (norm 4 x) off) = read_slice x off 1.
Proof.
  intros HO HW. change (read_slice (norm 4 x) off 1 = read_slice x off 1).
  apply slice_norm; lia.
Qed.
Ltac constant_offsets :=
  try change (norm 5 0) with 0; try change (norm 5 8) with 8;
  try change (norm 5 16) with 16; try change (norm 5 24) with 24;
  try change (norm 5 7) with 7; try change (norm 5 15) with 15;
  try change (norm 5 23) with 23; try change (norm 5 31) with 31;
  try change (norm 2 0) with 0; try change (norm 2 1) with 1;
  try change (norm 2 2) with 2; try change (norm 2 3) with 3.
Theorem original_equal_expression s n : (n < 4)%nat ->
  norm 1 (eval_expr s (assigned_expr (eq_process n))) =
    boolz (Z.eqb (byte_at (read_signal s 1304%nat) (8*Z.of_nat n))
                 (byte_at (read_signal s 1305%nat) (8*Z.of_nat n))).
Proof.
  intros HN. destruct n as [|[|[|[|n]]]]; try lia;
    cbn [eq_process assigned_expr process_563 process_564 process_565 process_566
      process_body eval_expr]; constant_offsets;
    rewrite !normalize_word_slice by lia;
    rewrite !norm_bool_bit; reflexivity.
Qed.
Theorem original_greater_expression s n : (n < 4)%nat ->
  norm 1 (eval_expr s (assigned_expr (greater_process n))) =
    boolz (Z.gtb
      (compare_byte_value (read_signal s 1304%nat) (8*Z.of_nat n)
        (read_slice (read_signal s 1352%nat) (Z.of_nat n) 1))
      (compare_byte_value (read_signal s 1305%nat) (8*Z.of_nat n)
        (read_slice (read_signal s 1352%nat) (Z.of_nat n) 1))).
Proof.
  intros HN. destruct n as [|[|[|[|n]]]]; try lia;
    cbn [greater_process assigned_expr process_587 process_588 process_589 process_590
      process_body eval_expr expr_width]; constant_offsets;
    rewrite !normalize_word_slice by lia; rewrite !norm_bool_bit;
    rewrite !normalize_mode_slice by lia;
    unfold compare_byte_value, byte_at; reflexivity.
Qed.
Print Assumptions original_equal_expression.
Print Assumptions original_greater_expression.
End CV32E40PCompareExpressionIdentity.
