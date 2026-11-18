(** Original compare signedness, less-than selection and output bit.  These
    are structural RTL certificates, not a claim that byte comparison already
    equals ISA signed/unsigned comparison.  The arithmetic bridge is separate. *)
From Coq Require Import ZArith List Bool Lia btauto.Btauto.
Require Import Lang.ExtendedSV Lang.ExtendedSVBlocking Lang.ExtendedSVRootProjection
  Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiDecoder
  Ex.External.CV32E40PAddiWritebackMux Ex.External.CV32E40PAddiIDEXAccept
  Ex.External.CV32E40PAddiForwardControl Ex.External.CV32E40PScalarMuxSlt.
Require Import Ex.External.CV32E40PAddiOperands.
Import CV32E40PAddiOperands.
Require Import Ex.External.CV32E40PAddiAdderInputs.
Import CV32E40PAddiAdderInputs.
Require Import Lang.ExtendedSVBitSlice Ex.External.CV32E40PAddiAdderBits.
Import ExtendedSVBitSlice CV32E40PAddiAdderBits.
Import ListNotations ExtendedSV ExtendedSVBlocking ExtendedSVRootProjection
  CV32E40PExtendedAST CV32E40PAddiDecoder CV32E40PAddiWritebackMux
  CV32E40PAddiIDEXAccept CV32E40PAddiForwardControl CV32E40PScalarMuxSlt.
Local Open Scope Z_scope.
Module CV32E40PCompareControlCone.

Lemma norm_not_idempotent w x : norm w (Z.lnot (norm w x)) = norm w (Z.lnot x).
Proof.
  unfold norm. apply Z.bits_inj. intro bit.
  destruct (Z_lt_ge_dec bit 0).
  - now rewrite !Z.testbit_neg_r by lia.
  - rewrite !Z.land_spec, !Z.lnot_spec, !Z.land_spec by lia. btauto.
Qed.

Lemma actual_signed_compare_mode s :
  norm 7 (read_signal s 1303%nat) = 2 -> norm 2 (read_signal s 1307%nat) = 0 ->
  norm 4 (read_signal (run_process cv32e40p_program s process_586) 1352%nat) = 8.
Proof.
  intros HO HV. rewrite blocking_run_process by reflexivity.
  change (statement_fuel cv32e40p_program) with 512%nat.
  cbn [process_586 process_body].
  rewrite exec_sequence, fold_one, exec_sequence, fold_two, exec_case.
  cbn [eval_expr].
  rewrite (preserves_inputs 510 (SAssign false (EConst 4 0) (LVar 4 1352%nat))
    _ 1303%nat eq_refl). cbn [blocking_state]. rewrite HO.
  cbn [select_case_stmt eval_expr].
  change (norm 7 8) with 8. change (norm 7 10) with 10.
  change (norm 7 0) with 0. change (norm 7 4) with 4.
  change (norm 7 2) with 2. cbn [Z.eqb Pos.eqb].
  rewrite exec_sequence, fold_one, exec_case. cbn [eval_expr].
  rewrite (preserves_inputs 510 (SAssign false (EConst 4 0) (LVar 4 1352%nat))
    _ 1307%nat eq_refl). cbn [blocking_state]. rewrite HV.
  cbn [select_case_stmt eval_expr]. change (norm 2 3) with 3.
  change (norm 2 2) with 2. cbn [Z.eqb].
  cbv beta iota zeta delta [exec_stmt blocking_state apply_update resolve_update
    resolve_lvalue update_signal update_offset update_width update_value eval_expr].
  rewrite read_signal_write_same, norm_write_low. reflexivity.
Qed.

Lemma actual_unsigned_compare_mode s :
  norm 7 (read_signal s 1303%nat) = 3 ->
  norm 4 (read_signal (run_process cv32e40p_program s process_586) 1352%nat) = 0.
Proof.
  intros HO. rewrite blocking_run_process by reflexivity.
  change (statement_fuel cv32e40p_program) with 512%nat.
  cbn [process_586 process_body].
  rewrite exec_sequence, fold_one, exec_sequence, fold_two, exec_case.
  cbn [eval_expr].
  rewrite (preserves_inputs 510 (SAssign false (EConst 4 0) (LVar 4 1352%nat))
    _ 1303%nat eq_refl). cbn [blocking_state]. rewrite HO.
  cbn [select_case_stmt eval_expr].
  change (norm 7 8) with 8. change (norm 7 10) with 10.
  change (norm 7 0) with 0. change (norm 7 4) with 4.
  change (norm 7 2) with 2. change (norm 7 6) with 6.
  change (norm 7 16) with 16. change (norm 7 18) with 18.
  change (norm 7 20) with 20. change (norm 7 22) with 22.
  change (norm 7 23) with 23. cbn [Z.eqb Pos.eqb].
  cbv beta iota zeta delta [exec_stmt blocking_state apply_update resolve_update
    resolve_lvalue update_signal update_offset update_width update_value eval_expr].
  rewrite read_signal_write_same, norm_write_low. reflexivity.
Qed.

Lemma actual_less_than_select s op :
  op = 2 \/ op = 3 -> norm 7 (read_signal s 1303%nat) = op ->
  norm 4 (read_signal (run_process cv32e40p_program s process_592) 1358%nat) =
    norm 4 (Z.lnot (Z.lor (norm 4 (read_signal s 1351%nat))
                         (norm 4 (read_signal s 1350%nat)))).
Proof.
  intros HC HO. rewrite blocking_run_process by reflexivity.
  change (statement_fuel cv32e40p_program) with 512%nat.
  cbn [process_592 process_body].
  rewrite exec_sequence, fold_one, exec_sequence, fold_two, exec_case.
  cbn [eval_expr].
  rewrite (preserves_inputs 510 (SAssign false (EVar 4 1350%nat) (LVar 4 1358%nat))
    _ 1303%nat eq_refl). cbn [blocking_state]. rewrite HO.
  destruct HC as [->| ->]; cbn [select_case_stmt eval_expr];
    change (norm 7 12) with 12; change (norm 7 13) with 13;
    change (norm 7 8) with 8; change (norm 7 9) with 9;
    change (norm 7 10) with 10; change (norm 7 11) with 11;
    change (norm 7 0) with 0; change (norm 7 2) with 2;
    try (change (norm 7 1) with 1; change (norm 7 3) with 3);
    cbn [Z.eqb Pos.eqb];
    cbv beta iota zeta delta [exec_stmt blocking_state apply_update resolve_update
      resolve_lvalue update_signal update_offset update_width update_value eval_expr];
    rewrite read_signal_write_same, norm_write_low, !norm_twice;
    repeat rewrite read_signal_write_other by discriminate;
    apply norm_not_idempotent.
Qed.

Lemma actual_compare_bit s :
  norm 1 (read_signal (run_process cv32e40p_program s process_593) 1315%nat) =
    read_slice (read_signal s 1358%nat) 3 1.
Proof.
  rewrite (assign_value s process_593 1 1315%nat
    (ESel 1 (EVar 4 1358%nat) (EConst 2 3)) eq_refl).
  cbn [eval_expr]. change (norm 2 3) with 3.
  rewrite norm_twice.
  change (read_slice (norm 4 (read_signal s 1358%nat)) 3 1 =
    read_slice (read_signal s 1358%nat) 3 1).
  apply slice_norm; lia.
Qed.
Print Assumptions actual_signed_compare_mode.
Print Assumptions actual_unsigned_compare_mode.
Print Assumptions actual_less_than_select.
Print Assumptions actual_compare_bit.
End CV32E40PCompareControlCone.
