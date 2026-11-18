(** Branch ALU control certificates for the original generated processes.
    This is a local wiring result, not a branch retirement/refinement theorem.
    op0/10 are signed; op1/11/12/13 are unsigned; vector mode must be scalar. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Ex.External.CV32E40PCompareControlCone.
Require Import Lang.ExtendedSV Lang.ExtendedSVBlocking Lang.ExtendedSVRootProjection
  Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiDecoder
  Ex.External.CV32E40PAddiWritebackMux Ex.External.CV32E40PAddiIDEXAccept
  Ex.External.CV32E40PAddiForwardControl Ex.External.CV32E40PAddiOperands
  Ex.External.CV32E40PAddiAdderInputs Ex.External.CV32E40PAddiAdderBits.
Import ListNotations ExtendedSV ExtendedSVBlocking ExtendedSVRootProjection
  CV32E40PExtendedAST CV32E40PAddiDecoder CV32E40PAddiWritebackMux
  CV32E40PAddiIDEXAccept CV32E40PAddiForwardControl CV32E40PAddiOperands
  CV32E40PAddiAdderInputs CV32E40PAddiAdderBits CV32E40PCompareControlCone.
Local Open Scope Z_scope.
Module CV32E40PBranchCompareControl.

Definition BranchALU (op : Z) : Prop :=
  op = 12 \/ op = 13 \/ op = 0 \/ op = 10 \/ op = 1 \/ op = 11.

Definition branch_compare_vector (op equal greater : Z) : Z :=
  if op =? 12 then norm 4 equal else
  if op =? 13 then norm 4 (Z.lnot equal) else
  if (op =? 10) || (op =? 11) then norm 4 (Z.lor greater equal)
  else norm 4 (Z.lnot (Z.lor greater equal)).

Ltac normalize_case_constants :=
  change (norm 7 8) with 8; change (norm 7 10) with 10;
  change (norm 7 0) with 0; change (norm 7 4) with 4;
  change (norm 7 2) with 2; change (norm 7 6) with 6;
  change (norm 7 16) with 16; change (norm 7 18) with 18;
  change (norm 7 20) with 20; change (norm 7 22) with 22;
  change (norm 7 23) with 23.

Lemma branch_signed_mode s op :
  op = 0 \/ op = 10 -> norm 7 (read_signal s 1303%nat) = op ->
  norm 2 (read_signal s 1307%nat) = 0 ->
  norm 4 (read_signal (run_process cv32e40p_program s process_586) 1352%nat) = 8.
Proof.
  intros HC HO HV. rewrite blocking_run_process by reflexivity.
  change (statement_fuel cv32e40p_program) with 512%nat.
  cbn [process_586 process_body].
  rewrite exec_sequence, fold_one, exec_sequence, fold_two, exec_case.
  cbn [eval_expr].
  rewrite (preserves_inputs 510 (SAssign false (EConst 4 0) (LVar 4 1352%nat))
    _ 1303%nat eq_refl). cbn [blocking_state]. rewrite HO.
  destruct HC as [->| ->]; cbn [select_case_stmt eval_expr];
    normalize_case_constants; cbn [Z.eqb Pos.eqb];
    rewrite exec_sequence, fold_one, exec_case; cbn [eval_expr];
    rewrite (preserves_inputs 510 (SAssign false (EConst 4 0) (LVar 4 1352%nat))
      _ 1307%nat eq_refl); cbn [blocking_state]; rewrite HV;
    cbn [select_case_stmt eval_expr];
    change (norm 2 3) with 3; change (norm 2 2) with 2; cbn [Z.eqb];
    cbv beta iota zeta delta [exec_stmt blocking_state apply_update resolve_update
      resolve_lvalue update_signal update_offset update_width update_value eval_expr];
    rewrite read_signal_write_same, norm_write_low; reflexivity.
Qed.

Lemma branch_unsigned_mode s op :
  op = 1 \/ op = 11 \/ op = 12 \/ op = 13 ->
  norm 7 (read_signal s 1303%nat) = op ->
  norm 4 (read_signal (run_process cv32e40p_program s process_586) 1352%nat) = 0.
Proof.
  intros HC HO. rewrite blocking_run_process by reflexivity.
  change (statement_fuel cv32e40p_program) with 512%nat.
  cbn [process_586 process_body].
  rewrite exec_sequence, fold_one, exec_sequence, fold_two, exec_case.
  cbn [eval_expr].
  rewrite (preserves_inputs 510 (SAssign false (EConst 4 0) (LVar 4 1352%nat))
    _ 1303%nat eq_refl). cbn [blocking_state]. rewrite HO.
  destruct HC as [->| [->| [->| ->]]]; cbn [select_case_stmt eval_expr];
    normalize_case_constants; cbn [Z.eqb Pos.eqb];
    cbv beta iota zeta delta [exec_stmt blocking_state apply_update resolve_update
      resolve_lvalue update_signal update_offset update_width update_value eval_expr];
    rewrite read_signal_write_same, norm_write_low; reflexivity.
Qed.

Lemma branch_result_select s op : BranchALU op ->
  norm 7 (read_signal s 1303%nat) = op ->
  norm 4 (read_signal (run_process cv32e40p_program s process_592) 1358%nat) =
    branch_compare_vector op (norm 4 (read_signal s 1350%nat))
      (norm 4 (read_signal s 1351%nat)).
Proof.
  intros HC HO. rewrite blocking_run_process by reflexivity.
  change (statement_fuel cv32e40p_program) with 512%nat.
  cbn [process_592 process_body].
  rewrite exec_sequence, fold_one, exec_sequence, fold_two, exec_case.
  cbn [eval_expr].
  rewrite (preserves_inputs 510 (SAssign false (EVar 4 1350%nat) (LVar 4 1358%nat))
    _ 1303%nat eq_refl). cbn [blocking_state]. rewrite HO.
  destruct HC as [->| [->| [->| [->| [->| ->]]]]];
    cbn [select_case_stmt eval_expr];
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
    cbn [branch_compare_vector Z.eqb Pos.eqb]; repeat rewrite norm_twice;
    try reflexivity; apply norm_not_idempotent.
Qed.

Print Assumptions branch_signed_mode.
Print Assumptions branch_unsigned_mode.
Print Assumptions branch_result_select.
End CV32E40PBranchCompareControl.
