(** Scalar ADD normalization, shifter and final result selection in the actual AST. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVBlocking
  Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiAdderInputs
  Ex.External.CV32E40PAddiAdderResult Ex.External.CV32E40PAddiAdderBits
  Ex.External.CV32E40PAddiAdder Ex.External.CV32E40PAddiOperands
  Ex.External.CV32E40PAddiWritebackMux.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVBlocking
  CV32E40PExtendedAST CV32E40PAddiAdderInputs CV32E40PAddiAdderResult
  CV32E40PAddiAdderBits CV32E40PAddiAdder CV32E40PAddiOperands
  CV32E40PAddiWritebackMux CV32E40PAddiIDEXAccept.CV32E40PAddiIDEXAccept
  CV32E40PAddiDecoder.CV32E40PAddiDecoder.
Local Open Scope Z_scope.
Module CV32E40PAddiALUOutput.
  Lemma left_disabled s : norm 7 (read_signal s 1303%nat) = 24 ->
    norm 1 (read_signal (run_process cv32e40p_program s process_411) 1336%nat) = 0.
  Proof.
    intros H. rewrite (assign_value s process_411 1 1336%nat (rhs process_411) eq_refl).
    unfold rhs. cbn [process_411 process_body eval_expr]. rewrite H. reflexivity.
  Qed.
  Lemma round_selected s : norm 7 (read_signal s 1303%nat) = 24 ->
    norm 1 (read_signal (run_process cv32e40p_program s process_412) 1337%nat) = 1.
  Proof.
    intros H. rewrite (assign_value s process_412 1 1337%nat (rhs process_412) eq_refl).
    unfold rhs. cbn [process_412 process_body eval_expr]. rewrite H. reflexivity.
  Qed.
  Lemma rounding_zero s : norm 7 (read_signal s 1303%nat) = 24 ->
    norm 32 (read_signal (run_process cv32e40p_program s process_578) 1334%nat) = 0.
  Proof.
    intros H. rewrite (assign_value s process_578 32 1334%nat (rhs process_578) eq_refl).
    unfold rhs. cbn [process_578 process_body eval_expr]. rewrite H. reflexivity.
  Qed.
  Lemma round_add_identity s : norm 32 (read_signal s 1334%nat) = 0 ->
    norm 32 (read_signal (run_process cv32e40p_program s process_627) 1335%nat) = norm 32 (read_signal s 1332%nat).
  Proof.
    intros H. rewrite (assign_value s process_627 32 1335%nat (rhs process_627) eq_refl).
    unfold rhs. cbn [process_627 process_body eval_expr]. rewrite H, Z.add_0_r. now rewrite !norm_twice.
  Qed.
  Lemma shift_operand s : norm 1 (read_signal s 1336%nat) = 0 -> norm 1 (read_signal s 1337%nat) = 1 ->
    norm 32 (read_signal (run_process cv32e40p_program s process_628) 1343%nat) = norm 32 (read_signal s 1335%nat).
  Proof.
    intros H0 H1. rewrite (assign_value s process_628 32 1343%nat (rhs process_628) eq_refl).
    unfold rhs. cbn [process_628 process_body eval_expr]. rewrite H0, H1. cbn [Z.eqb]. now rewrite !norm_twice.
  Qed.
  Lemma concat_low hi lo : norm 32 (norm 64 (Z.lor (Z.shiftl hi 32) (norm 32 lo))) = norm 32 lo.
  Proof.
    rewrite norm_down by lia. rewrite concat_arith by (try lia; apply norm_range).
    rewrite norm_mod. change (2^Z.of_nat 32) with (2^32).
    rewrite Z.add_comm, Z.mul_comm, Z.mod_add by (apply Z.pow_nonzero; lia).
    apply Z.mod_small. apply norm_range.
  Qed.
  Lemma extended_low s : norm 7 (read_signal s 1303%nat) = 24 ->
    norm 32 (read_signal (run_process cv32e40p_program s process_629) 1348%nat) = norm 32 (read_signal s 1343%nat).
  Proof.
    intros H. rewrite <- (norm_down 32 64 (read_signal (run_process cv32e40p_program s process_629) 1348%nat) ltac:(lia)).
    rewrite (assign_value s process_629 64 1348%nat (rhs process_629) eq_refl).
    unfold rhs. cbn [process_629 process_body eval_expr expr_width]. rewrite H.
    change (norm 7 38) with 38. cbn [Z.eqb boolz]. change (norm 1 0) with 0. cbn [Z.eqb].
    change (norm 1 (boolz (38 =? 24)%positive)) with 0.
    cbn [Z.eqb]. rewrite !norm_twice. apply concat_low.
  Qed.
  Lemma shift_amount_zero s : norm 1 (read_signal s 1311%nat) = 0 -> norm 5 (read_signal s 1309%nat) = 0 ->
    norm 32 (read_signal (run_process cv32e40p_program s process_639) 1342%nat) = 0.
  Proof.
    intros H0 H1. rewrite (assign_value s process_639 32 1342%nat (rhs process_639) eq_refl).
    unfold rhs. cbn [process_639 process_body eval_expr]. rewrite H0, H1. reflexivity.
  Qed.
  Lemma shift_amount_select s : norm 1 (read_signal s 1337%nat) = 1 ->
    norm 32 (read_signal (run_process cv32e40p_program s process_1794) 1341%nat) = norm 32 (read_signal s 1342%nat).
  Proof.
    intros H. rewrite (assign_value s process_1794 32 1341%nat (rhs process_1794) eq_refl).
    unfold rhs. cbn [process_1794 process_body eval_expr]. rewrite H. cbn [Z.eqb]. now rewrite !norm_twice.
  Qed.
  Lemma shift_identity s : norm 2 (read_signal s 1307%nat) = 0 -> norm 32 (read_signal s 1341%nat) = 0 ->
    norm 32 (read_signal (run_process cv32e40p_program s process_1795) 1345%nat) = norm 32 (read_signal s 1348%nat).
  Proof.
    intros Hv Ha. rewrite blocking_run_process by reflexivity.
    change (statement_fuel cv32e40p_program) with 512%nat.
    cbn [process_1795 process_body]. rewrite exec_sequence, fold_one, exec_sequence, fold_one, exec_case.
    cbn [eval_expr blocking_state]. rewrite Hv. change (norm 2 2) with 2. change (norm 2 3) with 3.
    cbn [select_case_stmt eval_expr Z.eqb Pos.eqb].
    change (norm 2 2) with 2. change (norm 2 3) with 3.
    cbn [Z.eqb]. rewrite exec_sequence, fold_one.
    cbv beta iota zeta delta [exec_stmt blocking_state apply_update resolve_update resolve_lvalue
      update_signal update_offset update_width update_value eval_expr].
    rewrite Ha. change (norm 5 (Z.shiftr 0 (norm 5 0))) with 0. change (norm 32 0) with 0.
    rewrite !Z.shiftr_0_r, read_signal_write_same, norm_write_low, !norm_twice.
    apply norm_down; lia.
  Qed.
  Lemma result_not_reversed s : norm 1 (read_signal s 1336%nat) = 0 ->
    norm 32 (read_signal (run_process cv32e40p_program s process_1828) 1344%nat) = norm 32 (read_signal s 1345%nat).
  Proof.
    intros H. rewrite (assign_value s process_1828 32 1344%nat (rhs process_1828) eq_refl).
    unfold rhs. cbn [process_1828 process_body eval_expr]. rewrite H. cbn [Z.eqb]. now rewrite !norm_twice.
  Qed.
  Lemma actual_alu_add_output s : norm 7 (read_signal s 1303%nat) = 24 ->
    norm 32 (read_signal (run_process cv32e40p_program s process_1896) 1314%nat) = norm 32 (read_signal s 1344%nat).
  Proof.
    intros H. rewrite blocking_run_process by reflexivity.
    change (statement_fuel cv32e40p_program) with 512%nat.
    cbn [process_1896 process_body]. rewrite exec_sequence, fold_one, exec_sequence, fold_two, exec_case.
    cbn [eval_expr].
    rewrite (preserves_inputs 510 (SAssign false (EConst 32 0) (LVar 32 1314%nat)) _ 1303%nat eq_refl).
    cbn [blocking_state]. rewrite H.
    cbn [select_case_stmt eval_expr]. change (norm 7 21) with 21. change (norm 7 46) with 46.
    change (norm 7 47) with 47. change (norm 7 24) with 24. cbn [Z.eqb Pos.eqb].
    cbv beta iota zeta delta [exec_stmt blocking_state apply_update resolve_update resolve_lvalue
      update_signal update_offset update_width update_value eval_expr].
    rewrite read_signal_write_same, norm_write_low, !norm_twice.
    rewrite read_signal_write_other by discriminate. reflexivity.
  Qed.
End CV32E40PAddiALUOutput.
