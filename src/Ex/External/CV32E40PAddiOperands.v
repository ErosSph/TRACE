(** Exact forwarding/operand cones in the generated FullCore, with the original
    process order.  In particular the A mux precedes the forwarding mux: its
    input is from the preceding combinational round, not a reordered circuit. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection
  Lang.ExtendedSVBitSlice Lang.ExtendedSVCombCut Lang.ExtendedSVBlocking.
Require Import Ex.Generated.CV32E40PExtendedAST
  Ex.External.CV32E40PAddiIDEXAccept Ex.External.CV32E40PAddiDecoderPhase.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVBitSlice
  ExtendedSVCombCut ExtendedSVBlocking CV32E40PExtendedAST CV32E40PAddiIDEXAccept
  CV32E40PAddiDecoderPhase CV32E40PAddiDecoder.CV32E40PAddiDecoder.
Local Open Scope Z_scope.
Module CV32E40PAddiOperands.
  Definition forward_value s :=
    if norm 2 (read_signal s 834%nat) =? 1 then norm 32 (read_signal s 695%nat)
    else if norm 2 (read_signal s 834%nat) =? 2 then norm 32 (read_signal s 691%nat)
    else norm 32 (read_signal s 776%nat).

  Lemma norm_write_low w old value :
    norm w (write_slice old 0 (Z.of_nat w) value) = norm w value.
  Proof.
    pose proof (read_slice_write_same old 0 (Z.of_nat w) value ltac:(lia) ltac:(lia)) as H.
    unfold read_slice in H. rewrite !Z.shiftr_0_r in H. exact H.
  Qed.
  Lemma forward_normalized s : norm 32 (forward_value s) = forward_value s.
  Proof.
    unfold forward_value. destruct (norm 2 (read_signal s 834%nat) =? 1);
      [|destruct (norm 2 (read_signal s 834%nat) =? 2)]; apply norm_twice.
  Qed.
  Lemma actual_forward_mux s :
    norm 32 (read_signal (run_process cv32e40p_program s process_1629) 837%nat) =
    forward_value s.
  Proof.
    unfold forward_value.
    rewrite blocking_run_process by reflexivity.
    change (statement_fuel cv32e40p_program) with 512%nat.
    cbn [process_1629 process_body].
    rewrite exec_sequence, fold_one, exec_sequence, fold_one, exec_case.
    cbn [eval_expr blocking_state].
    destruct (norm 2 (read_signal s 834%nat) =? 1) eqn:H1;
      [|destruct (norm 2 (read_signal s 834%nat) =? 2) eqn:H2];
      try destruct (norm 2 (read_signal s 834%nat) =? 0) eqn:H0;
      cbn [select_case_stmt eval_expr blocking_state];
      change (norm 2 1) with 1; change (norm 2 2) with 2;
      change (norm 2 0) with 0.
    all: rewrite ?H1, ?H2, ?H0.
    all: cbv beta iota zeta delta [exec_stmt resolve_update resolve_lvalue apply_update update_signal
      update_offset update_width update_value eval_expr blocking_state];
      rewrite read_signal_write_same, norm_write_low, !norm_twice; reflexivity.
  Qed.
  Lemma actual_a_mux s : norm 3 (read_signal s 781%nat) = 0 ->
    norm 32 (read_signal (run_process cv32e40p_program s process_1628) 844%nat) =
    norm 32 (read_signal s 837%nat).
  Proof.
    intros H. rewrite blocking_run_process by reflexivity.
    change (statement_fuel cv32e40p_program) with 512%nat.
    cbn [process_1628 process_body].
    rewrite exec_sequence, fold_one, exec_sequence, fold_one, exec_case.
    cbn [eval_expr blocking_state]. rewrite H.
    cbn [select_case_stmt eval_expr]. change (norm 3 0) with 0. cbn [Z.eqb].
    cbv beta iota zeta delta [exec_stmt resolve_update resolve_lvalue apply_update update_signal
      update_offset update_width update_value eval_expr blocking_state].
    rewrite read_signal_write_same, norm_write_low, !norm_twice. reflexivity.
  Qed.
  Lemma actual_immediate_mux s : norm 4 (read_signal s 786%nat) = 0 ->
    norm 32 (read_signal (run_process cv32e40p_program s process_1630) 759%nat) =
    norm 32 (read_signal s 742%nat).
  Proof.
    intros H. rewrite blocking_run_process by reflexivity.
    change (statement_fuel cv32e40p_program) with 512%nat.
    cbn [process_1630 process_body].
    rewrite exec_sequence, fold_one, exec_sequence, fold_one, exec_case.
    cbn [eval_expr blocking_state]. rewrite H.
    cbn [select_case_stmt eval_expr]. change (norm 4 0) with 0. cbn [Z.eqb].
    cbv beta iota zeta delta [exec_stmt resolve_update resolve_lvalue apply_update update_signal
      update_offset update_width update_value eval_expr blocking_state].
    rewrite read_signal_write_same, norm_write_low, !norm_twice. reflexivity.
  Qed.
  Lemma actual_b_mux s : norm 3 (read_signal s 782%nat) = 2 ->
    norm 32 (read_signal (run_process cv32e40p_program s process_1631) 840%nat) =
    norm 32 (read_signal s 759%nat).
  Proof.
    intros H. rewrite blocking_run_process by reflexivity.
    change (statement_fuel cv32e40p_program) with 512%nat.
    cbn [process_1631 process_body].
    rewrite exec_sequence, fold_one, exec_sequence, fold_one, exec_case.
    cbn [eval_expr blocking_state]. rewrite H. cbn [select_case_stmt eval_expr].
    change (norm 3 3) with 3. change (norm 3 0) with 0.
    change (norm 3 1) with 1. change (norm 3 2) with 2. cbn [Z.eqb].
    change (norm 32 (read_signal (blocking_state
      (exec_stmt 509 (SAssign false (EVar 32 759%nat) (LVar 32 840%nat))
        {| blocking_state := s; pending_nba := []; emitted_updates := [] |})) 840%nat) =
      norm 32 (read_signal s 759%nat)).
    cbv beta iota zeta delta [exec_stmt resolve_update resolve_lvalue apply_update update_signal
      update_offset update_width update_value eval_expr blocking_state].
    rewrite read_signal_write_same, norm_write_low, !norm_twice. reflexivity.
  Qed.
  Lemma actual_scalar_mux s : norm 1 (read_signal s 860%nat) = 0 ->
    norm 32 (read_signal (run_process cv32e40p_program s process_1633) 845%nat) =
    norm 32 (read_signal s 840%nat).
  Proof.
    intros H. change (norm 32 (read_signal
      (write_signal s 845%nat (write_slice (read_signal s 845%nat) 0 32
        (norm 32 (norm 32 (if norm 1 (read_signal s 860%nat) =? 0
          then norm 32 (read_signal s 840%nat) else norm 32 (read_signal s 841%nat))))))
      845%nat) = norm 32 (read_signal s 840%nat)).
    rewrite H. cbn [Z.eqb]. rewrite read_signal_write_same, norm_write_low.
    now rewrite !norm_twice.
  Qed.
End CV32E40PAddiOperands.
