(** Outstanding transaction counter, derived from the original process AST. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVBlocking Lang.ExtendedSVRootProjection
  Lang.ExtendedSVProcessSlice Lang.ExtendedSVCombCut Lang.ExtendedSVNBAProjection Ex.Generated.CV32E40PExtendedAST
  Ex.External.CV32E40PFetchFIFOCount Ex.External.CV32E40PAddiDecoder
  Ex.External.CV32E40PAddiForwardControl Ex.External.CV32E40PAddiOperands
  Ex.External.CV32E40PAddiIDEXAccept Ex.External.CV32E40PAddiOperandCone
  Ex.External.CV32E40PAddiDecoderPhase.
Import ListNotations ExtendedSV ExtendedSVBlocking ExtendedSVRootProjection
  ExtendedSVProcessSlice ExtendedSVCombCut ExtendedSVNBAProjection CV32E40PExtendedAST
  CV32E40PAddiDecoder CV32E40PAddiForwardControl CV32E40PAddiOperands
  CV32E40PAddiIDEXAccept CV32E40PAddiOperandCone CV32E40PAddiDecoderPhase CV32E40PFetchFIFOCount.
Local Open Scope Z_scope.
Module CV32E40PRequestCount.
  Definition counter_next c up down :=
    if up =? 0 then if down =? 0 then c else norm 2 (c - 1)
    else if down =? 0 then norm 2 (1 + c) else c.
  #[local] Opaque norm read_signal write_signal write_slice.
  Lemma actual_counter s : norm 2 (read_signal (run_process cv32e40p_program s process_1555) 441%nat) =
    counter_next (norm 2 (read_signal s 440%nat)) (norm 1 (read_signal s 442%nat))
      (norm 1 (read_signal s 443%nat)).
  Proof.
    rewrite blocking_run_process by reflexivity. change (statement_fuel cv32e40p_program) with 512%nat.
    cbn [process_1555 process_body]. rewrite exec_sequence, fold_one, exec_sequence, fold_one, exec_case.
    cbn [blocking_state eval_expr expr_width Z.of_nat Pos.of_succ_nat].
    destruct (bit_cases (read_signal s 442%nat)) as [Hu|Hu];
      destruct (bit_cases (read_signal s 443%nat)) as [Hd|Hd]; rewrite Hu, Hd;
      change (norm 2 (Z.lor (Z.shiftl 0 1) 0)) with 0;
      change (norm 2 (Z.lor (Z.shiftl 0 1) 1)) with 1;
      change (norm 2 (Z.lor (Z.shiftl 1 1) 0)) with 2;
      change (norm 2 (Z.lor (Z.shiftl 1 1) 1)) with 3;
      change (norm 2 0) with 0; change (norm 2 1) with 1;
      change (norm 2 2) with 2; change (norm 2 3) with 3;
      cbn [select_case_stmt eval_expr Z.eqb Pos.eqb]; change (norm 2 0) with 0; change (norm 2 1) with 1;
      change (norm 2 2) with 2; change (norm 2 3) with 3;
      cbn [select_case_stmt Z.eqb Pos.eqb]; unfold counter_next; cbn [Z.eqb].
    all: straight; change (norm 2 1) with 1; reflexivity.
  Qed.
  Lemma counter_next_arithmetic c up down :
    counter_next (norm 2 c) (norm 1 up) (norm 1 down) =
      norm 2 (norm 2 c + norm 1 up - norm 1 down).
  Proof.
    destruct (bit_cases up) as [Hu|Hu]; destruct (bit_cases down) as [Hd|Hd];
      rewrite Hu, Hd; unfold counter_next; cbn [Z.eqb];
      rewrite ?Z.add_0_r, ?Z.sub_0_r, ?norm_twice; try reflexivity.
    - f_equal. lia.
    - replace (norm 2 c + 1 - 1) with (norm 2 c) by lia. symmetry. apply norm_twice.
  Qed.
  #[local] Opaque before_process comb_round run_process.
  Lemma count_unwritten : comb_root_unwrittenb cv32e40p_program 440%nat = true.
  Proof. vm_compute; reflexivity. Qed.
  Theorem round_counter s : norm 2 (read_signal (round s) 441%nat) =
    norm 2 (norm 2 (read_signal s 440%nat) + norm 1 (read_signal (cut 1555 s) 442%nat)
      - norm 1 (read_signal (cut 1555 s) 443%nat)).
  Proof.
    unfold round, cut. rewrite (comb_cut_root cv32e40p_program 1555 process_1555 s 441%nat
      eq_refl eq_refl ltac:(vm_compute; reflexivity)), actual_counter, counter_next_arithmetic.
    rewrite before_process_keeps_root by (vm_compute; reflexivity). reflexivity.
  Qed.
  Lemma sequential_counter s old :
    norm 2 (apply_updates_root_value 440%nat old (process_updates cv32e40p_program s process_12)) =
    if norm 1 (read_signal s 419%nat) =? 0 then 0 else norm 2 (read_signal s 441%nat).
  Proof.
    rewrite process_nba_pruned_projection by reflexivity.
    change (statement_fuel cv32e40p_program) with 512%nat.
    cbn [nba_root_pruned process_12 process_body stmt_writers lvalue_root flat_map fold_left existsb Nat.eqb app orb eval_expr].
    change (norm 2 (if norm 1 (read_signal s 419%nat) =? 0
      then write_slice old 0 2 (norm 2 (norm 2 0))
      else write_slice old 0 2 (norm 2 (norm 2 (read_signal s 441%nat)))) =
      if norm 1 (read_signal s 419%nat) =? 0 then 0 else norm 2 (read_signal s 441%nat)).
    destruct (norm 1 (read_signal s 419%nat) =? 0);
      rewrite norm_write_low, !norm_twice; reflexivity.
  Qed.
  Lemma count_writers : filter (writes_rootb 440%nat) (processes cv32e40p_program) = [process_12].
  Proof. vm_compute; reflexivity. Qed.
  #[local] Opaque PhaseSemantics phase_driven_state process_updates apply_updates_root_value.
  Theorem phase_counter ev pre : changed_signal ev <> 440%nat ->
    norm 2 (read_signal (PhaseSemantics cv32e40p_program ev pre) 440%nat) =
    if process_matches_states pre (phase_driven_state cv32e40p_program ev pre) process_12 then
      if norm 1 (read_signal (phase_driven_state cv32e40p_program ev pre) 419%nat) =? 0 then 0
      else norm 2 (read_signal (phase_driven_state cv32e40p_program ev pre) 441%nat)
    else norm 2 (read_signal pre 440%nat).
  Proof.
    intros He. rewrite phase_root_projection by auto using count_unwritten.
    unfold phase_update_chain, selected_on_transition.
    rewrite process_slice_sound, filter_swap, count_writers. cbn [filter].
    destruct (process_matches_states pre (phase_driven_state cv32e40p_program ev pre) process_12);
      cbn [flat_map]; rewrite ?app_nil_r; [apply sequential_counter|reflexivity].
  Qed.
  Definition counter_sample ev pre := cut 1555
    (comb_iter cv32e40p_program 7 (write_signal pre (changed_signal ev) (new_value ev))).
  Theorem phase_transaction_balance ev pre : changed_signal ev <> 440%nat ->
    norm 2 (read_signal (PhaseSemantics cv32e40p_program ev pre) 440%nat) =
    if process_matches_states pre (phase_driven_state cv32e40p_program ev pre) process_12 then
      if norm 1 (read_signal (phase_driven_state cv32e40p_program ev pre) 419%nat) =? 0 then 0
      else norm 2 (norm 2 (read_signal pre 440%nat) +
        norm 1 (read_signal (counter_sample ev pre) 442%nat) -
        norm 1 (read_signal (counter_sample ev pre) 443%nat))
    else norm 2 (read_signal pre 440%nat).
  Proof.
    intros He. rewrite phase_counter by exact He.
    pose proof (round_counter (comb_iter cv32e40p_program 7
      (write_signal pre (changed_signal ev) (new_value ev)))) as H.
    unfold round in H. rewrite <- phase_driven_last_round in H.
    rewrite comb_iter_preserves_unwritten_root in H by exact count_unwritten.
    rewrite read_signal_write_other in H by exact He.
    rewrite H. reflexivity.
  Qed.
  Print Assumptions phase_transaction_balance.
End CV32E40PRequestCount.
