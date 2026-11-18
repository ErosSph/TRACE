(** Fetch FIFO occupancy safety over the actual FullCore scheduler. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice
  Lang.ExtendedSVCombCut Ex.Generated.CV32E40PExtendedAST
  Ex.External.CV32E40PFetchFIFOCount Ex.External.CV32E40PAddiAdderInputs
  Ex.External.CV32E40PAddiForwardControl Ex.External.CV32E40PAddiDecoder
  Ex.External.CV32E40PAddiOperandCone Ex.External.CV32E40PAddiDecoderPhase
  Ex.External.CV32E40PAddiIDEXAccept Ex.External.CV32E40PAddiOperands
  Ex.External.CV32E40PAddiReachability Ex.External.CV32E40PReq39Trace
  Ex.External.CV32E40PReq38Phase Ex.External.CV32E40PReq38Clock.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVProcessSlice ExtendedSVCombCut
  CV32E40PExtendedAST CV32E40PFetchFIFOCount CV32E40PAddiAdderInputs
  CV32E40PAddiForwardControl CV32E40PAddiDecoder
  CV32E40PAddiOperandCone CV32E40PAddiDecoderPhase CV32E40PAddiIDEXAccept
  CV32E40PAddiOperands CV32E40PAddiReachability CV32E40PReq39Trace CV32E40PReq38Phase CV32E40PReq38Clock.
Local Open Scope Z_scope.
Module CV32E40PFetchFIFOInvariant.
  Definition CountBound s := 0 <= norm 2 (read_signal s 479%nat) <= 2.
  Lemma count_comb_unwritten : comb_root_unwrittenb cv32e40p_program 479%nat = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma count_writer : filter (writes_rootb 479%nat) (processes cv32e40p_program) = [process_19].
  Proof. vm_compute. reflexivity. Qed.
  Lemma actual_full_flag s :
    norm 1 (read_signal (run_process cv32e40p_program s process_158) 465%nat) =
      if norm 2 (read_signal s 479%nat) =? 2 then 1 else 0.
  Proof.
    rewrite (assign_value s process_158 1 465%nat (rhs process_158) eq_refl).
    unfold rhs. cbn [process_158 process_body eval_expr]. change (norm 2 2) with 2.
    rewrite Z.eqb_sym. destruct (norm 2 (read_signal s 479%nat) =? 2); reflexivity.
  Qed.
  Lemma actual_empty_flag s :
    norm 1 (read_signal (run_process cv32e40p_program s process_159) 466%nat) =
      if norm 2 (read_signal s 479%nat) =? 0 then 1 else 0.
  Proof.
    rewrite (assign_value s process_159 1 466%nat (rhs process_159) eq_refl).
    unfold rhs. cbn [process_159 process_body eval_expr]. change (norm 2 0) with 0.
    rewrite Z.eqb_sym. destruct (norm 2 (read_signal s 479%nat) =? 0); reflexivity.
  Qed.
  #[local] Opaque before_process comb_round run_process.
  Lemma actual_count_inputs s : CountBound s -> CountInputs (cut 1570 s).
  Proof.
    intros H. unfold CountInputs, cut.
    rewrite (before_process_keeps_root cv32e40p_program 1570 s 479%nat ltac:(vm_compute; reflexivity)).
    split; [exact H|]. split.
    - rewrite <- (cut_final_root cv32e40p_program 1570 s 465%nat ltac:(vm_compute; reflexivity)).
      rewrite (comb_cut_root cv32e40p_program 158 process_158 s 465%nat eq_refl eq_refl ltac:(vm_compute; reflexivity)), actual_full_flag.
      rewrite before_process_keeps_root by (vm_compute; reflexivity). reflexivity.
    - rewrite <- (cut_final_root cv32e40p_program 1570 s 466%nat ltac:(vm_compute; reflexivity)).
      rewrite (comb_cut_root cv32e40p_program 159 process_159 s 466%nat eq_refl eq_refl ltac:(vm_compute; reflexivity)), actual_empty_flag.
      rewrite before_process_keeps_root by (vm_compute; reflexivity). reflexivity.
  Qed.
  Lemma round_next_count_bound s : CountBound s ->
    0 <= norm 2 (read_signal (round s) 478%nat) <= 2.
  Proof.
    intros H. unfold round.
    rewrite (comb_cut_root cv32e40p_program 1570 process_1570 s 478%nat eq_refl eq_refl ltac:(vm_compute; reflexivity)).
    apply actual_count_bounded. apply actual_count_inputs. exact H.
  Qed.
  Lemma actual_sequential_count_bounded s old :
    0 <= norm 2 old <= 2 -> 0 <= norm 2 (read_signal s 478%nat) <= 2 ->
    0 <= norm 2 (apply_updates_root_value 479%nat old
      (process_updates cv32e40p_program s process_19)) <= 2.
  Proof.
    intros Hold Hnext.
    unfold process_updates. change (statement_fuel cv32e40p_program) with 512%nat.
    cbn [process_19 process_body].
    rewrite exec_sequence, fold_one, exec_sequence, fold_one, exec_if.
    cbn [blocking_state eval_expr].
    destruct (bit_cases (read_signal s 461%nat)) as [Hr|Hr];
      rewrite Hr; cbn [Z.eqb].
    2: rewrite exec_sequence, fold_one, exec_case;
      cbn [blocking_state eval_expr select_case_stmt];
      destruct (bit_cases (read_signal s 462%nat)) as [Hf|Hf];
      destruct (bit_cases (read_signal s 463%nat)) as [Hk|Hk];
      rewrite Hf, ?Hk; change (norm 1 1) with 1; cbn [Z.eqb Pos.eqb].
    all:
      cbv beta iota zeta delta [process_19 process_body exec_stmt fold_left blocking_state pending_nba
        emitted_updates select_case_stmt eval_expr resolve_update resolve_lvalue
        update_signal update_offset update_width update_value apply_updates_root_value apply_update_root_value];
      change (norm 2 0) with 0;
      cbn [Z.eqb app];
      repeat rewrite norm_write_low;
      repeat rewrite norm_twice;
      try exact Hnext; try (change (0 <= 0 <= 2); lia).
    all: destruct (0 <? norm 2 (read_signal s 479%nat));
      change (norm 2 1) with 1; change (norm 2 0) with 0;
      change (norm 1 1) with 1; change (norm 1 0) with 0;
      cbn [Z.eqb Pos.eqb Nat.eqb boolz];
      change (norm 1 1) with 1; change (norm 1 0) with 0;
      cbn [Z.eqb Pos.eqb];
      rewrite norm_write_low, ?norm_twice; try exact Hnext;
      vm_compute; intuition discriminate.
  Qed.
  #[local] Opaque PhaseSemantics phase_driven_state.
  Theorem phase_preserves_count ev pre : changed_signal ev <> 479%nat ->
    CountBound pre -> CountBound (PhaseSemantics cv32e40p_program ev pre).
  Proof.
    intros He Hpre.
    assert (Hnext : 0 <= norm 2 (read_signal (phase_driven_state cv32e40p_program ev pre) 478%nat) <= 2).
    { rewrite phase_driven_last_round. apply round_next_count_bound.
      unfold CountBound. rewrite comb_iter_preserves_unwritten_root by exact count_comb_unwritten.
      rewrite read_signal_write_other by exact He. exact Hpre. }
    unfold CountBound. rewrite phase_root_projection by assumption || exact count_comb_unwritten.
    unfold phase_update_chain, selected_on_transition.
    rewrite process_slice_sound, filter_swap, count_writer.
    cbn [filter]. destruct (process_matches_states pre (phase_driven_state cv32e40p_program ev pre) process_19).
    - cbn [flat_map]. rewrite app_nil_r. apply actual_sequential_count_bounded; assumption.
    - exact Hpre.
  Qed.
  Lemma initial_count_bound : CountBound initialized_zero.
  Proof.
    unfold CountBound, initialized_zero, initialize.
    rewrite fold_run_process_preserves_root.
    - vm_compute. intuition discriminate.
    - apply avoids_root_sound. vm_compute. reflexivity.
  Qed.
  Lemma reset_count_bound : CountBound released.
  Proof.
    unfold released. apply phase_preserves_count; [discriminate|].
    unfold post_reset. apply phase_preserves_count; [discriminate|].
    unfold pre_reset, CountBound. rewrite lfp_candidate_preserves_unwritten_root by exact count_comb_unwritten.
    rewrite read_signal_write_other by discriminate. exact initial_count_bound.
  Qed.
  Lemma environment_keeps_count image s :
    read_signal (environment_state_image image s) 479%nat = read_signal (trace_rtl s) 479%nat.
  Proof.
    unfold environment_state_image, obi_ports_image.
    rewrite lfp_candidate_preserves_unwritten_root by exact count_comb_unwritten.
    unfold drive. cbn [fold_left fst snd].
    repeat rewrite read_signal_write_other by discriminate. reflexivity.
  Qed.
  Theorem full_cycle_preserves_count image s : CountBound (trace_rtl s) ->
    CountBound (trace_rtl (full_cycle_image image s)).
  Proof.
    intros H. change (CountBound (settled_state_image image s)).
    unfold settled_state_image, CountBound.
    rewrite lfp_candidate_preserves_unwritten_root by exact count_comb_unwritten.
    change (CountBound (falling_state_image image s)).
    unfold falling_state_image. apply phase_preserves_count; [discriminate|].
    unfold rising_state_image. apply phase_preserves_count; [discriminate|].
    unfold CountBound. rewrite environment_keeps_count. exact H.
  Qed.
  Theorem every_reachable_fetch_fifo_count_bounded image s : ResetReachable image s ->
    CountBound (trace_rtl (physical_state s)).
  Proof.
    intros H. induction H.
    - exact reset_count_bound.
    - rewrite advance_physical. apply full_cycle_preserves_count. exact IHResetReachable.
  Qed.
  Print Assumptions every_reachable_fetch_fifo_count_bounded.
End CV32E40PFetchFIFOInvariant.
