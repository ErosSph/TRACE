(** Actual ungated startup register, not an assumed clock-enable input. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVCombCut
 Lang.ExtendedSVProcessSlice Lang.ExtendedSVNBAProjection Lang.ExtendedSVBitInvariant
 Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiDecoder
 Ex.External.CV32E40PAddiOperands Ex.External.CV32E40PAddiForwardControl
 Ex.External.CV32E40PAddiDecoderPhase Ex.External.CV32E40PAddiOperandCone
 Ex.External.CV32E40PAddiIDEXAccept Ex.External.CV32E40PFetchFIFOCount
 Ex.External.CV32E40PRequestWiring Ex.External.CV32E40PReq39Trace
 Ex.External.CV32E40PAddiReachability Ex.External.CV32E40PAddiResetReleaseInvariant
 Ex.External.CV32E40PInternalBits Ex.External.CV32E40PClockBoundary.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVCombCut
 ExtendedSVProcessSlice ExtendedSVNBAProjection ExtendedSVBitInvariant
 CV32E40PExtendedAST CV32E40PAddiDecoder CV32E40PAddiOperands CV32E40PAddiForwardControl
 CV32E40PAddiDecoderPhase CV32E40PAddiOperandCone CV32E40PAddiIDEXAccept
 CV32E40PFetchFIFOCount CV32E40PRequestWiring CV32E40PReq39Trace CV32E40PAddiReachability
 CV32E40PAddiResetReleaseInvariant CV32E40PInternalBits CV32E40PClockBoundary.
Local Open Scope Z_scope.
Import CV32E40PAddiAdderInputs.CV32E40PAddiAdderInputs.
Module CV32E40PFetchEnable.
 #[local] Opaque norm read_signal run_process before_process comb_round.
 Lemma round_clock s : norm 1 (read_signal (round s) 287%nat) = norm 1 (read_signal s 7%nat).
 Proof.
   rewrite (wire 1118 process_1118 56%nat 287%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)),
     (wire 1117 process_1117 7%nat 56%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   unfold round. rewrite comb_round_preserves_unwritten_root by (vm_compute; reflexivity). reflexivity.
 Qed.
 Lemma round_reset s : norm 1 (read_signal (round s) 288%nat) = norm 1 (read_signal s 8%nat).
 Proof.
   rewrite (wire 1123 process_1123 57%nat 288%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)),
     (wire 1122 process_1122 8%nat 57%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   unfold round. rewrite comb_round_preserves_unwritten_root by exact reset_comb_unwritten. reflexivity.
 Qed.
 Lemma round_fetch_input s : norm 1 (read_signal s 36%nat) = 1 ->
   norm 1 (read_signal (round s) 304%nat) = 1.
 Proof.
   intros H. unfold round.
   rewrite (comb_cut_root cv32e40p_program 1528 process_1528 s 304%nat eq_refl eq_refl ltac:(vm_compute; reflexivity)),
     (assign_value _ process_1528 1 304%nat (rhs process_1528) eq_refl).
   unfold rhs. cbn [process_1528 process_body eval_expr]. rewrite norm_twice.
   rewrite <- (cut_final_root cv32e40p_program 1528 s 292%nat ltac:(vm_compute; reflexivity)).
   fold (round s).
   rewrite (wire 1527 process_1527 94%nat 292%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)),
     (wire 1526 process_1526 36%nat 94%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   unfold round. rewrite comb_round_preserves_unwritten_root by (vm_compute; reflexivity). rewrite H.
   destruct (bit_cases (read_signal (before_process cv32e40p_program 1528 s) 303%nat)) as [Hb|Hb]; rewrite Hb; reflexivity.
 Qed.
 Lemma fetch_unwritten : comb_root_unwrittenb cv32e40p_program 303%nat = true.
 Proof. vm_compute; reflexivity. Qed.
 Lemma fetch_writers : filter (writes_rootb 303%nat) (processes cv32e40p_program) = [process_8].
 Proof. vm_compute; reflexivity. Qed.
 Lemma sequential_fetch s old :
   norm 1 (apply_updates_root_value 303%nat old (process_updates cv32e40p_program s process_8)) =
   if norm 1 (read_signal s 288%nat) =? 0 then 0 else norm 1 (read_signal s 304%nat).
 Proof.
   rewrite process_nba_pruned_projection by reflexivity.
   change (statement_fuel cv32e40p_program) with 512%nat.
   cbn [nba_root_pruned process_8 process_body stmt_writers lvalue_root flat_map fold_left existsb Nat.eqb app orb].
   change (norm 1 (if norm 1 (read_signal s 288%nat) =? 0 then write_slice old 0 1 (norm 1 0)
     else write_slice old 0 1 (norm 1 (norm 1 (read_signal s 304%nat)))) =
     if norm 1 (read_signal s 288%nat) =? 0 then 0 else norm 1 (read_signal s 304%nat)).
   destruct (norm 1 (read_signal s 288%nat) =? 0); rewrite norm_write_low, !norm_twice; reflexivity.
 Qed.
 #[local] Opaque phase_driven_state PhaseSemantics process_updates process_matches_states apply_updates_root_value.
 Lemma phase_fetch ev pre : changed_signal ev <> 303%nat ->
   norm 1 (read_signal (PhaseSemantics cv32e40p_program ev pre) 303%nat) =
   if process_matches_states pre (phase_driven_state cv32e40p_program ev pre) process_8 then
     if norm 1 (read_signal (phase_driven_state cv32e40p_program ev pre) 288%nat) =? 0 then 0
     else norm 1 (read_signal (phase_driven_state cv32e40p_program ev pre) 304%nat)
   else norm 1 (read_signal pre 303%nat).
 Proof.
   intros He. rewrite phase_root_projection by auto using fetch_unwritten.
   unfold phase_update_chain, selected_on_transition.
   rewrite process_slice_sound, filter_swap, fetch_writers. cbn [filter].
   destruct (process_matches_states pre (phase_driven_state cv32e40p_program ev pre) process_8);
     cbn [flat_map]; rewrite ?app_nil_r; [apply sequential_fetch|reflexivity].
 Qed.
 Lemma driven_fetch ev pre : changed_signal ev <> 36%nat -> norm 1 (read_signal pre 36%nat) = 1 ->
   norm 1 (read_signal (phase_driven_state cv32e40p_program ev pre) 304%nat) = 1.
 Proof.
   intros He H. rewrite phase_driven_last_round. apply round_fetch_input.
   rewrite comb_iter_preserves_unwritten_root by (vm_compute; reflexivity).
   rewrite read_signal_write_other by exact He. exact H.
 Qed.
 Lemma driven_reset ev pre : changed_signal ev <> 8%nat -> read_signal pre 8%nat = 1 ->
   norm 1 (read_signal (phase_driven_state cv32e40p_program ev pre) 288%nat) = 1.
 Proof.
   intros He H. rewrite phase_driven_last_round, round_reset.
   rewrite comb_iter_preserves_unwritten_root by exact reset_comb_unwritten.
   rewrite read_signal_write_other by exact He. rewrite H. reflexivity.
 Qed.
 Lemma environment_fetch image s : norm 1 (read_signal (environment_state_image image s) 36%nat) = 1.
 Proof.
   unfold environment_state_image, obi_ports_image.
   rewrite lfp_candidate_preserves_unwritten_root by (vm_compute; reflexivity).
   unfold drive. cbn [fold_left fst snd]. rewrite read_signal_write_same. reflexivity.
 Qed.
 Lemma ungated_clock_internal : InternalBit 287%nat.
 Proof. split; [vm_compute; reflexivity|cbn; intuition discriminate]. Qed.
 Lemma lfp_clock s : norm 1 (read_signal (lfp_candidate cv32e40p_program s) 287%nat) = norm 1 (read_signal s 7%nat).
 Proof.
   unfold lfp_candidate. change (lfp_fuel cv32e40p_program) with 8%nat.
   rewrite (comb_iter_last cv32e40p_program 7), round_clock.
   rewrite comb_iter_preserves_unwritten_root by (vm_compute; reflexivity). reflexivity.
 Qed.
 Lemma reachable_rise_event image s : ResetReachable image s ->
   let pre := environment_state_image image (physical_state s) in
   process_matches_states pre (phase_driven_state cv32e40p_program clk_rise pre) process_8 = true.
 Proof.
   intros Hr. cbv zeta.
   assert (HB : BitRoot 287%nat (environment_state_image image (physical_state s))).
   { apply environment_bit; [exact ungated_clock_internal|].
     exact (reachable_internal_bit 287%nat image s ungated_clock_internal Hr). }
   assert (Hlo : read_signal (environment_state_image image (physical_state s)) 287%nat = 0).
   { unfold BitRoot in HB. rewrite <- (bit_normalized _ HB).
     unfold environment_state_image, obi_ports_image. rewrite lfp_clock.
     unfold drive. cbn [fold_left fst snd]. repeat rewrite read_signal_write_other by discriminate.
     rewrite (reachable_top_low image s Hr). reflexivity. }
   assert (Hhi : read_signal (phase_driven_state cv32e40p_program clk_rise
     (environment_state_image image (physical_state s))) 287%nat = 1).
   { assert (B : BitRoot 287%nat (phase_driven_state cv32e40p_program clk_rise
       (environment_state_image image (physical_state s)))).
     { rewrite phase_driven_last_round. apply round_bit; [exact (proj1 ungated_clock_internal)|].
       apply iter_bit; [exact (proj1 ungated_clock_internal)|]. unfold BitRoot.
       rewrite read_signal_write_other by discriminate. exact HB. }
     unfold BitRoot in B. rewrite <- (bit_normalized _ B), phase_driven_last_round, round_clock.
     rewrite comb_iter_preserves_unwritten_root by (vm_compute; reflexivity).
     rewrite read_signal_write_same. reflexivity. }
   cbn [process_matches_states process_8 process_kind process_events existsb event_spec_matches_states
     event_edge event_signal edge_fires]. rewrite Hlo, Hhi. reflexivity.
 Qed.
 #[local] Opaque environment_state_image full_cycle_image advance_retirement.
 Theorem reachable_cycle_fetch_enabled image s : ResetReachable image s ->
   norm 1 (read_signal (trace_rtl (physical_state (advance_retirement image s))) 303%nat) = 1.
 Proof.
   intros Hr. rewrite advance_physical.
   change (norm 1 (read_signal (settled_state_image image (physical_state s)) 303%nat) = 1).
   unfold settled_state_image. rewrite lfp_candidate_preserves_unwritten_root by exact fetch_unwritten.
   assert (Hr0 : read_signal (environment_state_image image (physical_state s)) 8%nat = 1).
   { rewrite environment_keeps_reset. exact (reachable_reset_stays_released image s Hr). }
   assert (Hrise : norm 1 (read_signal (rising_state_image image (physical_state s)) 303%nat) = 1).
   { unfold rising_state_image. rewrite phase_fetch by discriminate.
     rewrite (reachable_rise_event image s Hr).
     rewrite (driven_reset clk_rise (environment_state_image image (physical_state s)) ltac:(discriminate) Hr0).
     change (1 =? 0) with false. cbn beta iota zeta.
     apply driven_fetch; [discriminate|apply environment_fetch]. }
   unfold falling_state_image. rewrite phase_fetch by discriminate.
   rewrite driven_reset.
   - destruct (process_matches_states _ _ process_8); [|exact Hrise].
     apply driven_fetch; [discriminate|]. unfold rising_state_image.
     rewrite input_phase_frame by (vm_compute; reflexivity).
     rewrite read_signal_write_other by discriminate. apply environment_fetch.
   - discriminate.
   - unfold rising_state_image. rewrite input_phase_frame by (vm_compute; reflexivity).
     rewrite read_signal_write_other by discriminate. exact Hr0.
 Qed.
 Theorem reachable_fetch_enabled_or_reset image s : ResetReachable image s ->
   s = reset_retirement \/ norm 1 (read_signal (trace_rtl (physical_state s)) 303%nat) = 1.
 Proof. intros Hr. destruct Hr; [left; reflexivity|right; now apply reachable_cycle_fetch_enabled]. Qed.
 Print Assumptions reachable_cycle_fetch_enabled.
End CV32E40PFetchEnable.
