(** Actual sleep-register sampling history across a complete real cycle. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice
 Lang.ExtendedSVNBAProjection Lang.ExtendedSVBitInvariant
 Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiOperands
 Ex.External.CV32E40PAddiDecoderPhase Ex.External.CV32E40PAddiOperandCone
 Ex.External.CV32E40PAddiIDEXAccept Ex.External.CV32E40PReq39Trace
 Ex.External.CV32E40PAddiReachability Ex.External.CV32E40PAddiResetReleaseInvariant
 Ex.External.CV32E40PInternalBits Ex.External.CV32E40PFetchEnable
 Ex.External.CV32E40PSleepGate Ex.External.CV32E40PBusyCone.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVProcessSlice
 ExtendedSVNBAProjection ExtendedSVBitInvariant CV32E40PExtendedAST
 CV32E40PAddiOperands CV32E40PAddiDecoderPhase CV32E40PAddiOperandCone CV32E40PAddiIDEXAccept
 CV32E40PReq39Trace CV32E40PAddiReachability CV32E40PAddiResetReleaseInvariant
 CV32E40PInternalBits CV32E40PFetchEnable CV32E40PSleepGate CV32E40PBusyCone.
Local Open Scope Z_scope.
Module CV32E40PBusyHistory.
 Lemma busy_unwritten : comb_root_unwrittenb cv32e40p_program 305%nat = true.
 Proof. vm_compute; reflexivity. Qed.
 Lemma busy_writers : filter (writes_rootb 305%nat) (processes cv32e40p_program) = [process_8].
 Proof. vm_compute; reflexivity. Qed.
 Lemma sequential_busy s old :
   norm 1 (apply_updates_root_value 305%nat old (process_updates cv32e40p_program s process_8)) =
   if norm 1 (read_signal s 288%nat) =? 0 then 0 else norm 1 (read_signal s 306%nat).
 Proof.
   rewrite process_nba_pruned_projection by reflexivity.
   change (statement_fuel cv32e40p_program) with 512%nat.
   cbn [nba_root_pruned process_8 process_body stmt_writers lvalue_root flat_map fold_left existsb Nat.eqb app orb].
   change (norm 1 (if norm 1 (read_signal s 288%nat) =? 0 then write_slice old 0 1 (norm 1 0)
     else write_slice old 0 1 (norm 1 (norm 1 (read_signal s 306%nat)))) =
     if norm 1 (read_signal s 288%nat) =? 0 then 0 else norm 1 (read_signal s 306%nat)).
   destruct (norm 1 (read_signal s 288%nat) =? 0); rewrite norm_write_low, !norm_twice; reflexivity.
 Qed.
 #[local] Opaque phase_driven_state PhaseSemantics process_updates process_matches_states apply_updates_root_value.
 Lemma phase_busy ev pre : changed_signal ev <> 305%nat ->
   norm 1 (read_signal (PhaseSemantics cv32e40p_program ev pre) 305%nat) =
   if process_matches_states pre (phase_driven_state cv32e40p_program ev pre) process_8 then
     if norm 1 (read_signal (phase_driven_state cv32e40p_program ev pre) 288%nat) =? 0 then 0
     else norm 1 (read_signal (phase_driven_state cv32e40p_program ev pre) 306%nat)
   else norm 1 (read_signal pre 305%nat).
 Proof.
   intros He. rewrite phase_root_projection by auto using busy_unwritten.
   unfold phase_update_chain, selected_on_transition.
   rewrite process_slice_sound, filter_swap, busy_writers. cbn [filter].
   destruct (process_matches_states pre (phase_driven_state cv32e40p_program ev pre) process_8);
     cbn [flat_map]; rewrite ?app_nil_r; [apply sequential_busy|reflexivity].
 Qed.
 Lemma ungated_reset_internal : InternalBit 288%nat.
 Proof. split; [vm_compute; reflexivity|cbn; intuition discriminate]. Qed.
 Lemma rising_internal_bit root image s : InternalBit root -> ResetReachable image s ->
   BitRoot root (rising_state_image image (physical_state s)).
 Proof.
   intros Hi Hr. unfold rising_state_image. apply phase_bit; [exact (proj1 Hi)| |].
   - apply (external_other root 7 (proj2 Hi)); cbn; tauto.
   - apply environment_bit; [exact Hi|]. exact (reachable_internal_bit root image s Hi Hr).
 Qed.
 Lemma driven_internal_bit root ev pre : InternalBit root -> changed_signal ev <> root ->
   BitRoot root pre -> BitRoot root (phase_driven_state cv32e40p_program ev pre).
 Proof.
   intros Hi He Hb. rewrite phase_driven_last_round. apply round_bit; [exact (proj1 Hi)|].
   apply iter_bit; [exact (proj1 Hi)|]. unfold BitRoot. rewrite read_signal_write_other by exact He. exact Hb.
 Qed.
 #[local] Opaque environment_state_image norm read_signal comb_round.
 Lemma reachable_fall_no_sleep_event image s : ResetReachable image s ->
   let pre := rising_state_image image (physical_state s) in
   process_matches_states pre (phase_driven_state cv32e40p_program clk_fall pre) process_8 = false.
 Proof.
   intros Hr. cbv zeta.
   assert (Hc : read_signal (phase_driven_state cv32e40p_program clk_fall
     (rising_state_image image (physical_state s))) 287%nat = 0).
   { pose proof (driven_internal_bit 287%nat clk_fall (rising_state_image image (physical_state s))
       ungated_clock_internal ltac:(discriminate)
       (rising_internal_bit 287%nat image s ungated_clock_internal Hr)) as Hb.
     unfold BitRoot in Hb. rewrite <- (bit_normalized _ Hb), phase_driven_last_round, round_clock.
     rewrite comb_iter_preserves_unwritten_root by (vm_compute; reflexivity).
     rewrite read_signal_write_same. reflexivity. }
   assert (Hr0 : read_signal (rising_state_image image (physical_state s)) 8%nat = 1).
   { unfold rising_state_image. rewrite input_phase_frame by (vm_compute; reflexivity).
     rewrite read_signal_write_other by discriminate. rewrite environment_keeps_reset.
     exact (reachable_reset_stays_released image s Hr). }
   assert (Hrst : read_signal (phase_driven_state cv32e40p_program clk_fall
     (rising_state_image image (physical_state s))) 288%nat = 1).
   { pose proof (driven_internal_bit 288%nat clk_fall (rising_state_image image (physical_state s))
       ungated_reset_internal ltac:(discriminate)
       (rising_internal_bit 288%nat image s ungated_reset_internal Hr)) as Hb.
     unfold BitRoot in Hb. rewrite <- (bit_normalized _ Hb).
     exact (driven_reset clk_fall (rising_state_image image (physical_state s)) ltac:(discriminate) Hr0). }
   cbn [process_matches_states process_8 process_kind process_events existsb event_spec_matches_states
     event_edge event_signal edge_fires]. rewrite Hc, Hrst.
   cbn [Z.eqb andb negb]. rewrite !andb_false_r. reflexivity.
 Qed.
 Definition sampled_busy image s := norm 1 (read_signal
   (phase_driven_state cv32e40p_program clk_rise (environment_state_image image (physical_state s))) 306%nat).
 Theorem reachable_cycle_busy_history image s : ResetReachable image s ->
   norm 1 (read_signal (trace_rtl (physical_state (advance_retirement image s))) 305%nat) = sampled_busy image s.
 Proof.
   intros Hr. rewrite advance_physical.
   change (norm 1 (read_signal (settled_state_image image (physical_state s)) 305%nat) = sampled_busy image s).
   unfold settled_state_image. rewrite lfp_candidate_preserves_unwritten_root by exact busy_unwritten.
   unfold falling_state_image. rewrite phase_busy by discriminate.
   rewrite (reachable_fall_no_sleep_event image s Hr).
   unfold rising_state_image. rewrite phase_busy by discriminate.
   rewrite (reachable_rise_event image s Hr).
   assert (Hrst : read_signal (environment_state_image image (physical_state s)) 8%nat = 1).
   { rewrite environment_keeps_reset. exact (reachable_reset_stays_released image s Hr). }
   rewrite (driven_reset clk_rise (environment_state_image image (physical_state s)) ltac:(discriminate) Hrst).
   reflexivity.
 Qed.
 Theorem sampled_busy_enables_next_prefetch image s : ResetReachable image s -> sampled_busy image s = 1 ->
   let pre := environment_state_image image (physical_state (advance_retirement image s)) in
   process_matches_states pre (phase_driven_state cv32e40p_program clk_rise pre) process_12 = true.
 Proof.
   intros Hr Hb. apply reachable_busy_selects_prefetch; [now constructor|].
   now rewrite (reachable_cycle_busy_history image s Hr).
 Qed.
 #[local] Transparent environment_state_image.
 Lemma sampled_busy_from_count image s :
   norm 2 (read_signal (trace_rtl (physical_state s)) 440%nat) <> 0 -> sampled_busy image s = 1.
 Proof.
   intros H. unfold sampled_busy. apply counter_busy_phase; [discriminate|].
   unfold environment_state_image, obi_ports_image.
   rewrite lfp_candidate_preserves_unwritten_root by (vm_compute; reflexivity).
   unfold drive. cbn [fold_left fst snd]. repeat rewrite read_signal_write_other by discriminate. exact H.
 Qed.
 #[local] Opaque environment_state_image.
 Theorem outstanding_keeps_next_gate image s : ResetReachable image s ->
   norm 2 (read_signal (trace_rtl (physical_state s)) 440%nat) <> 0 ->
   norm 1 (read_signal (trace_rtl (physical_state (advance_retirement image s))) 305%nat) = 1 /\
   let pre := environment_state_image image (physical_state (advance_retirement image s)) in
   process_matches_states pre (phase_driven_state cv32e40p_program clk_rise pre) process_12 = true.
 Proof.
   intros Hr H. pose proof (sampled_busy_from_count image s H) as Hb. split.
   - now rewrite (reachable_cycle_busy_history image s Hr).
   - now apply sampled_busy_enables_next_prefetch.
 Qed.
 Print Assumptions reachable_cycle_busy_history.
 Print Assumptions sampled_busy_enables_next_prefetch.
 Print Assumptions outstanding_keeps_next_gate.
End CV32E40PBusyHistory.
