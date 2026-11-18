(** Actual gate output at cycle boundaries and exact reachable event selection. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVBitInvariant Lang.ExtendedSVRootProjection
 Lang.ExtendedSVProcessSlice Lang.ExtendedSVCombCut Ex.Generated.CV32E40PExtendedAST
 Ex.External.CV32E40PReq38Clock Ex.External.CV32E40PReq39Trace
 Ex.External.CV32E40PAddiReachability Ex.External.CV32E40PAddiResetReleaseInvariant
 Ex.External.CV32E40PAddiOperandCone Ex.External.CV32E40PAddiAdderInputs
 Ex.External.CV32E40PAddiIDEXAccept Ex.External.CV32E40PAddiDecoderPhase
 Ex.External.CV32E40PRequestWiring Ex.External.CV32E40PRequestReachable
 Ex.External.CV32E40PInternalBits.
Import ListNotations ExtendedSV ExtendedSVBitInvariant ExtendedSVRootProjection
 ExtendedSVProcessSlice ExtendedSVCombCut CV32E40PExtendedAST CV32E40PReq38Clock
 CV32E40PReq39Trace CV32E40PAddiReachability CV32E40PAddiResetReleaseInvariant
 CV32E40PAddiOperandCone CV32E40PAddiAdderInputs CV32E40PAddiIDEXAccept
 CV32E40PAddiDecoderPhase CV32E40PRequestWiring CV32E40PRequestReachable CV32E40PInternalBits.
Local Open Scope Z_scope.
Module CV32E40PClockBoundary.
 #[local] Opaque norm read_signal run_process before_process comb_round.
 Lemma round_input_clock s : norm 1 (read_signal (round s) 310%nat) = norm 1 (read_signal s 7%nat).
 Proof.
   rewrite (wire 1119 process_1119 287%nat 310%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   rewrite (wire 1118 process_1118 56%nat 287%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   rewrite (wire 1117 process_1117 7%nat 56%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   unfold round. rewrite comb_round_preserves_unwritten_root by (vm_compute; reflexivity). reflexivity.
 Qed.
 Lemma round_gate s : norm 1 (read_signal (round s) 418%nat) =
   norm 1 (Z.land (norm 1 (read_signal s 7%nat)) (norm 1 (read_signal (cut 1501 s) 314%nat))).
 Proof.
   rewrite (wire 1507 process_1507 381%nat 418%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   rewrite (wire 1506 process_1506 320%nat 381%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   rewrite (wire 1505 process_1505 284%nat 320%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   rewrite (wire 1503 process_1503 289%nat 284%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   rewrite (wire 1502 process_1502 313%nat 289%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   unfold round. rewrite (comb_cut_root cv32e40p_program 1501 process_1501 s 313%nat eq_refl eq_refl ltac:(vm_compute; reflexivity)),
     (assign_value _ process_1501 1 313%nat (rhs process_1501) eq_refl).
   unfold rhs. cbn [process_1501 process_body eval_expr]. rewrite norm_twice.
   rewrite <- (cut_final_root cv32e40p_program 1501 s 310%nat ltac:(vm_compute; reflexivity)).
   rewrite round_input_clock. reflexivity.
 Qed.
 Lemma round_low s : read_signal s 7%nat = 0 -> norm 1 (read_signal (round s) 418%nat) = 0.
 Proof. intros H. rewrite round_gate, H. change (norm 1 0) with 0. rewrite Z.land_0_l. reflexivity. Qed.
 Lemma lfp_low s : read_signal s 7%nat = 0 ->
   norm 1 (read_signal (lfp_candidate cv32e40p_program s) 418%nat) = 0.
 Proof.
   intros H. unfold lfp_candidate. change (lfp_fuel cv32e40p_program) with 8%nat.
   rewrite (comb_iter_last cv32e40p_program 7). apply round_low.
   rewrite comb_iter_preserves_unwritten_root by (vm_compute; reflexivity). exact H.
 Qed.
 #[local] Opaque lfp_candidate PhaseSemantics phase_driven_state.
 Lemma released_top_low : read_signal released 7%nat = 0.
 Proof.
   unfold released. rewrite input_phase_frame by (vm_compute; reflexivity).
   rewrite read_signal_write_other by discriminate.
   unfold CV32E40PReq38Phase.CV32E40PReq38Phase.post_reset.
   rewrite input_phase_frame by (vm_compute; reflexivity).
   rewrite read_signal_write_other by discriminate.
   unfold CV32E40PReq38Phase.CV32E40PReq38Phase.pre_reset.
   rewrite lfp_candidate_preserves_unwritten_root by (vm_compute; reflexivity).
   rewrite read_signal_write_other by discriminate.
   unfold CV32E40PReq38Phase.CV32E40PReq38Phase.initialized_zero, initialize.
   rewrite fold_run_process_preserves_root by (apply avoids_root_sound; vm_compute; reflexivity). reflexivity.
 Qed.
 Lemma cycle_top_low image s : read_signal (trace_rtl (full_cycle_image image s)) 7%nat = 0.
 Proof.
   change (read_signal (settled_state_image image s) 7%nat = 0).
   unfold settled_state_image. rewrite lfp_candidate_preserves_unwritten_root by (vm_compute; reflexivity).
   unfold falling_state_image. rewrite input_phase_frame by (vm_compute; reflexivity).
   apply read_signal_write_same.
 Qed.
 Theorem reachable_top_low image s : ResetReachable image s ->
   read_signal (trace_rtl (physical_state s)) 7%nat = 0.
 Proof. intros H. induction H; [exact released_top_low|]. rewrite advance_physical. apply cycle_top_low. Qed.
 Theorem reachable_environment_clock_low image s : ResetReachable image s ->
   read_signal (environment_state_image image (physical_state s)) 418%nat = 0.
 Proof.
   intros Hr. pose proof (environment_bit 418%nat image (physical_state s) prefetch_clock_internal
     (reachable_internal_bit 418%nat image s prefetch_clock_internal Hr)) as Hb.
   unfold BitRoot in Hb. rewrite <- (bit_normalized _ Hb).
   unfold environment_state_image, obi_ports_image. apply lfp_low.
   unfold drive. cbn [fold_left fst snd].
   repeat rewrite read_signal_write_other by discriminate. exact (reachable_top_low image s Hr).
 Qed.
 #[local] Transparent phase_driven_state.
 Theorem reachable_driven_reset_high image s : ResetReachable image s ->
   read_signal (phase_driven_state cv32e40p_program clk_rise
     (environment_state_image image (physical_state s))) 419%nat = 1.
 Proof.
   intros Hr.
   assert (Hb : BitRoot 419%nat (phase_driven_state cv32e40p_program clk_rise
     (environment_state_image image (physical_state s)))).
   { unfold phase_driven_state. apply lfp_bit; [exact (proj1 prefetch_reset_internal)|].
     unfold BitRoot. rewrite read_signal_write_other by discriminate.
     apply environment_bit; [exact prefetch_reset_internal|].
     exact (reachable_internal_bit 419%nat image s prefetch_reset_internal Hr). }
   unfold BitRoot in Hb. rewrite <- (bit_normalized _ Hb).
   rewrite phase_driven_last_round, controller_reset.
   rewrite comb_iter_preserves_unwritten_root by exact reset_comb_unwritten.
   rewrite read_signal_write_other by discriminate.
   rewrite environment_keeps_reset, (reachable_reset_stays_released image s Hr). reflexivity.
 Qed.
 #[local] Opaque phase_driven_state.
 Theorem reachable_prefetch_edge image s : ResetReachable image s ->
   let pre := environment_state_image image (physical_state s) in
   let driven := phase_driven_state cv32e40p_program clk_rise pre in
   process_matches_states pre driven process_12 = negb (read_signal driven 418%nat =? 0).
 Proof.
   intros Hr. cbv zeta. cbn [process_matches_states process_12 process_kind process_events
     existsb event_spec_matches_states event_edge event_signal edge_fires].
   rewrite (reachable_environment_clock_low image s Hr), (reachable_driven_reset_high image s Hr).
   cbn [Z.eqb andb]. rewrite andb_false_r, orb_false_r. reflexivity.
 Qed.
 Print Assumptions reachable_environment_clock_low.
 Print Assumptions reachable_prefetch_edge.
End CV32E40PClockBoundary.
