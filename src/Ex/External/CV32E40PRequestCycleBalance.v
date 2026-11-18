(** Exact whole-cycle counter and environment response recurrence. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVBitInvariant
 Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PReq39Trace
 Ex.External.CV32E40PAddiReachability Ex.External.CV32E40PAddiResetReleaseInvariant
 Ex.External.CV32E40PAddiOperandCone Ex.External.CV32E40PAddiIDEXAccept
 Ex.External.CV32E40PAddiDecoderPhase Ex.External.CV32E40PFetchFIFOCount
 Ex.External.CV32E40PInternalBits Ex.External.CV32E40PClockBoundary
 Ex.External.CV32E40PBusyHistory Ex.External.CV32E40PRequestCount
 Ex.External.CV32E40PRequestReachable Ex.External.CV32E40PGatedEdge
 Ex.External.CV32E40PRequestOutput.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVBitInvariant
 CV32E40PExtendedAST CV32E40PReq39Trace CV32E40PAddiReachability
 CV32E40PAddiResetReleaseInvariant CV32E40PAddiOperandCone CV32E40PAddiIDEXAccept
 CV32E40PAddiDecoderPhase CV32E40PFetchFIFOCount CV32E40PInternalBits
 CV32E40PClockBoundary CV32E40PBusyHistory CV32E40PRequestCount CV32E40PRequestReachable
 CV32E40PGatedEdge CV32E40PRequestOutput.
Local Open Scope Z_scope.
Module CV32E40PRequestCycleBalance.
 #[local] Opaque norm read_signal PhaseSemantics phase_driven_state comb_round environment_state_image.
 Lemma reachable_fall_no_prefetch image s : ResetReachable image s ->
   let pre := rising_state_image image (physical_state s) in
   process_matches_states pre (phase_driven_state cv32e40p_program clk_fall pre) process_12 = false.
 Proof.
   intros Hr. cbv zeta.
   assert (Hc : read_signal (phase_driven_state cv32e40p_program clk_fall
     (rising_state_image image (physical_state s))) 418%nat = 0).
   { pose proof (driven_internal_bit 418%nat clk_fall (rising_state_image image (physical_state s))
       prefetch_clock_internal ltac:(discriminate)
       (rising_internal_bit 418%nat image s prefetch_clock_internal Hr)) as Hb.
     unfold BitRoot in Hb. rewrite <- (bit_normalized _ Hb), phase_driven_last_round.
     apply round_low. rewrite comb_iter_preserves_unwritten_root by (vm_compute; reflexivity).
     apply read_signal_write_same. }
   assert (Hr0 : read_signal (rising_state_image image (physical_state s)) 8%nat = 1).
   { unfold rising_state_image. rewrite input_phase_frame by (vm_compute; reflexivity).
     rewrite read_signal_write_other by discriminate. rewrite environment_keeps_reset.
     exact (reachable_reset_stays_released image s Hr). }
   assert (Hrst : read_signal (phase_driven_state cv32e40p_program clk_fall
     (rising_state_image image (physical_state s))) 419%nat = 1).
   { pose proof (driven_internal_bit 419%nat clk_fall (rising_state_image image (physical_state s))
       prefetch_reset_internal ltac:(discriminate)
       (rising_internal_bit 419%nat image s prefetch_reset_internal Hr)) as Hb.
     unfold BitRoot in Hb. rewrite <- (bit_normalized _ Hb), phase_driven_last_round, controller_reset.
     rewrite comb_iter_preserves_unwritten_root by exact reset_comb_unwritten.
     rewrite read_signal_write_other by discriminate. rewrite Hr0. reflexivity. }
   cbn [process_matches_states process_12 process_kind process_events existsb event_spec_matches_states
     event_edge event_signal edge_fires]. rewrite Hc, Hrst.
   cbn [Z.eqb andb negb]. rewrite !andb_false_r. reflexivity.
 Qed.
 Definition Count s := norm 2 (read_signal (trace_rtl (physical_state s)) 440%nat).
 Definition Pending s := pending_count (physical_state s).
 Definition Gate image s := norm 1 (read_signal (environment_state_image image (physical_state s)) 314%nat).
 Definition InternalRequest image s := norm 1 (read_signal
   (phase_driven_state cv32e40p_program clk_rise (environment_state_image image (physical_state s))) 426%nat).
 Definition ExternalRequest image s := norm 1 (read_signal (request_sample image (physical_state s)) 426%nat).
 #[local] Transparent environment_state_image.
 Lemma environment_count image s : read_signal (environment_state_image image s) 440%nat = read_signal (trace_rtl s) 440%nat.
 Proof.
   unfold environment_state_image, obi_ports_image.
   rewrite lfp_candidate_preserves_unwritten_root by exact count_unwritten.
   unfold drive. cbn [fold_left fst snd]. repeat rewrite read_signal_write_other by discriminate. reflexivity.
 Qed.
 #[local] Opaque environment_state_image.
 Theorem reachable_cycle_count image s : ResetReachable image s ->
   Count (advance_retirement image s) =
   if Gate image s =? 1 then norm 2 (Count s + InternalRequest image s - Pending s) else Count s.
 Proof.
   intros Hr. unfold Count at 1. rewrite advance_physical.
   change (trace_rtl (full_cycle_image image (physical_state s))) with (settled_state_image image (physical_state s)).
   unfold settled_state_image. rewrite lfp_candidate_preserves_unwritten_root by exact count_unwritten.
   unfold falling_state_image. rewrite phase_counter by discriminate.
   rewrite (reachable_fall_no_prefetch image s Hr).
   unfold rising_state_image. rewrite (reachable_gated_request_balance image s Hr), environment_count. reflexivity.
 Qed.
 Lemma request_output_internal : InternalBit 16%nat.
 Proof. split; [vm_compute; reflexivity|cbn; intuition discriminate]. Qed.
 Theorem reachable_cycle_pending image s : ResetReachable image s ->
   Pending (advance_retirement image s) = ExternalRequest image s.
 Proof.
   intros Hr. unfold Pending. rewrite advance_physical.
   change ((match (if read_signal (environment_state_image image (physical_state s)) 16%nat =? 0
      then None else Some (read_signal (environment_state_image image (physical_state s)) 19%nat))
      with Some _ => 1 | None => 0 end) = ExternalRequest image s).
   pose proof (environment_bit 16%nat image (physical_state s) request_output_internal
     (reachable_internal_bit 16%nat image s request_output_internal Hr)) as Hb.
   unfold BitRoot in Hb.
   unfold ExternalRequest. rewrite <- (reachable_request_history image s Hr).
   destruct Hb as [H|H]; rewrite H; reflexivity.
 Qed.
 Theorem enabled_count_preservation_iff image s : ResetReachable image s -> Count s = Pending s -> Gate image s = 1 ->
   (Count (advance_retirement image s) = Pending (advance_retirement image s) <->
    InternalRequest image s = ExternalRequest image s).
 Proof.
   intros Hr HC HG. rewrite (reachable_cycle_count image s Hr), (reachable_cycle_pending image s Hr), HG.
   change (1 =? 1) with true. cbn beta iota zeta. rewrite HC.
   replace (Pending s + InternalRequest image s - Pending s) with (InternalRequest image s) by lia.
   unfold InternalRequest.
   destruct (bit_cases (read_signal (phase_driven_state cv32e40p_program clk_rise
     (environment_state_image image (physical_state s))) 426%nat)) as [H|H]; rewrite H; reflexivity.
 Qed.
 Print Assumptions reachable_cycle_count.
 Print Assumptions reachable_cycle_pending.
 Print Assumptions enabled_count_preservation_iff.
End CV32E40PRequestCycleBalance.
