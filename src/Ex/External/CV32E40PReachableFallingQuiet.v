(** All reset-reachable states: real falling phase selects neither RF nor ID/EX.
    No ADDI, FIFO-capacity, normal-FSM or gate-enabled premise is required. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVBitInvariant Lang.ExtendedSVRootProjection Lang.ExtendedSVCombCut
 Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PReq39Trace
 Ex.External.CV32E40PAddiReachability Ex.External.CV32E40PClockBoundary
 Ex.External.CV32E40PInternalBits Ex.External.CV32E40PBusyHistory
 Ex.External.CV32E40PRequestWiring Ex.External.CV32E40PAddiResetReleaseInvariant
 Ex.External.CV32E40PAddiOperandCone Ex.External.CV32E40PAddiDecoderPhase
 Ex.External.CV32E40PAddiRFCycle Ex.External.CV32E40PAddiRFPhase
 Ex.External.CV32E40PAddiIDEXCycle Ex.External.CV32E40PAddiIDEXHold.
Import ListNotations ExtendedSV ExtendedSVBitInvariant ExtendedSVRootProjection ExtendedSVCombCut
 CV32E40PExtendedAST CV32E40PReq39Trace CV32E40PAddiReachability
 CV32E40PClockBoundary CV32E40PInternalBits CV32E40PBusyHistory
 CV32E40PRequestWiring CV32E40PAddiResetReleaseInvariant
 CV32E40PAddiOperandCone CV32E40PAddiDecoderPhase
 CV32E40PAddiRFCycle CV32E40PAddiRFPhase CV32E40PAddiIDEXCycle CV32E40PAddiIDEXHold.
Local Open Scope Z_scope.
Module CV32E40PReachableFallingQuiet.
#[local] Opaque norm read_signal comb_round run_process before_process.
Lemma round_id_clock s : norm 1 (read_signal (round s) 559%nat) =
 norm 1 (read_signal (round s) 418%nat).
Proof.
 rewrite (wire 1511 process_1511 284%nat 559%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)),
 (wire 1507 process_1507 381%nat 418%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)),
 (wire 1506 process_1506 320%nat 381%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)),
 (wire 1505 process_1505 284%nat 320%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
 reflexivity.
Qed.
Lemma round_rf_clock s : norm 1 (read_signal (round s) 884%nat) =
 norm 1 (read_signal (round s) 418%nat).
Proof.
 rewrite (wire 1512 process_1512 559%nat 884%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
 apply round_id_clock.
Qed.
Lemma event_ports_internal root : In root [559%nat;561%nat;884%nat;885%nat] -> InternalBit root.
Proof.
 intros [<-|[<-|[<-|[<-|[]]]]]; (split; [vm_compute; reflexivity|cbn; intuition discriminate]).
Qed.
Lemma rising_top_reset image s : ResetReachable image s ->
 read_signal (rising_state_image image (physical_state s)) 8%nat=1.
Proof.
 intros Hr. unfold rising_state_image.
 rewrite input_phase_frame by auto using reset_comb_unwritten, reset_no_writers.
 rewrite read_signal_write_other by discriminate.
 rewrite environment_keeps_reset. exact (reachable_reset_stays_released image s Hr).
Qed.
Lemma fall_clock_low pre root :
 (forall s, norm 1 (read_signal (round s) root)=norm 1 (read_signal (round s) 418%nat)) ->
 norm 1 (read_signal (phase_driven_state cv32e40p_program clk_fall pre) root)=0.
Proof.
 intros Hwire. rewrite phase_driven_last_round, Hwire. apply round_low.
 rewrite comb_iter_preserves_unwritten_root by (vm_compute; reflexivity).
 apply read_signal_write_same.
Qed.
Lemma fall_reset_high pre root : read_signal pre 8%nat=1 ->
 (forall s, norm 1 (read_signal (round s) root)=norm 1 (read_signal s 8%nat)) ->
 norm 1 (read_signal (phase_driven_state cv32e40p_program clk_fall pre) root)=1.
Proof.
 intros Hr Hwire. rewrite phase_driven_last_round, Hwire.
 rewrite comb_iter_preserves_unwritten_root by exact reset_comb_unwritten.
 rewrite read_signal_write_other by discriminate. rewrite Hr. reflexivity.
Qed.
Lemma reachable_fall_port_bit root image s : In root [559%nat;561%nat;884%nat;885%nat] ->
 ResetReachable image s -> BitRoot root
 (phase_driven_state cv32e40p_program clk_fall (rising_state_image image (physical_state s))).
Proof.
 intros Hin Hr. pose proof (event_ports_internal root Hin) as Hi.
 apply driven_internal_bit; [exact Hi| |now apply rising_internal_bit].
 cbn [In] in Hin. change (7%nat <> root). intuition congruence.
Qed.
Theorem reachable_fall_event_ports image s : ResetReachable image s ->
 let d := phase_driven_state cv32e40p_program clk_fall (rising_state_image image (physical_state s)) in
 read_signal d 559%nat=0 /\ read_signal d 561%nat=1 /\
 read_signal d 884%nat=0 /\ read_signal d 885%nat=1.
Proof.
 intros Hr. cbv zeta.
 assert (Hbit : forall root, In root [559%nat;561%nat;884%nat;885%nat] ->
   norm 1 (read_signal (phase_driven_state cv32e40p_program clk_fall
     (rising_state_image image (physical_state s))) root)=
   read_signal (phase_driven_state cv32e40p_program clk_fall
     (rising_state_image image (physical_state s))) root).
 { intros root Hin. apply bit_normalized. exact (reachable_fall_port_bit root image s Hin Hr). }
 rewrite <- (Hbit 559%nat ltac:(cbn; tauto)), <- (Hbit 561%nat ltac:(cbn; tauto)),
   <- (Hbit 884%nat ltac:(cbn; tauto)), <- (Hbit 885%nat ltac:(cbn; tauto)).
 split; [apply fall_clock_low; exact round_id_clock|].
 split; [apply fall_reset_high; [now apply rising_top_reset|exact round_id_reset]|].
 split; [apply fall_clock_low; exact round_rf_clock|].
 apply fall_reset_high; [now apply rising_top_reset|exact round_rf_reset].
Qed.
Theorem reachable_falling_quiet image s : ResetReachable image s ->
 FallingRFQuiet image (physical_state s) /\ FallingIDEXQuiet image (physical_state s).
Proof.
 intros Hr. destruct (reachable_fall_event_ports image s Hr) as (Hic & Hir & Hrc & Hrr).
 unfold FallingRFQuiet, FallingIDEXQuiet, rf_trigger.
 cbn [process_matches_states process_23 process_44 process_kind process_events existsb
   event_spec_matches_states event_edge event_signal edge_fires].
 rewrite Hic, Hir, Hrc, Hrr. cbn [Z.eqb andb negb].
 rewrite !andb_false_r. split; reflexivity.
Qed.
Corollary reachable_cycle_rf_frame image s : ResetReachable image s ->
 read_signal (trace_rtl (physical_state (advance_retirement image s))) 902%nat=
 read_signal (rising_state_image image (physical_state s)) 902%nat.
Proof.
 intros Hr. rewrite advance_physical. apply cycle_rf_equals_rising.
 exact (proj1 (reachable_falling_quiet image s Hr)).
Qed.
Corollary reachable_cycle_idex_frame image s root : ResetReachable image s -> In root idex_roots ->
 read_signal (trace_rtl (physical_state (advance_retirement image s))) root=
 read_signal (rising_state_image image (physical_state s)) root.
Proof.
 intros Hr Hi. rewrite advance_physical. apply cycle_idex_equals_rising; [exact Hi|].
 exact (proj2 (reachable_falling_quiet image s Hr)).
Qed.
Print Assumptions reachable_falling_quiet.
Print Assumptions reachable_cycle_rf_frame.
End CV32E40PReachableFallingQuiet.
