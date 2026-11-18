(** Raw event equivalence and full-cycle RF/IDEX frame when the gate is closed.
    No FIFO or normal-controller premise. This is not gate-enable progress. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVBitInvariant Lang.ExtendedSVRootProjection
 Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PReachableFallingQuiet
 Ex.External.CV32E40PInternalBits Ex.External.CV32E40PBusyHistory
 Ex.External.CV32E40PGatedEdge Ex.External.CV32E40PRequestReachable
 Ex.External.CV32E40PAddiResetReleaseInvariant Ex.External.CV32E40PAddiReachability
 Ex.External.CV32E40PReq39Trace Ex.External.CV32E40PAddiOperandCone
 Ex.External.CV32E40PAddiDecoderPhase Ex.External.CV32E40PAddiRFPhase
 Ex.External.CV32E40PAddiIDEXCycle Ex.External.CV32E40PAddiIDEXHold
 Ex.External.CV32E40PAddiEXOperandWiring Ex.External.CV32E40PAddiResetInvariant.
Require Import Ex.External.CV32E40PRequestCycleBalance.
Import ListNotations ExtendedSV ExtendedSVBitInvariant ExtendedSVRootProjection
 CV32E40PExtendedAST CV32E40PReachableFallingQuiet CV32E40PInternalBits CV32E40PBusyHistory
 CV32E40PGatedEdge CV32E40PRequestReachable CV32E40PAddiResetReleaseInvariant
 CV32E40PAddiReachability CV32E40PReq39Trace CV32E40PAddiOperandCone
 CV32E40PAddiDecoderPhase CV32E40PAddiRFPhase CV32E40PAddiIDEXCycle
 CV32E40PAddiIDEXHold CV32E40PAddiEXOperandWiring CV32E40PAddiResetInvariant.
Import CV32E40PRequestCycleBalance.
Local Open Scope Z_scope.
Module CV32E40PReachableGatedPipeline.
Definition ports : list nat := [559%nat;561%nat;884%nat;885%nat].
Definition mapped root : nat := if (root =? 559)%nat || (root =? 884)%nat then 418%nat else 419%nat.
Lemma mapped_internal root : In root ports -> InternalBit (mapped root).
Proof.
 intros [<-|[<-|[<-|[<-|[]]]]]; cbn [mapped Nat.eqb orb];
 auto using prefetch_clock_internal, prefetch_reset_internal.
Qed.
#[local] Opaque norm read_signal comb_round.
Lemma round_ports root s : In root ports ->
 norm 1 (read_signal (round s) root)=norm 1 (read_signal (round s) (mapped root)).
Proof.
 intros [<-|[<-|[<-|[<-|[]]]]]; cbn [mapped Nat.eqb orb].
 - apply round_id_clock.
 - rewrite round_id_reset, controller_reset. reflexivity.
 - apply round_rf_clock.
 - rewrite round_rf_reset, controller_reset. reflexivity.
Qed.
Lemma lfp_ports root s : In root ports ->
 norm 1 (read_signal (lfp_candidate cv32e40p_program s) root)=
 norm 1 (read_signal (lfp_candidate cv32e40p_program s) (mapped root)).
Proof.
 intros Hin. unfold lfp_candidate. change (lfp_fuel cv32e40p_program) with 8%nat.
 rewrite (comb_iter_last cv32e40p_program 7). now apply round_ports.
Qed.
Lemma environment_ports root image s : In root ports -> ResetReachable image s ->
 read_signal (environment_state_image image (physical_state s)) root=
 read_signal (environment_state_image image (physical_state s)) (mapped root).
Proof.
 intros Hi Hr.
 pose proof (event_ports_internal root Hi) as Hroot.
 pose proof (mapped_internal root Hi) as Hmapped.
 pose proof (environment_bit root image (physical_state s) Hroot
   (reachable_internal_bit root image s Hroot Hr)) as Ha.
 pose proof (environment_bit (mapped root) image (physical_state s) Hmapped
   (reachable_internal_bit (mapped root) image s Hmapped Hr)) as Hb.
 rewrite <- (bit_normalized _ Ha), <- (bit_normalized _ Hb).
 unfold environment_state_image, obi_ports_image. now apply lfp_ports.
Qed.
Lemma driven_ports root image s : In root ports -> ResetReachable image s ->
 let pre := environment_state_image image (physical_state s) in
 read_signal (phase_driven_state cv32e40p_program clk_rise pre) root=
 read_signal (phase_driven_state cv32e40p_program clk_rise pre) (mapped root).
Proof.
 intros Hi Hr. cbv zeta.
 assert (HB : forall r, InternalBit r -> BitRoot r (phase_driven_state cv32e40p_program clk_rise
   (environment_state_image image (physical_state s)))).
 { intros r Hir. apply driven_internal_bit; [exact Hir| |].
   - apply (external_other r 7 (proj2 Hir)); cbn; tauto.
   - apply environment_bit; [exact Hir|exact (reachable_internal_bit r image s Hir Hr)]. }
 rewrite <- (bit_normalized _ (HB root (event_ports_internal root Hi))),
   <- (bit_normalized _ (HB (mapped root) (mapped_internal root Hi))).
 unfold phase_driven_state. now apply lfp_ports.
Qed.
#[local] Opaque phase_driven_state environment_state_image.
Theorem reachable_pipeline_events image s : ResetReachable image s ->
 let pre := environment_state_image image (physical_state s) in
 let d := phase_driven_state cv32e40p_program clk_rise pre in
 rf_trigger pre d=(norm 1 (read_signal pre 314%nat)=?1) /\
 process_matches_states pre d process_23=(norm 1 (read_signal pre 314%nat)=?1).
Proof.
 intros Hr. cbv zeta. rewrite <- (reachable_event_iff_gate image s Hr).
 unfold rf_trigger.
 cbn [process_matches_states process_12 process_23 process_44 process_kind process_events
   existsb event_spec_matches_states event_edge event_signal].
 unfold event_spec_matches_states. cbn [event_edge event_signal].
 rewrite (environment_ports 559%nat image s ltac:(cbn [ports In]; tauto) Hr),
 (environment_ports 561%nat image s ltac:(cbn [ports In]; tauto) Hr),
 (environment_ports 884%nat image s ltac:(cbn [ports In]; tauto) Hr),
 (environment_ports 885%nat image s ltac:(cbn [ports In]; tauto) Hr),
 (driven_ports 559%nat image s ltac:(cbn [ports In]; tauto) Hr),
 (driven_ports 561%nat image s ltac:(cbn [ports In]; tauto) Hr),
 (driven_ports 884%nat image s ltac:(cbn [ports In]; tauto) Hr),
 (driven_ports 885%nat image s ltac:(cbn [ports In]; tauto) Hr).
 split; reflexivity.
Qed.

(** A small projected interface for consumers that already know the real
    pre-edge gate bit.  Keeping this next to [reachable_pipeline_events]
    avoids rebuilding or exporting its large generated event expression. *)
Theorem reachable_open_gate_idex_event image s : ResetReachable image s ->
 Gate image s = 1 ->
 process_matches_states
   (environment_state_image image (physical_state s))
   (phase_driven_state cv32e40p_program clk_rise
     (environment_state_image image (physical_state s))) process_23 = true.
Proof.
 intros Hr Hg.
 unfold Gate in Hg.
 rewrite (proj2 (reachable_pipeline_events image s Hr)), Hg. reflexivity.
Qed.
Theorem reachable_closed_gate_rf image s : ResetReachable image s ->
 norm 1 (read_signal (environment_state_image image (physical_state s)) 314%nat)=0 ->
 read_signal (trace_rtl (physical_state (advance_retirement image s))) 902%nat=
 read_signal (trace_rtl (physical_state s)) 902%nat.
Proof.
 intros Hr Hg. rewrite (reachable_cycle_rf_frame image s Hr). unfold rising_state_image.
 rewrite (no_rf_edge_preserves_fullcore_rf clk_rise _ ltac:(discriminate)).
 - apply environment_preserves_rf.
 - rewrite (proj1 (reachable_pipeline_events image s Hr)), Hg. reflexivity.
Qed.
Theorem reachable_closed_gate_idex image s root : ResetReachable image s -> In root idex_roots ->
 norm 1 (read_signal (environment_state_image image (physical_state s)) 314%nat)=0 ->
 read_signal (trace_rtl (physical_state (advance_retirement image s))) root=
 read_signal (trace_rtl (physical_state s)) root.
Proof.
 intros Hr Hi Hg. rewrite (reachable_cycle_idex_frame image s root Hr Hi). unfold rising_state_image.
 rewrite (unselected_idex_preserved clk_rise _ root Hi).
 - now apply environment_keeps_idex.
 - cbn [idex_roots In] in Hi. change (7%nat <> root). intuition congruence.
 - rewrite (proj2 (reachable_pipeline_events image s Hr)), Hg. reflexivity.
Qed.
Print Assumptions reachable_pipeline_events.
Print Assumptions reachable_open_gate_idex_event.
Print Assumptions reachable_closed_gate_rf.
Print Assumptions reachable_closed_gate_idex.
End CV32E40PReachableGatedPipeline.
