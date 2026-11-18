(** Actual RF rising-edge result survives falling phase and settling. *)
From Coq Require Import ZArith Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection
 Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiRFPhase
 Ex.External.CV32E40PReq39Trace.
Import ExtendedSV ExtendedSVRootProjection CV32E40PExtendedAST
 CV32E40PAddiRFPhase CV32E40PReq39Trace.
Module CV32E40PAddiRFCycle.
 Definition FallingRFQuiet image s :=
   rf_trigger (rising_state_image image s)
     (phase_driven_state cv32e40p_program clk_fall (rising_state_image image s)) = false.
 #[local] Opaque PhaseSemantics phase_driven_state read_signal.
 Theorem cycle_rf_equals_rising image s : FallingRFQuiet image s ->
   read_signal (trace_rtl (full_cycle_image image s)) 902%nat =
   read_signal (rising_state_image image s) 902%nat.
 Proof.
   intros H. change (read_signal (lfp_candidate cv32e40p_program
     (falling_state_image image s)) 902%nat = read_signal (rising_state_image image s) 902%nat).
   rewrite lfp_candidate_preserves_unwritten_root by exact fullcore_rf_comb_unwritten.
   unfold falling_state_image. apply no_rf_edge_preserves_fullcore_rf; [discriminate|exact H].
 Qed.
 Print Assumptions cycle_rf_equals_rising.
End CV32E40PAddiRFCycle.
