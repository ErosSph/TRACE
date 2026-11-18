(** Genuine reset base case and an unconditional, unbounded x0 invariant.
    No expected writeback/retirement certificate is a reachability premise. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVCombCut.
Require Import Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PReq38Phase
  Ex.External.CV32E40PReq38Clock Ex.External.CV32E40PReq39Trace
  Ex.External.CV32E40PAddiRFFields Ex.External.CV32E40PAddiRFPhase
  Ex.External.CV32E40PAddiReachability.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVCombCut
  CV32E40PExtendedAST CV32E40PReq38Phase CV32E40PReq38Clock CV32E40PReq39Trace
  CV32E40PAddiRFFields CV32E40PAddiRFPhase CV32E40PAddiReachability.
Local Open Scope Z_scope.
Module CV32E40PAddiResetInvariant.
  Lemma initial_rf_unwritten : avoids_root 902%nat
    (filter is_initial (processes cv32e40p_program)) = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma initialized_rf_zero : read_signal initialized_zero 902%nat = 0.
  Proof.
    unfold initialized_zero, initialize.
    rewrite fold_run_process_preserves_root.
    - reflexivity.
    - exact (avoids_root_sound _ _ initial_rf_unwritten).
  Qed.
  Lemma pre_reset_rf_zero : read_signal pre_reset 902%nat = 0.
  Proof.
    unfold pre_reset. rewrite lfp_candidate_preserves_unwritten_root by exact fullcore_rf_comb_unwritten.
    rewrite read_signal_write_other by discriminate. exact initialized_rf_zero.
  Qed.
  Lemma post_reset_rf_zero : read_signal post_reset 902%nat = 0.
  Proof.
    unfold post_reset. rewrite phase_root_projection by
      (exact fullcore_rf_comb_unwritten || discriminate).
    unfold phase_update_chain. rewrite reset_updates_materialized, pre_reset_rf_zero.
    vm_compute. reflexivity.
  Qed.
  Lemma released_rf_zero : read_signal released 902%nat = 0.
  Proof.
    unfold released. rewrite phase_root_projection by
      (exact fullcore_rf_comb_unwritten || discriminate).
    unfold phase_update_chain.
    pose proof release_selects_no_edge_process as H.
    apply length_zero_iff_nil in H. rewrite H. cbn [flat_map apply_updates_root_value].
    exact post_reset_rf_zero.
  Qed.
  Lemma rf_field_is_register s r :
    rf_field (read_signal s 902%nat) r = rf_register s r.
  Proof.
    unfold rf_field, ExtendedSVBitSlice.ExtendedSVBitSlice.read_slice, rf_register, norm, mask.
    rewrite Nat2Z.inj_mul. reflexivity.
  Qed.
  Theorem actual_reset_all_registers_zero r :
    rf_register (trace_rtl (physical_state reset_retirement)) r = 0.
  Proof.
    change (rf_register released r = 0). unfold rf_register.
    rewrite released_rf_zero, Z.shiftr_0_l. reflexivity.
  Qed.
  Definition X0Zero (s : RetirementState) : Prop :=
    rf_register (trace_rtl (physical_state s)) 0 = 0.

  Lemma phase_preserves_x0 ev pre : changed_signal ev <> 902%nat ->
    rf_register pre 0 = 0 -> rf_register (PhaseSemantics cv32e40p_program ev pre) 0 = 0.
  Proof.
    intros He Hzero. rewrite <- rf_field_is_register.
    rewrite fullcore_phase_rf_field by (assumption || lia).
    cbv beta zeta. destruct (rf_trigger pre (phase_driven_state cv32e40p_program ev pre)).
    - reflexivity.
    - rewrite rf_field_is_register. exact Hzero.
  Qed.
  Lemma drive_preserves_rf s writes : Forall (fun pair => fst pair <> 902%nat) writes ->
    read_signal (drive s writes) 902%nat = read_signal s 902%nat.
  Proof.
    intros H. unfold drive. induction H in s |- *; cbn [fold_left].
    - reflexivity.
    - rewrite IHForall. apply read_signal_write_other. exact H.
  Qed.
  Lemma environment_preserves_rf image s :
    read_signal (environment_state_image image s) 902%nat = read_signal (trace_rtl s) 902%nat.
  Proof.
    unfold environment_state_image, obi_ports_image.
    rewrite lfp_candidate_preserves_unwritten_root by exact fullcore_rf_comb_unwritten.
    apply drive_preserves_rf. repeat constructor; discriminate.
  Qed.
  #[local] Opaque PhaseSemantics lfp_candidate.
  Lemma full_cycle_preserves_x0 image s :
    rf_register (trace_rtl s) 0 = 0 -> rf_register (trace_rtl (full_cycle_image image s)) 0 = 0.
  Proof.
    intros H. change (rf_register (settled_state_image image s) 0 = 0).
    unfold settled_state_image, rf_register.
    rewrite lfp_candidate_preserves_unwritten_root by exact fullcore_rf_comb_unwritten.
    change (rf_register (falling_state_image image s) 0 = 0).
    unfold falling_state_image. apply phase_preserves_x0; [discriminate|].
    unfold rising_state_image. apply phase_preserves_x0; [discriminate|].
    unfold rf_register. rewrite environment_preserves_rf. exact H.
  Qed.
  #[local] Opaque rf_register full_cycle_image.
  Theorem every_reset_reachable_state_has_zero_x0 image s :
    ResetReachable image s -> X0Zero s.
  Proof.
    intros H. induction H.
    - exact (actual_reset_all_registers_zero 0%nat).
    - unfold X0Zero in *. rewrite advance_physical. now apply full_cycle_preserves_x0.
  Qed.
  Print Assumptions actual_reset_all_registers_zero.
  Print Assumptions every_reset_reachable_state_has_zero_x0.
End CV32E40PAddiResetInvariant.
