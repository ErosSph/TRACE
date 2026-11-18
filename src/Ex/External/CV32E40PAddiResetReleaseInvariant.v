(** From actual reset reachability to ID/EX and RF reset inputs. No assumed
    reset guard in the conclusion, and no whole-CPU fixed-point premise. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice
  Lang.ExtendedSVCombCut Ex.Generated.CV32E40PExtendedAST
  Ex.External.CV32E40PReq39Trace Ex.External.CV32E40PReq38Clock
  Ex.External.CV32E40PAddiReachability Ex.External.CV32E40PAddiAdderInputs
  Ex.External.CV32E40PAddiOperandCone Ex.External.CV32E40PAddiDecoderPhase
  Ex.External.CV32E40PAddiIDEXAccept.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVProcessSlice
  ExtendedSVCombCut CV32E40PExtendedAST CV32E40PReq39Trace CV32E40PReq38Clock
  CV32E40PAddiReachability CV32E40PAddiAdderInputs CV32E40PAddiOperandCone
  CV32E40PAddiDecoderPhase CV32E40PAddiIDEXAccept.
Local Open Scope Z_scope.
Module CV32E40PAddiResetReleaseInvariant.
  Lemma input_phase_frame p root ev pre :
    comb_root_unwrittenb p root = true ->
    filter (writes_rootb root) (processes p) = [] ->
    read_signal (PhaseSemantics p ev pre) root =
      read_signal (write_signal pre (changed_signal ev) (new_value ev)) root.
  Proof.
    intros Hcomb Hwriters. unfold PhaseSemantics, phase_execute_order, execute_process_order.
    rewrite lfp_candidate_preserves_unwritten_root by exact Hcomb.
    rewrite read_signal_apply_updates, process_slice_sound.
    unfold selected_on_transition. rewrite filter_swap, Hwriters.
    cbn [filter flat_map apply_updates_root_value].
    unfold phase_driven_state. apply lfp_candidate_preserves_unwritten_root. exact Hcomb.
  Qed.
  Lemma reset_comb_unwritten : comb_root_unwrittenb cv32e40p_program 8%nat = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma reset_no_writers : filter (writes_rootb 8%nat) (processes cv32e40p_program) = [].
  Proof. vm_compute. reflexivity. Qed.
  Lemma release_input_high : read_signal released 8%nat = 1.
  Proof. unfold released. rewrite input_phase_frame by auto using reset_comb_unwritten, reset_no_writers.
    apply read_signal_write_same. Qed.
  Lemma environment_keeps_reset image s :
    read_signal (environment_state_image image s) 8%nat = read_signal (trace_rtl s) 8%nat.
  Proof.
    unfold environment_state_image, obi_ports_image.
    rewrite lfp_candidate_preserves_unwritten_root by exact reset_comb_unwritten.
    unfold drive. cbn [fold_left fst snd].
    repeat rewrite read_signal_write_other by discriminate. reflexivity.
  Qed.
  #[local] Opaque lfp_candidate PhaseSemantics.
  Lemma cycle_keeps_reset image s :
    read_signal (trace_rtl (full_cycle_image image s)) 8%nat = read_signal (trace_rtl s) 8%nat.
  Proof.
    change (read_signal (settled_state_image image s) 8%nat = read_signal (trace_rtl s) 8%nat).
    unfold settled_state_image. rewrite lfp_candidate_preserves_unwritten_root by exact reset_comb_unwritten.
    unfold falling_state_image, rising_state_image.
    rewrite !input_phase_frame by auto using reset_comb_unwritten, reset_no_writers.
    rewrite !read_signal_write_other by discriminate.
    rewrite input_phase_frame by auto using reset_comb_unwritten, reset_no_writers.
    rewrite read_signal_write_other by discriminate. apply environment_keeps_reset.
  Qed.
  Theorem reachable_reset_stays_released image s :
    ResetReachable image s -> read_signal (trace_rtl (physical_state s)) 8%nat = 1.
  Proof.
    intros H. induction H.
    - exact release_input_high.
    - rewrite advance_physical, cycle_keeps_reset. exact IHResetReachable.
  Qed.
  Lemma reset_wire s proc src dst :
    process_body proc = SAssign false (EVar 1 src) (LVar 1 dst) ->
    norm 1 (read_signal (run_process cv32e40p_program s proc) dst) = norm 1 (read_signal s src).
  Proof. intros H. rewrite (assign_value s proc 1 dst (EVar 1 src) H).
    cbn [eval_expr]. apply norm_twice. Qed.
  #[local] Opaque before_process comb_round run_process.
  Lemma round_reset_port s : norm 1 (read_signal (round s) 57%nat) = norm 1 (read_signal s 8%nat).
  Proof.
    unfold round. rewrite (comb_cut_root cv32e40p_program 1122 process_1122 s 57%nat
      eq_refl eq_refl ltac:(vm_compute; reflexivity)), (reset_wire _ process_1122 8%nat 57%nat eq_refl).
    rewrite before_process_keeps_root by (vm_compute; reflexivity). reflexivity.
  Qed.
  Lemma round_id_reset s : norm 1 (read_signal (round s) 561%nat) = norm 1 (read_signal s 8%nat).
  Proof.
    unfold round. rewrite (comb_cut_root cv32e40p_program 1130 process_1130 s 561%nat
      eq_refl eq_refl ltac:(vm_compute; reflexivity)), (reset_wire _ process_1130 57%nat 561%nat eq_refl).
    rewrite <- (cut_final_root cv32e40p_program 1130 s 57%nat ltac:(vm_compute; reflexivity)).
    apply round_reset_port.
  Qed.
  Lemma round_rf_reset s : norm 1 (read_signal (round s) 885%nat) = norm 1 (read_signal s 8%nat).
  Proof.
    unfold round. rewrite (comb_cut_root cv32e40p_program 1131 process_1131 s 885%nat
      eq_refl eq_refl ltac:(vm_compute; reflexivity)), (reset_wire _ process_1131 561%nat 885%nat eq_refl).
    rewrite <- (cut_final_root cv32e40p_program 1131 s 561%nat ltac:(vm_compute; reflexivity)).
    apply round_id_reset.
  Qed.
  Theorem reachable_rise_reset_guards image s : ResetReachable image s ->
    let driven := phase_driven_state cv32e40p_program clk_rise (environment_state_image image (physical_state s)) in
    norm 1 (read_signal driven 561%nat) = 1 /\ norm 1 (read_signal driven 885%nat) = 1.
  Proof.
    intros Hr. cbv zeta. rewrite phase_driven_last_round.
    split; [rewrite round_id_reset|rewrite round_rf_reset];
      rewrite comb_iter_preserves_unwritten_root by exact reset_comb_unwritten;
      rewrite read_signal_write_other by discriminate;
      rewrite environment_keeps_reset, (reachable_reset_stays_released image s Hr); reflexivity.
  Qed.
  Print Assumptions reachable_reset_stays_released.
  Print Assumptions reachable_rise_reset_guards.
End CV32E40PAddiResetReleaseInvariant.
