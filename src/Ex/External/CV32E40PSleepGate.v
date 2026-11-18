(** Low-phase sleep-control cone, composed with the actual gated event. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVCombCut
 Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiDecoder
 Ex.External.CV32E40PAddiForwardControl Ex.External.CV32E40PAddiDecoderPhase
 Ex.External.CV32E40PAddiOperandCone Ex.External.CV32E40PAddiIDEXAccept
 Ex.External.CV32E40PFetchFIFOCount Ex.External.CV32E40PRequestWiring
 Ex.External.CV32E40PReq39Trace Ex.External.CV32E40PAddiReachability
 Ex.External.CV32E40PClockBoundary Ex.External.CV32E40PGatedEdge
 Ex.External.CV32E40PFetchEnable Ex.External.CV32E40PRequestReachable.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVCombCut
 CV32E40PExtendedAST CV32E40PAddiDecoder CV32E40PAddiForwardControl
 CV32E40PAddiDecoderPhase CV32E40PAddiOperands.CV32E40PAddiOperands CV32E40PAddiOperandCone CV32E40PAddiIDEXAccept
 CV32E40PFetchFIFOCount CV32E40PRequestWiring CV32E40PReq39Trace
 CV32E40PAddiReachability CV32E40PClockBoundary CV32E40PGatedEdge
 CV32E40PFetchEnable CV32E40PRequestReachable.
Local Open Scope Z_scope.
Import CV32E40PAddiAdderInputs.CV32E40PAddiAdderInputs.
Module CV32E40PSleepGate.
 #[local] Opaque norm read_signal write_signal.
 Lemma low_latch_process s : norm 1 (read_signal s 310%nat) = 0 ->
   norm 1 (read_signal (run_process cv32e40p_program s process_1500) 314%nat) =
   norm 1 (Z.lor (norm 1 (read_signal s 311%nat)) (norm 1 (read_signal s 312%nat))).
 Proof.
   intros H. unfold run_process. change (statement_fuel cv32e40p_program) with 512%nat.
   cbn [process_1500 process_body]. rewrite exec_sequence, fold_one, exec_sequence, fold_one, exec_if.
   cbn [eval_expr blocking_state]. rewrite H. change (norm 1 (Z.lnot 0)) with 1.
   cbn [exec_stmt blocking_state pending_nba emitted_updates apply_nba apply_updates
     resolve_update resolve_lvalue apply_update update_signal update_offset update_width update_value eval_expr Z.eqb Pos.eqb app fold_left].
   unfold apply_update. cbn [update_signal update_offset update_width update_value].
   rewrite read_signal_write_same, norm_write_low, !norm_twice. reflexivity.
 Qed.
 #[local] Opaque run_process before_process comb_round.
 Lemma busy_enable s : norm 1 (read_signal s 303%nat) = 1 ->
   norm 1 (read_signal s 305%nat) = 1 ->
   norm 1 (read_signal (round s) 311%nat) = 1.
 Proof.
   intros Hf Hb.
   rewrite (wire 1499 process_1499 309%nat 311%nat s eq_refl eq_refl eq_refl
     ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   unfold round. rewrite (comb_cut_root cv32e40p_program 1497 process_1497 s 309%nat
     eq_refl eq_refl ltac:(vm_compute; reflexivity)),
     (assign_value _ process_1497 1 309%nat (rhs process_1497) eq_refl).
   unfold rhs. cbn [process_1497 process_body eval_expr]. rewrite !norm_twice.
   rewrite (before_process_keeps_root cv32e40p_program 1497 s 303%nat ltac:(vm_compute; reflexivity)),
     (before_process_keeps_root cv32e40p_program 1497 s 305%nat ltac:(vm_compute; reflexivity)), Hf, Hb.
   destruct (bit_cases (read_signal (before_process cv32e40p_program 1497 s) 302%nat)) as [H|H];
     rewrite H; reflexivity.
 Qed.
 Theorem low_round_busy_gate s : norm 1 (read_signal s 7%nat) = 0 ->
   norm 1 (read_signal s 303%nat) = 1 -> norm 1 (read_signal s 305%nat) = 1 ->
   norm 1 (read_signal (round s) 314%nat) = 1.
 Proof.
   intros Hc Hf Hb. unfold round.
   rewrite (comb_cut_root cv32e40p_program 1500 process_1500 s 314%nat
     eq_refl eq_refl ltac:(vm_compute; reflexivity)), low_latch_process.
   - rewrite <- (cut_final_root cv32e40p_program 1500 s 311%nat ltac:(vm_compute; reflexivity)).
     fold (round s). rewrite (busy_enable s Hf Hb).
     destruct (bit_cases (read_signal (before_process cv32e40p_program 1500 s) 312%nat)) as [H|H];
       rewrite H; reflexivity.
   - rewrite <- (cut_final_root cv32e40p_program 1500 s 310%nat ltac:(vm_compute; reflexivity)).
     fold (round s). rewrite round_input_clock. exact Hc.
 Qed.
 Theorem low_lfp_busy_gate s : norm 1 (read_signal s 7%nat) = 0 ->
   norm 1 (read_signal s 303%nat) = 1 -> norm 1 (read_signal s 305%nat) = 1 ->
   norm 1 (read_signal (lfp_candidate cv32e40p_program s) 314%nat) = 1.
 Proof.
   intros Hc Hf Hb. unfold lfp_candidate. change (lfp_fuel cv32e40p_program) with 8%nat.
   rewrite (comb_iter_last cv32e40p_program 7). apply low_round_busy_gate;
     rewrite comb_iter_preserves_unwritten_root by (vm_compute; reflexivity); assumption.
 Qed.
 #[local] Opaque lfp_candidate PhaseSemantics phase_driven_state.
 Theorem reachable_busy_gate image s : ResetReachable image s ->
   norm 1 (read_signal (trace_rtl (physical_state s)) 303%nat) = 1 ->
   norm 1 (read_signal (trace_rtl (physical_state s)) 305%nat) = 1 ->
   norm 1 (read_signal (environment_state_image image (physical_state s)) 314%nat) = 1.
 Proof.
   intros Hr Hf Hb. unfold environment_state_image, obi_ports_image.
   apply low_lfp_busy_gate; unfold drive; cbn [fold_left fst snd];
     repeat rewrite read_signal_write_other by discriminate.
   - rewrite (reachable_top_low image s Hr). reflexivity.
   - exact Hf.
   - exact Hb.
 Qed.
 Theorem reachable_busy_event image s : ResetReachable image s ->
   norm 1 (read_signal (trace_rtl (physical_state s)) 303%nat) = 1 ->
   norm 1 (read_signal (trace_rtl (physical_state s)) 305%nat) = 1 ->
   let pre := environment_state_image image (physical_state s) in
   process_matches_states pre (phase_driven_state cv32e40p_program clk_rise pre) process_12 = true.
 Proof.
   intros Hr Hf Hb. cbv zeta. rewrite (reachable_event_iff_gate image s Hr),
     (reachable_busy_gate image s Hr Hf Hb). reflexivity.
 Qed.
 Lemma reset_not_busy : norm 1 (read_signal (trace_rtl (physical_state reset_retirement)) 305%nat) = 0.
 Proof. vm_compute; reflexivity. Qed.
 Theorem reachable_busy_selects_prefetch image s : ResetReachable image s ->
   norm 1 (read_signal (trace_rtl (physical_state s)) 305%nat) = 1 ->
   let pre := environment_state_image image (physical_state s) in
   process_matches_states pre (phase_driven_state cv32e40p_program clk_rise pre) process_12 = true.
 Proof.
   intros Hr Hb. apply reachable_busy_event; [exact Hr| |exact Hb].
   destruct (reachable_fetch_enabled_or_reset image s Hr) as [E|H]; [|exact H].
   subst s. rewrite reset_not_busy in Hb. discriminate.
 Qed.
 Theorem reachable_busy_request_balance image s : ResetReachable image s ->
   norm 1 (read_signal (trace_rtl (physical_state s)) 305%nat) = 1 ->
   let pre := environment_state_image image (physical_state s) in
   let driven := phase_driven_state cv32e40p_program clk_rise pre in
   norm 2 (read_signal (PhaseSemantics cv32e40p_program clk_rise pre) 440%nat) =
   norm 2 (norm 2 (read_signal pre 440%nat) + norm 1 (read_signal driven 426%nat)
       - pending_count (physical_state s)).
 Proof.
   intros Hr Hb. cbv zeta. rewrite (reachable_rise_balance image s Hr),
     (reachable_busy_selects_prefetch image s Hr Hb). reflexivity.
 Qed.
 Print Assumptions reachable_busy_event.
 Print Assumptions reachable_busy_selects_prefetch.
 Print Assumptions reachable_busy_request_balance.
End CV32E40PSleepGate.
