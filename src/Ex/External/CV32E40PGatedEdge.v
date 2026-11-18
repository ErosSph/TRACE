(** Real gate latch -> real prefetch event, from original reset reachability. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVBitInvariant Lang.ExtendedSVRootProjection
 Lang.ExtendedSVCombCut Ex.Generated.CV32E40PExtendedAST
 Ex.External.CV32E40PAddiDecoder Ex.External.CV32E40PAddiForwardControl
 Ex.External.CV32E40PAddiDecoderPhase Ex.External.CV32E40PAddiOperandCone
 Ex.External.CV32E40PAddiIDEXAccept Ex.External.CV32E40PFetchFIFOCount
 Ex.External.CV32E40PReq39Trace Ex.External.CV32E40PAddiReachability
 Ex.External.CV32E40PInternalBits Ex.External.CV32E40PClockBoundary
 Ex.External.CV32E40PRequestReachable.
Import ListNotations ExtendedSV ExtendedSVBitInvariant ExtendedSVRootProjection ExtendedSVCombCut
 CV32E40PExtendedAST CV32E40PAddiDecoder CV32E40PAddiForwardControl
 CV32E40PAddiDecoderPhase CV32E40PAddiOperandCone CV32E40PAddiIDEXAccept
 CV32E40PFetchFIFOCount CV32E40PReq39Trace CV32E40PAddiReachability
 CV32E40PInternalBits CV32E40PClockBoundary CV32E40PRequestReachable.
Local Open Scope Z_scope.
Module CV32E40PGatedEdge.
 #[local] Opaque norm read_signal write_signal.
 Lemma high_latch_process s : norm 1 (read_signal s 310%nat) = 1 ->
   run_process cv32e40p_program s process_1500 = s.
 Proof.
   intros H. unfold run_process. change (statement_fuel cv32e40p_program) with 512%nat.
   cbn [process_1500 process_body]. rewrite exec_sequence, fold_one, exec_sequence, fold_one, exec_if.
   cbn [eval_expr blocking_state]. rewrite H. change (norm 1 (Z.lnot 1)) with 0.
   reflexivity.
 Qed.
 #[local] Opaque run_process comb_round before_process.
 Lemma high_round_latch s : norm 1 (read_signal s 7%nat) = 1 ->
   read_signal (round s) 314%nat = read_signal s 314%nat.
 Proof.
   intros H. unfold round.
   rewrite (comb_cut_root cv32e40p_program 1500 process_1500 s 314%nat eq_refl eq_refl ltac:(vm_compute; reflexivity)).
   rewrite high_latch_process.
   - apply before_process_keeps_root. vm_compute; reflexivity.
   - rewrite <- (cut_final_root cv32e40p_program 1500 s 310%nat ltac:(vm_compute; reflexivity)).
     now rewrite round_input_clock.
 Qed.
 Lemma iter_observe p (P : State -> Prop) (f : State -> Z) :
   (forall s, P s -> P (comb_round p s)) ->
   (forall s, P s -> f (comb_round p s) = f s) ->
   forall n s, P s -> f (comb_iter p n s) = f s.
 Proof.
   intros HP HF n s. induction n in s |- *; [reflexivity|].
   intros H. cbn [comb_iter]. rewrite IHn by now apply HP. now apply HF.
 Qed.
 Lemma high_iter_latch n s : norm 1 (read_signal s 7%nat) = 1 ->
   read_signal (comb_iter cv32e40p_program n s) 314%nat = read_signal s 314%nat.
 Proof.
   apply (iter_observe cv32e40p_program (fun s => norm 1 (read_signal s 7%nat) = 1)
     (fun s => read_signal s 314%nat)).
   - intros t H. rewrite comb_round_preserves_unwritten_root by (vm_compute; reflexivity). exact H.
   - exact high_round_latch.
 Qed.
 Lemma high_sample_latch s : norm 1 (read_signal s 7%nat) = 1 ->
   read_signal (cut 1501 s) 314%nat = read_signal s 314%nat.
 Proof.
   intros H. unfold cut. rewrite <- (cut_final_root cv32e40p_program 1501 s 314%nat ltac:(vm_compute; reflexivity)).
   now apply high_round_latch.
 Qed.
 Lemma rising_clock_lowbit pre :
   norm 1 (read_signal (phase_driven_state cv32e40p_program clk_rise pre) 418%nat) =
   norm 1 (read_signal pre 314%nat).
 Proof.
   rewrite phase_driven_last_round, round_gate.
   assert (H : norm 1 (read_signal (comb_iter cv32e40p_program 7
     (write_signal pre (changed_signal clk_rise) (new_value clk_rise))) 7%nat) = 1).
   { rewrite comb_iter_preserves_unwritten_root by (vm_compute; reflexivity).
     rewrite read_signal_write_same. reflexivity. }
   rewrite H, high_sample_latch by exact H.
   rewrite high_iter_latch by (rewrite read_signal_write_same; reflexivity).
   rewrite read_signal_write_other by discriminate.
   destruct (bit_cases (read_signal pre 314%nat)) as [Hb|Hb]; rewrite Hb; reflexivity.
 Qed.
 #[local] Opaque phase_driven_state environment_state_image.
 Lemma reachable_rising_clock image s : ResetReachable image s ->
   read_signal (phase_driven_state cv32e40p_program clk_rise (environment_state_image image (physical_state s))) 418%nat =
   norm 1 (read_signal (environment_state_image image (physical_state s)) 314%nat).
 Proof.
   intros Hr.
   assert (Hb : BitRoot 418%nat (phase_driven_state cv32e40p_program clk_rise
     (environment_state_image image (physical_state s)))).
   { rewrite phase_driven_last_round. apply round_bit; [exact (proj1 prefetch_clock_internal)|].
     apply iter_bit; [exact (proj1 prefetch_clock_internal)|]. unfold BitRoot.
     rewrite read_signal_write_other by discriminate.
     apply environment_bit; [exact prefetch_clock_internal|].
     exact (reachable_internal_bit 418%nat image s prefetch_clock_internal Hr). }
   unfold BitRoot in Hb. rewrite <- (bit_normalized _ Hb). apply rising_clock_lowbit.
 Qed.
 Theorem reachable_event_iff_gate image s : ResetReachable image s ->
   let pre := environment_state_image image (physical_state s) in
   process_matches_states pre (phase_driven_state cv32e40p_program clk_rise pre) process_12 =
   (norm 1 (read_signal pre 314%nat) =? 1).
 Proof.
   intros Hr. cbv zeta. rewrite (reachable_prefetch_edge image s Hr), (reachable_rising_clock image s Hr).
   destruct (bit_cases (read_signal (environment_state_image image (physical_state s)) 314%nat)) as [Hb|Hb];
     rewrite Hb; reflexivity.
 Qed.
 Theorem reachable_gated_request_balance image s : ResetReachable image s ->
   let pre := environment_state_image image (physical_state s) in
   let driven := phase_driven_state cv32e40p_program clk_rise pre in
   norm 2 (read_signal (PhaseSemantics cv32e40p_program clk_rise pre) 440%nat) =
   if norm 1 (read_signal pre 314%nat) =? 1 then
     norm 2 (norm 2 (read_signal pre 440%nat) + norm 1 (read_signal driven 426%nat)
       - pending_count (physical_state s))
   else norm 2 (read_signal pre 440%nat).
 Proof.
   intros Hr. cbv zeta. rewrite (reachable_rise_balance image s Hr), (reachable_event_iff_gate image s Hr).
   reflexivity.
 Qed.
 Example masked_clock_is_not_raw_clock : norm 1 2 = 0 /\
   edge_fires Posedge 2 1 = false /\ edge_fires Posedge 0 1 = true.
 Proof. repeat split; reflexivity. Qed.
 Example bit_checker_rejects_wide_write : bit_writesb 0%nat (SAssign false (EConst 2 2) (LVar 2 0%nat)) = false.
 Proof. reflexivity. Qed.
 Print Assumptions reachable_event_iff_gate.
 Print Assumptions reachable_gated_request_balance.
End CV32E40PGatedEdge.
