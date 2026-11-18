(** Counter conservation specialized to the original reset-reachable environment.
    No assertion about ISA address order is built into reachability. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVCombCut
 Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PReq39Trace
 Ex.External.CV32E40PAddiReachability Ex.External.CV32E40PAddiResetReleaseInvariant
 Ex.External.CV32E40PAddiDecoder Ex.External.CV32E40PAddiIDEXAccept
 Ex.External.CV32E40PAddiDecoderPhase Ex.External.CV32E40PAddiOperandCone Ex.External.CV32E40PFetchFIFOCount
 Ex.External.CV32E40PRequestCount Ex.External.CV32E40PRequestWiring
 Ex.External.CV32E40POBIAdapter Ex.External.CV32E40POBIReachable.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVCombCut
 CV32E40PExtendedAST CV32E40PReq39Trace CV32E40PAddiReachability
 CV32E40PAddiResetReleaseInvariant CV32E40PAddiDecoder CV32E40PAddiIDEXAccept
 CV32E40PAddiDecoderPhase CV32E40PAddiOperandCone CV32E40PFetchFIFOCount CV32E40PRequestCount
 CV32E40PRequestWiring CV32E40POBIAdapter CV32E40POBIReachable.
Local Open Scope Z_scope.
Module CV32E40PRequestReachable.
 #[local] Opaque norm read_signal phase_driven_state comb_iter comb_round before_process.
 Lemma controller_reset s : norm 1 (read_signal (round s) 419%nat) = norm 1 (read_signal s 8%nat).
 Proof.
   rewrite (wire 1126 process_1126 382%nat 419%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   rewrite (wire 1125 process_1125 321%nat 382%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   rewrite (wire 1124 process_1124 57%nat 321%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   rewrite (wire 1122 process_1122 8%nat 57%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   unfold round. rewrite comb_round_preserves_unwritten_root by exact reset_comb_unwritten. reflexivity.
 Qed.
 Lemma phase_acceptance ev pre : changed_signal ev <> 505%nat ->
   norm 1 (read_signal pre 505%nat) = 0 ->
   norm 1 (read_signal (counter_sample ev pre) 442%nat) =
   norm 1 (read_signal (phase_driven_state cv32e40p_program ev pre) 426%nat).
 Proof.
   intros He Hs. unfold counter_sample. rewrite acceptance_wiring.
   rewrite comb_iter_preserves_unwritten_root by exact state_unwritten.
   rewrite read_signal_write_other by exact He. rewrite Hs.
   rewrite phase_driven_last_round. change (0 =? 0) with true. cbn beta iota zeta.
   unfold round.
   destruct (bit_cases (read_signal
     (comb_round cv32e40p_program (comb_iter cv32e40p_program 7 (write_signal pre (changed_signal ev) (new_value ev)))) 426%nat))
     as [Hb|Hb]; rewrite Hb; reflexivity.
 Qed.
 Definition pending_count (s : TraceState) : Z :=
   match trace_instruction_pending s with Some _ => 1 | None => 0 end.
 Lemma environment_response image s :
   norm 1 (read_signal (environment_state_image image s) 18%nat) = pending_count s.
 Proof.
   unfold environment_state_image, obi_ports_image.
   rewrite lfp_candidate_preserves_unwritten_root by (vm_compute; reflexivity).
   unfold drive. cbn [fold_left fst snd].
   repeat rewrite read_signal_write_other by discriminate.
   rewrite read_signal_write_same.
   unfold pending_count. destruct (trace_instruction_pending s); reflexivity.
 Qed.
 #[local] Opaque PhaseSemantics environment_state_image counter_sample process_matches_states.
 Theorem reachable_rise_balance image s : ResetReachable image s ->
   let pre := environment_state_image image (physical_state s) in
   let driven := phase_driven_state cv32e40p_program clk_rise pre in
   norm 2 (read_signal (PhaseSemantics cv32e40p_program clk_rise pre) 440%nat) =
   if process_matches_states pre driven process_12 then
     norm 2 (norm 2 (read_signal pre 440%nat) +
       norm 1 (read_signal driven 426%nat) - pending_count (physical_state s))
   else norm 2 (read_signal pre 440%nat).
 Proof.
   intros Hr. cbv zeta.
   assert (Hempty : norm 1 (read_signal (environment_state_image image (physical_state s)) 505%nat) = 0).
   { rewrite environment_adapter. exact (reachable_adapter_empty image s Hr). }
   rewrite phase_transaction_balance by discriminate.
   rewrite (phase_acceptance clk_rise (environment_state_image image (physical_state s)) ltac:(discriminate) Hempty).
   rewrite (sampled_response clk_rise (environment_state_image image (physical_state s))).
   rewrite (read_signal_write_other (environment_state_image image (physical_state s))
     (changed_signal clk_rise) 18%nat (new_value clk_rise)) by discriminate.
   rewrite environment_response.
   assert (Hreset : norm 1 (read_signal (phase_driven_state cv32e40p_program clk_rise
     (environment_state_image image (physical_state s))) 419%nat) = 1).
   { rewrite phase_driven_last_round, controller_reset.
     rewrite comb_iter_preserves_unwritten_root by exact reset_comb_unwritten.
     rewrite read_signal_write_other by discriminate.
     rewrite environment_keeps_reset, (reachable_reset_stays_released image s Hr). reflexivity. }
   rewrite Hreset. reflexivity.
 Qed.
 Print Assumptions reachable_rise_balance.
End CV32E40PRequestReachable.
