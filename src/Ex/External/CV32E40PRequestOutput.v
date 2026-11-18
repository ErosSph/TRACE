(** Ordered external OBI request propagation; no comb fixed-point premise. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVBlocking Lang.ExtendedSVRootProjection Lang.ExtendedSVCombCut
 Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiOperands
 Ex.External.CV32E40PAddiAdderInputs Ex.External.CV32E40PAddiDecoder
 Ex.External.CV32E40PAddiForwardControl Ex.External.CV32E40PAddiOperandCone
 Ex.External.CV32E40PAddiIDEXAccept Ex.External.CV32E40PAddiDecoderPhase
 Ex.External.CV32E40PRequestWiring Ex.External.CV32E40PBusyCone
 Ex.External.CV32E40POBIAdapter Ex.External.CV32E40POBIReachable
 Ex.External.CV32E40PReq39Trace Ex.External.CV32E40PAddiReachability.
Import ListNotations ExtendedSV ExtendedSVBlocking ExtendedSVRootProjection ExtendedSVCombCut
 CV32E40PExtendedAST CV32E40PAddiOperands CV32E40PAddiAdderInputs CV32E40PAddiDecoder
 CV32E40PAddiForwardControl CV32E40PAddiOperandCone CV32E40PAddiIDEXAccept CV32E40PAddiDecoderPhase
 CV32E40PRequestWiring CV32E40PBusyCone CV32E40POBIAdapter CV32E40POBIReachable
 CV32E40PReq39Trace CV32E40PAddiReachability.
Local Open Scope Z_scope.
Import CV32E40PFetchFIFOCount.CV32E40PFetchFIFOCount.
Module CV32E40PRequestOutput.
 #[local] Opaque norm read_signal write_signal write_slice.
 Lemma adapter_request s :
   norm 1 (read_signal (run_process cv32e40p_program s process_1576) 495%nat) =
   if norm 1 (read_signal s 505%nat) =? 0 then norm 1 (read_signal s 485%nat) else 1.
 Proof.
   rewrite blocking_run_process by reflexivity.
   change (statement_fuel cv32e40p_program) with 512%nat.
   cbn [process_1576 process_body]. rewrite exec_sequence, fold_one, exec_sequence, fold_one, exec_if.
   cbn [eval_expr blocking_state]. destruct (norm 1 (read_signal s 505%nat) =? 0);
     straight; reflexivity.
 Qed.
 #[local] Opaque before_process comb_round run_process.
 Lemma round_adapter_request s :
   norm 1 (read_signal (round s) 280%nat) =
   if norm 1 (read_signal s 505%nat) =? 0 then norm 1 (read_signal s 485%nat) else 1.
 Proof.
   rewrite (wire 1609 process_1609 329%nat 280%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)),
     (wire 1588 process_1588 391%nat 329%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)),
     (wire 1579 process_1579 495%nat 391%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   unfold round. rewrite (comb_cut_root cv32e40p_program 1576 process_1576 s 495%nat
     eq_refl eq_refl ltac:(vm_compute; reflexivity)), adapter_request.
   rewrite (before_process_keeps_root cv32e40p_program 1576 s 505%nat ltac:(vm_compute; reflexivity)),
     (before_process_keeps_root cv32e40p_program 1576 s 485%nat ltac:(vm_compute; reflexivity)). reflexivity.
 Qed.
 Lemma round_external_request s : norm 1 (read_signal (round s) 16%nat) = norm 1 (read_signal s 280%nat).
 Proof.
   rewrite (wire 1997 process_1997 65%nat 16%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   apply (old_wire 1532 process_1532); try reflexivity; vm_compute; reflexivity.
 Qed.
 Lemma round_adapter_input s : norm 1 (read_signal (round s) 485%nat) = norm 1 (read_signal (round s) 426%nat).
 Proof.
   rewrite (wire 1577 process_1577 401%nat 485%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)),
     (wire 1563 process_1563 426%nat 401%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)). reflexivity.
 Qed.
 Theorem three_round_request s : norm 1 (read_signal s 505%nat) = 0 ->
   norm 1 (read_signal (round (round (round s))) 16%nat) = norm 1 (read_signal (round s) 426%nat).
 Proof.
   intros H. rewrite round_external_request, round_adapter_request, round_adapter_input.
   unfold round at 1. rewrite comb_round_preserves_unwritten_root by exact state_unwritten.
   rewrite H. reflexivity.
 Qed.
 Theorem lfp_request_history s : norm 1 (read_signal s 505%nat) = 0 ->
   norm 1 (read_signal (lfp_candidate cv32e40p_program s) 16%nat) =
   norm 1 (read_signal (comb_iter cv32e40p_program 6 s) 426%nat).
 Proof.
   intros H. unfold lfp_candidate. change (lfp_fuel cv32e40p_program) with 8%nat.
   rewrite (comb_iter_last _ 7), (comb_iter_last _ 6), (comb_iter_last _ 5).
   rewrite three_round_request.
   - reflexivity.
   - rewrite comb_iter_preserves_unwritten_root by exact state_unwritten. exact H.
 Qed.
 Definition environment_input image s :=
   drive (trace_rtl s) [((9%nat),1);((10%nat),0);((11%nat),0);((12%nat),0);((13%nat),0);
     ((14%nat),0);((15%nat),0);((17%nat),1);
     ((18%nat),match trace_instruction_pending s with Some _ => 1 | None => 0 end);
     ((20%nat),match trace_instruction_pending s with Some a => instruction_from_image image a | None => nop end);
     ((22%nat),1);((23%nat),match trace_data_pending s with Some _ => 1 | None => 0 end);
     ((28%nat),match trace_data_pending s with Some r => memory_read_word (trace_memory_word s) (obi_data_address r) | None => 0 end);
     ((29%nat),0);((32%nat),0);((36%nat),1)].
 Lemma environment_shape image s : environment_state_image image s = lfp_candidate cv32e40p_program (environment_input image s).
 Proof. reflexivity. Qed.
 Definition request_sample image s := comb_iter cv32e40p_program 6 (environment_input image s).
 Theorem reachable_request_history image s : ResetReachable image s ->
   norm 1 (read_signal (environment_state_image image (physical_state s)) 16%nat) =
   norm 1 (read_signal (request_sample image (physical_state s)) 426%nat).
 Proof.
   intros Hr. rewrite environment_shape. apply lfp_request_history.
   unfold environment_input, drive. cbn [fold_left fst snd].
   repeat rewrite read_signal_write_other by discriminate.
   exact (reachable_adapter_empty image s Hr).
 Qed.
 Print Assumptions reachable_request_history.
End CV32E40PRequestOutput.
