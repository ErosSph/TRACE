(** Connect the actual masked FIFO occupancy to both request sampling boundaries. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection
 Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiOperandCone
 Ex.External.CV32E40PAddiDecoderPhase Ex.External.CV32E40PFetchFIFOInvariant
 Ex.External.CV32E40PRequestOccupancy Ex.External.CV32E40PRequestCone
 Ex.External.CV32E40PRequestOutput Ex.External.CV32E40PRequestCycleBalance
 Ex.External.CV32E40PReq39Trace Ex.External.CV32E40PAddiReachability.
Import ListNotations ExtendedSV ExtendedSVRootProjection CV32E40PExtendedAST
 CV32E40PAddiOperandCone CV32E40PAddiDecoderPhase CV32E40PFetchFIFOInvariant
 CV32E40PRequestOccupancy CV32E40PRequestCone CV32E40PRequestOutput
 CV32E40PRequestCycleBalance CV32E40PReq39Trace CV32E40PAddiReachability.
Local Open Scope Z_scope.
Module CV32E40PRequestOccupancyConnection.
 Definition FifoCount s := norm 2 (read_signal (trace_rtl (physical_state s)) 479%nat).
 Definition internal_mask_input image s := comb_iter cv32e40p_program 6
   (write_signal (environment_state_image image (physical_state s)) 7%nat 1).
 Definition external_mask_input image s := comb_iter cv32e40p_program 4
   (environment_input image (physical_state s)).
 #[local] Opaque norm read_signal comb_iter comb_round.
 Lemma input_frame image s root : root = 479%nat \/ root = 1054%nat ->
   read_signal (environment_input image s) root = read_signal (trace_rtl s) root.
 Proof.
   intros [H | H]; subst root; unfold environment_input, drive; cbn [fold_left fst snd];
     repeat rewrite read_signal_write_other by discriminate; reflexivity.
 Qed.
 Lemma environment_fifo image s : read_signal (environment_state_image image s) 479%nat =
   read_signal (trace_rtl s) 479%nat.
 Proof.
   rewrite environment_shape, lfp_candidate_preserves_unwritten_root by exact count_comb_unwritten.
   apply input_frame; auto.
 Qed.
 #[local] Opaque environment_state_image environment_input.
 Theorem internal_occupancy image s : ResetReachable image s ->
   norm 2 (read_signal (internal_boundary image s) 450%nat) =
   if norm 1 (read_signal (internal_mask_input image s) 421%nat) =? 0 then FifoCount s else 0.
 Proof.
   intros Hr. unfold internal_boundary. rewrite (comb_iter_last _ 6). fold (internal_mask_input image s). fold round.
   rewrite round_masked_occupancy.
   - unfold internal_mask_input.
     rewrite (comb_iter_preserves_unwritten_root cv32e40p_program 479%nat) by exact count_comb_unwritten.
     rewrite (read_signal_write_other _ 7%nat 479%nat) by discriminate.
     rewrite environment_fifo. reflexivity.
   - unfold internal_mask_input.
     rewrite (comb_iter_preserves_unwritten_root cv32e40p_program 1054%nat) by exact hwlp_unwritten.
     rewrite (read_signal_write_other _ 7%nat 1054%nat) by discriminate.
     rewrite environment_hwlp. exact (reachable_hwlp_disabled image s Hr).
 Qed.
 Theorem external_occupancy image s : ResetReachable image s ->
   norm 2 (read_signal (external_boundary image s) 450%nat) =
   if norm 1 (read_signal (external_mask_input image s) 421%nat) =? 0 then FifoCount s else 0.
 Proof.
   intros Hr. unfold external_boundary. rewrite (comb_iter_last _ 4). fold (external_mask_input image s). fold round.
   rewrite round_masked_occupancy.
   - unfold external_mask_input.
     rewrite (comb_iter_preserves_unwritten_root cv32e40p_program 479%nat) by exact count_comb_unwritten.
     rewrite input_frame by auto. reflexivity.
   - unfold external_mask_input.
     rewrite (comb_iter_preserves_unwritten_root cv32e40p_program 1054%nat) by exact hwlp_unwritten.
     rewrite input_frame by auto. exact (reachable_hwlp_disabled image s Hr).
 Qed.
 Lemma zero_masks (a b : bool) : (if a then 0 else 0) = (if b then 0 else 0).
 Proof. destruct a, b; reflexivity. Qed.
 Lemma masks_equal_iff c (a b : bool) :
   ((if a then c else 0) = (if b then c else 0) <-> c = 0 \/ a = b).
 Proof. destruct a, b; intuition congruence. Qed.
 #[local] Opaque internal_boundary external_boundary internal_mask_input external_mask_input FifoCount.
 Theorem reachable_empty_fifo_occupancy_stable image s : ResetReachable image s -> FifoCount s = 0 ->
   norm 2 (read_signal (internal_boundary image s) 450%nat) =
   norm 2 (read_signal (external_boundary image s) 450%nat).
 Proof.
   intros Hr Hf. rewrite internal_occupancy, external_occupancy by exact Hr. rewrite Hf.
   apply zero_masks.
 Qed.
 Theorem reachable_occupancy_stable_iff image s : ResetReachable image s ->
   (norm 2 (read_signal (internal_boundary image s) 450%nat) =
    norm 2 (read_signal (external_boundary image s) 450%nat) <->
    FifoCount s = 0 \/
    (norm 1 (read_signal (internal_mask_input image s) 421%nat) =? 0) =
    (norm 1 (read_signal (external_mask_input image s) 421%nat) =? 0)).
 Proof.
   intros Hr. rewrite internal_occupancy, external_occupancy by exact Hr.
   apply masks_equal_iff.
 Qed.
 Theorem empty_fifo_request_alignment image s : ResetReachable image s -> FifoCount s = 0 ->
   norm 1 (read_signal (internal_boundary image s) 420%nat) =
   norm 1 (read_signal (external_boundary image s) 420%nat) ->
   InternalRequest image s = ExternalRequest image s.
 Proof.
   intros Hr HF He. apply request_alignment_from_two_fields; [exact He|].
   now apply reachable_empty_fifo_occupancy_stable.
 Qed.
 Print Assumptions reachable_empty_fifo_occupancy_stable.
 Print Assumptions reachable_occupancy_stable_iff.
End CV32E40PRequestOccupancyConnection.
