(** Real FIFO occupancy and disabled-hardware-loop contribution to requests. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVCombCut
 Lang.ExtendedSVProcessSlice Ex.Generated.CV32E40PExtendedAST
 Ex.External.CV32E40PAddiOperands Ex.External.CV32E40PAddiAdderInputs
 Ex.External.CV32E40PAddiOperandCone Ex.External.CV32E40PAddiIDEXAccept
 Ex.External.CV32E40PAddiDecoderPhase Ex.External.CV32E40PFetchFIFOCount
 Ex.External.CV32E40PFetchFIFOInvariant Ex.External.CV32E40PRequestWiring
 Ex.External.CV32E40PRequestCone Ex.External.CV32E40PReq39Trace
 Ex.External.CV32E40PAddiReachability.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVCombCut ExtendedSVProcessSlice
 CV32E40PExtendedAST CV32E40PAddiOperands CV32E40PAddiAdderInputs
 CV32E40PAddiOperandCone CV32E40PAddiIDEXAccept CV32E40PAddiDecoderPhase
 CV32E40PFetchFIFOCount CV32E40PFetchFIFOInvariant CV32E40PRequestWiring
 CV32E40PRequestCone CV32E40PReq39Trace CV32E40PAddiReachability.
Local Open Scope Z_scope.
Module CV32E40PRequestOccupancy.
 #[local] Opaque norm read_signal run_process before_process comb_round.
 Lemma hwlp_unwritten : comb_root_unwrittenb cv32e40p_program 1054%nat = true.
 Proof. vm_compute; reflexivity. Qed.
 Lemma hwlp_writers : filter (writes_rootb 1054%nat) (processes cv32e40p_program) = [process_80].
 Proof. vm_compute; reflexivity. Qed.
 Lemma phase_hwlp ev s : changed_signal ev <> 1054%nat ->
   read_signal (PhaseSemantics cv32e40p_program ev s) 1054%nat = read_signal s 1054%nat.
 Proof.
   intros He. rewrite phase_root_projection by auto using hwlp_unwritten.
   unfold phase_update_chain, selected_on_transition.
   rewrite process_slice_sound, filter_swap, hwlp_writers. reflexivity.
 Qed.
 Lemma environment_hwlp image s :
   read_signal (environment_state_image image s) 1054%nat = read_signal (trace_rtl s) 1054%nat.
 Proof.
   unfold environment_state_image, obi_ports_image.
   rewrite lfp_candidate_preserves_unwritten_root by exact hwlp_unwritten.
   unfold drive. cbn [fold_left fst snd]. repeat rewrite read_signal_write_other by discriminate. reflexivity.
 Qed.
 #[local] Opaque PhaseSemantics lfp_candidate.
 Lemma cycle_hwlp image s : read_signal (trace_rtl (full_cycle_image image s)) 1054%nat =
   read_signal (trace_rtl s) 1054%nat.
 Proof.
   change (read_signal (settled_state_image image s) 1054%nat = read_signal (trace_rtl s) 1054%nat).
   unfold settled_state_image. rewrite lfp_candidate_preserves_unwritten_root by exact hwlp_unwritten.
   unfold falling_state_image, rising_state_image. repeat rewrite phase_hwlp by discriminate.
   apply environment_hwlp.
 Qed.
 Lemma reset_hwlp : read_signal (trace_rtl (physical_state reset_retirement)) 1054%nat = 0.
 Proof. vm_compute; reflexivity. Qed.
 Theorem reachable_hwlp_disabled image s : ResetReachable image s ->
   read_signal (trace_rtl (physical_state s)) 1054%nat = 0.
 Proof. intros H; induction H; [exact reset_hwlp|rewrite advance_physical, cycle_hwlp; exact IHResetReachable]. Qed.
 Lemma wire2 n proc src dst s :
   nth_error (processes cv32e40p_program) n = Some proc -> is_comb proc = true ->
   process_body proc = SAssign false (EVar 2 src) (LVar 2 dst) ->
   avoids_root dst (filter is_comb (skipn (S n) (processes cv32e40p_program))) = true ->
   avoids_root src (filter is_comb (skipn n (processes cv32e40p_program))) = true ->
   norm 2 (read_signal (round s) dst) = norm 2 (read_signal (round s) src).
 Proof.
   intros Hn Hc Hb Hd Hs. unfold round.
   rewrite (comb_cut_root cv32e40p_program n proc s dst Hn Hc Hd),
     (assign_value _ proc 2 dst (EVar 2 src) Hb).
   cbn [eval_expr]. rewrite norm_twice. now rewrite <- (cut_final_root cv32e40p_program n s src Hs).
 Qed.
 Lemma round_fifo_occupancy s : norm 2 (read_signal (round s) 436%nat) = norm 2 (read_signal s 479%nat).
 Proof.
   rewrite (wire2 166 process_166 406%nat 436%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)),
     (wire2 165 process_165 467%nat 406%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)),
     (wire2 157 process_157 479%nat 467%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   unfold round. rewrite comb_round_preserves_unwritten_root by exact count_comb_unwritten. reflexivity.
 Qed.
 Lemma round_hwlp_input s : norm 1 (read_signal (round s) 424%nat) = norm 1 (read_signal s 1054%nat).
 Proof.
   rewrite (wire 303 process_303 386%nat 424%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)),
     (wire 302 process_302 355%nat 386%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)),
     (wire 301 process_301 259%nat 355%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)),
     (wire 300 process_300 652%nat 259%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)),
     (wire 202 process_202 1054%nat 652%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   unfold round. rewrite comb_round_preserves_unwritten_root by exact hwlp_unwritten. reflexivity.
 Qed.
 Theorem round_masked_occupancy s : read_signal s 1054%nat = 0 ->
   norm 2 (read_signal (round s) 450%nat) =
   if norm 1 (read_signal s 421%nat) =? 0 then norm 2 (read_signal s 479%nat) else 0.
 Proof.
   intros H. unfold round at 1.
   rewrite (comb_cut_root cv32e40p_program 1550 process_1550 s 450%nat eq_refl eq_refl ltac:(vm_compute; reflexivity)),
     (assign_value _ process_1550 2 450%nat (rhs process_1550) eq_refl).
   unfold rhs. cbn [process_1550 process_body eval_expr].
   rewrite (before_process_keeps_root cv32e40p_program 1550 s 421%nat ltac:(vm_compute; reflexivity)),
     <- (cut_final_root cv32e40p_program 1550 s 424%nat ltac:(vm_compute; reflexivity)),
     <- (cut_final_root cv32e40p_program 1550 s 436%nat ltac:(vm_compute; reflexivity)).
   fold round. rewrite round_hwlp_input, round_fifo_occupancy, H.
   destruct (bit_cases (read_signal s 421%nat)) as [Hb|Hb]; rewrite Hb;
     change (norm 1 0) with 0; change (norm 1 (Z.lor 0 0)) with 0;
     change (norm 1 (Z.lor 1 0)) with 1; cbn [Z.eqb]; rewrite ?norm_twice; reflexivity.
 Qed.
 Print Assumptions reachable_hwlp_disabled.
 Print Assumptions round_masked_occupancy.
End CV32E40PRequestOccupancy.
