(** Actual OBI response and acceptance wiring at the counter evaluation cut. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVBlocking Lang.ExtendedSVRootProjection
 Lang.ExtendedSVProcessSlice Lang.ExtendedSVCombCut Ex.Generated.CV32E40PExtendedAST
 Ex.External.CV32E40PFetchFIFOCount Ex.External.CV32E40PAddiDecoder
 Ex.External.CV32E40PAddiForwardControl Ex.External.CV32E40PAddiOperands
 Ex.External.CV32E40PAddiIDEXAccept Ex.External.CV32E40PAddiOperandCone
 Ex.External.CV32E40PAddiDecoderPhase
 Ex.External.CV32E40PRequestCount Ex.External.CV32E40PAddiAdderInputs.
Import ListNotations ExtendedSV ExtendedSVBlocking ExtendedSVRootProjection
 ExtendedSVProcessSlice ExtendedSVCombCut CV32E40PExtendedAST
 CV32E40PAddiDecoder CV32E40PAddiForwardControl CV32E40PAddiOperands
 CV32E40PAddiIDEXAccept CV32E40PAddiOperandCone CV32E40PAddiDecoderPhase
 CV32E40PAddiAdderInputs CV32E40PFetchFIFOCount CV32E40PRequestCount.
Local Open Scope Z_scope.
Module CV32E40PRequestWiring.
 #[local] Opaque norm read_signal run_process before_process comb_round.
 Lemma wire n proc src dst s :
   nth_error (processes cv32e40p_program) n = Some proc ->
   is_comb proc = true ->
   process_body proc = SAssign false (EVar 1 src) (LVar 1 dst) ->
   avoids_root dst (filter is_comb (skipn (S n) (processes cv32e40p_program))) = true ->
   avoids_root src (filter is_comb (skipn n (processes cv32e40p_program))) = true ->
   norm 1 (read_signal (round s) dst) = norm 1 (read_signal (round s) src).
 Proof.
   intros Hn Hc Hb Hd Hs. unfold round.
   rewrite (comb_cut_root cv32e40p_program n proc s dst Hn Hc Hd),
     (assign_value _ proc 1 dst (EVar 1 src) Hb).
   cbn [eval_expr]. rewrite norm_twice.
   now rewrite <- (cut_final_root cv32e40p_program n s src Hs).
 Qed.
 Lemma response_wiring s : norm 1 (read_signal (cut 1555 s) 443%nat) =
   norm 1 (read_signal s 18%nat).
 Proof.
   unfold cut. rewrite <- (cut_final_root cv32e40p_program 1555 s 443%nat ltac:(vm_compute; reflexivity)).
   change (comb_round cv32e40p_program s) with (round s).
   rewrite (wire 1248 process_1248 429%nat 443%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   rewrite (wire 1247 process_1247 411%nat 429%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   rewrite (wire 1246 process_1246 492%nat 411%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   rewrite (wire 1245 process_1245 503%nat 492%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   rewrite (wire 1244 process_1244 395%nat 503%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   rewrite (wire 1243 process_1243 332%nat 395%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   rewrite (wire 1242 process_1242 67%nat 332%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   rewrite (wire 1241 process_1241 18%nat 67%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   unfold round. rewrite comb_round_preserves_unwritten_root by (vm_compute; reflexivity). reflexivity.
 Qed.
 Lemma grant_wiring s : norm 1 (read_signal (round s) 496%nat) = norm 1 (read_signal s 17%nat).
 Proof.
   rewrite (wire 1240 process_1240 392%nat 496%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   rewrite (wire 1239 process_1239 331%nat 392%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   rewrite (wire 1238 process_1238 281%nat 331%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   rewrite (wire 1237 process_1237 66%nat 281%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   rewrite (wire 1236 process_1236 17%nat 66%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   unfold round. rewrite comb_round_preserves_unwritten_root by (vm_compute; reflexivity). reflexivity.
 Qed.
 Lemma ready_wiring s : norm 1 (read_signal (round s) 427%nat) =
   if norm 1 (read_signal s 505%nat) =? 0 then 1 else 0.
 Proof.
   rewrite (wire 169 process_169 402%nat 427%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)),
     (wire 168 process_168 486%nat 402%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   unfold round. rewrite (comb_cut_root cv32e40p_program 167 process_167 s 486%nat eq_refl eq_refl ltac:(vm_compute; reflexivity)),
     (assign_value _ process_167 1 486%nat (rhs process_167) eq_refl).
   unfold rhs. cbn [process_167 process_body eval_expr].
   rewrite before_process_keeps_root by (vm_compute; reflexivity).
   destruct (bit_cases (read_signal s 505%nat)) as [Hs|Hs]; rewrite Hs; reflexivity.
 Qed.
 Lemma acceptance_wiring s : norm 1 (read_signal (cut 1555 s) 442%nat) =
   norm 1 (Z.land (norm 1 (read_signal (round s) 426%nat))
     (if norm 1 (read_signal s 505%nat) =? 0 then 1 else 0)).
 Proof.
   unfold cut. rewrite <- (cut_final_root cv32e40p_program 1555 s 442%nat ltac:(vm_compute; reflexivity)).
   rewrite (comb_cut_root cv32e40p_program 1554 process_1554 s 442%nat eq_refl eq_refl ltac:(vm_compute; reflexivity)),
     (assign_value _ process_1554 1 442%nat (rhs process_1554) eq_refl).
   unfold rhs. cbn [process_1554 process_body eval_expr]. rewrite norm_twice.
   rewrite <- (cut_final_root cv32e40p_program 1554 s 426%nat ltac:(vm_compute; reflexivity)),
     <- (cut_final_root cv32e40p_program 1554 s 427%nat ltac:(vm_compute; reflexivity)).
   rewrite ready_wiring. reflexivity.
 Qed.
 #[local] Opaque comb_iter phase_driven_state.
 Theorem sampled_response ev pre :
   norm 1 (read_signal (counter_sample ev pre) 443%nat) =
   norm 1 (read_signal (write_signal pre (changed_signal ev) (new_value ev)) 18%nat).
 Proof.
   unfold counter_sample. rewrite response_wiring.
   rewrite comb_iter_preserves_unwritten_root by (vm_compute; reflexivity). reflexivity.
 Qed.
 Print Assumptions acceptance_wiring.
 Print Assumptions sampled_response.
End CV32E40PRequestWiring.
