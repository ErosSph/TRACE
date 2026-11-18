(** Original ordered RTL wiring from persistent ID/EX operands to the ALU cut. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVCombCut
 Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiIDEXHold
 Ex.External.CV32E40PAddiOperandCone Ex.External.CV32E40PAddiWritebackCone
 Ex.External.CV32E40PReq39Trace Ex.External.CV32E40PReq40RootProjection.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVCombCut
 CV32E40PExtendedAST CV32E40PAddiIDEXHold CV32E40PAddiOperandCone CV32E40PAddiWritebackCone
 CV32E40PReq39Trace CV32E40PReq40RootProjection.
Module CV32E40PAddiEXOperandWiring.
 #[local] Opaque before_process comb_round run_process read_signal.
 Ltac port n proc dst :=
   rewrite (comb_cut_root cv32e40p_program n proc _ dst eq_refl eq_refl ltac:(vm_compute; reflexivity));
   rewrite (wire _ proc _ dst eq_refl).
 Ltac final_src n root :=
   rewrite <- (cut_final_root cv32e40p_program n _ root ltac:(vm_compute; reflexivity)).
 Lemma round_alu_a s : norm 32 (read_signal (comb_round cv32e40p_program s) 1304%nat) =
   norm 32 (read_signal s 589%nat).
 Proof.
   port 421%nat process_421 1304%nat. final_src 421%nat 1195%nat.
   port 420%nat process_420 1195%nat. final_src 420%nat 137%nat.
   port 251%nat process_251 137%nat.
   rewrite before_process_keeps_root by (vm_compute; reflexivity). reflexivity.
 Qed.
 Lemma round_alu_b s : norm 32 (read_signal (comb_round cv32e40p_program s) 1305%nat) =
   norm 32 (read_signal s 590%nat).
 Proof.
   port 559%nat process_559 1305%nat. final_src 559%nat 1196%nat.
   port 558%nat process_558 1196%nat. final_src 558%nat 138%nat.
   port 253%nat process_253 138%nat.
   rewrite before_process_keeps_root by (vm_compute; reflexivity). reflexivity.
 Qed.
 Theorem alu_cut_operands s :
   norm 32 (read_signal (cut 621 s) 1304%nat) = norm 32 (read_signal s 589%nat) /\
   norm 32 (read_signal (cut 621 s) 1305%nat) = norm 32 (read_signal s 590%nat).
 Proof.
   unfold cut. split;
     rewrite <- cut_final_root by (vm_compute; reflexivity).
   - apply round_alu_a.
   - apply round_alu_b.
 Qed.
 Theorem phase_alu_operands ev pre : changed_signal ev <> 589%nat -> changed_signal ev <> 590%nat ->
   norm 32 (read_signal (cut 621 (phase_round4 ev pre)) 1304%nat) = norm 32 (read_signal pre 589%nat) /\
   norm 32 (read_signal (cut 621 (phase_round4 ev pre)) 1305%nat) = norm 32 (read_signal pre 590%nat).
 Proof.
   intros Ha Hb. destruct (alu_cut_operands (phase_round4 ev pre)) as [A B].
   rewrite A, B. unfold phase_round4.
   rewrite !comb_iter_preserves_unwritten_root by (apply idex_comb_unwritten; cbn [idex_roots In]; auto).
   rewrite !read_signal_write_other by assumption. split; reflexivity.
 Qed.
 Print Assumptions phase_alu_operands.
 Theorem environment_keeps_idex image s root : In root idex_roots ->
   read_signal (environment_state_image image s) root = read_signal (trace_rtl s) root.
 Proof.
   intros Hr. unfold environment_state_image, obi_ports_image.
   rewrite lfp_candidate_preserves_unwritten_root by (now apply idex_comb_unwritten).
   apply drive_preserves_root.
   cbn [idex_roots In] in Hr.
   repeat constructor; cbn; intuition congruence.
 Qed.
End CV32E40PAddiEXOperandWiring.
