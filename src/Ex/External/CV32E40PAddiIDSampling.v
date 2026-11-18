(** Instruction/PC projection stability from settled environment to edge input.
    No full-CPU fixed-point hypothesis, and no restriction to concrete traces. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVCombCut
  Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiAdderInputs
  Ex.External.CV32E40PAddiOperandCone Ex.External.CV32E40PAddiDecoderPhase.
Import ExtendedSV ExtendedSVRootProjection ExtendedSVCombCut CV32E40PExtendedAST
  CV32E40PAddiAdderInputs CV32E40PAddiOperandCone CV32E40PAddiDecoderPhase
  CV32E40PAddiIDEXAccept.CV32E40PAddiIDEXAccept.
Local Open Scope Z_scope.
Module CV32E40PAddiIDSampling.
  Lemma instruction_q_unwritten : comb_root_unwrittenb cv32e40p_program 337%nat = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma pc_q_unwritten : comb_root_unwrittenb cv32e40p_program 341%nat = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma wire s proc src dst : process_body proc = SAssign false (EVar 32 src) (LVar 32 dst) ->
    norm 32 (read_signal (run_process cv32e40p_program s proc) dst) = norm 32 (read_signal s src).
  Proof. intros H. rewrite (assign_value s proc 32 dst (EVar 32 src) H). cbn [eval_expr]. apply norm_twice. Qed.
  #[local] Opaque comb_round before_process run_process.
  Lemma round_instruction_top s : norm 32 (read_signal (round s) 108%nat) = norm 32 (read_signal s 337%nat).
  Proof.
    unfold round. rewrite (comb_cut_root cv32e40p_program 186 process_186 s 108%nat
      eq_refl eq_refl ltac:(vm_compute; reflexivity)).
    rewrite (wire _ process_186 337%nat 108%nat eq_refl).
    rewrite before_process_keeps_root by (vm_compute; reflexivity). reflexivity.
  Qed.
  Lemma round_instruction_port s : norm 32 (read_signal (round s) 567%nat) = norm 32 (read_signal s 337%nat).
  Proof.
    unfold round. rewrite (comb_cut_root cv32e40p_program 221 process_221 s 567%nat
      eq_refl eq_refl ltac:(vm_compute; reflexivity)).
    rewrite (wire _ process_221 108%nat 567%nat eq_refl).
    rewrite <- (cut_final_root cv32e40p_program 221 s 108%nat ltac:(vm_compute; reflexivity)).
    apply round_instruction_top.
  Qed.
  Theorem round_instruction s : norm 32 (read_signal (round s) 718%nat) = norm 32 (read_signal s 337%nat).
  Proof.
    unfold round. rewrite (comb_cut_root cv32e40p_program 222 process_222 s 718%nat
      eq_refl eq_refl ltac:(vm_compute; reflexivity)).
    rewrite (wire _ process_222 567%nat 718%nat eq_refl).
    rewrite <- (cut_final_root cv32e40p_program 222 s 567%nat ltac:(vm_compute; reflexivity)).
    apply round_instruction_port.
  Qed.
  Theorem round_pc s : norm 32 (read_signal (round s) 121%nat) = norm 32 (read_signal s 341%nat).
  Proof.
    unfold round. rewrite (comb_cut_root cv32e40p_program 188 process_188 s 121%nat
      eq_refl eq_refl ltac:(vm_compute; reflexivity)).
    rewrite (wire _ process_188 341%nat 121%nat eq_refl).
    rewrite before_process_keeps_root by (vm_compute; reflexivity). reflexivity.
  Qed.
  Lemma iter_instruction n s : norm 32 (read_signal (comb_iter cv32e40p_program (S n) s) 718%nat) =
    norm 32 (read_signal s 337%nat).
  Proof.
    rewrite comb_iter_last. rewrite round_instruction.
    rewrite comb_iter_preserves_unwritten_root by exact instruction_q_unwritten. reflexivity.
  Qed.
  Lemma iter_pc n s : norm 32 (read_signal (comb_iter cv32e40p_program (S n) s) 121%nat) =
    norm 32 (read_signal s 341%nat).
  Proof.
    rewrite comb_iter_last. rewrite round_pc.
    rewrite comb_iter_preserves_unwritten_root by exact pc_q_unwritten. reflexivity.
  Qed.
  Lemma settled_instruction s : norm 32 (read_signal (lfp_candidate cv32e40p_program s) 718%nat) =
    norm 32 (read_signal s 337%nat).
  Proof. unfold lfp_candidate. change (lfp_fuel cv32e40p_program) with 8%nat. apply iter_instruction. Qed.
  Lemma settled_pc s : norm 32 (read_signal (lfp_candidate cv32e40p_program s) 121%nat) =
    norm 32 (read_signal s 341%nat).
  Proof. unfold lfp_candidate. change (lfp_fuel cv32e40p_program) with 8%nat. apply iter_pc. Qed.
  Theorem settled_to_edge_id_projection ev s :
    changed_signal ev <> 337%nat -> changed_signal ev <> 341%nat ->
    let env := lfp_candidate cv32e40p_program s in
    let edge := phase_driven_state cv32e40p_program ev env in
    norm 32 (read_signal edge 718%nat) = norm 32 (read_signal env 718%nat) /\
    norm 32 (read_signal edge 121%nat) = norm 32 (read_signal env 121%nat).
  Proof.
    intros Hi Hp. cbv beta zeta. unfold phase_driven_state. split.
    - rewrite !settled_instruction, read_signal_write_other by congruence.
      rewrite lfp_candidate_preserves_unwritten_root by exact instruction_q_unwritten. reflexivity.
    - rewrite !settled_pc, read_signal_write_other by congruence.
      rewrite lfp_candidate_preserves_unwritten_root by exact pc_q_unwritten. reflexivity.
  Qed.
  Print Assumptions settled_to_edge_id_projection.
End CV32E40PAddiIDSampling.
