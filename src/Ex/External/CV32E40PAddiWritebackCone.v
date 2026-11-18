(** Original ordered FullCore ALU -> EX -> forwarding -> RF-data connection.
    Rounds below are combinational rounds, NOT clock cycles. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVCombCut
  Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiAdderInputs
  Ex.External.CV32E40PAddiOperandCone Ex.External.CV32E40PAddiWritebackMux.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVCombCut
  CV32E40PExtendedAST CV32E40PAddiAdderInputs CV32E40PAddiOperandCone
  CV32E40PAddiWritebackMux CV32E40PAddiIDEXAccept.CV32E40PAddiIDEXAccept.
Local Open Scope Z_scope.
Module CV32E40PAddiWritebackCone.
  Lemma suffix_rf : avoids_root 897%nat (filter is_comb (skipn 1681 (processes cv32e40p_program))) = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma prefix_fw : avoids_root 695%nat (filter is_comb (firstn 1680 (processes cv32e40p_program))) = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma suffix_fw : avoids_root 695%nat (filter is_comb (skipn 1787 (processes cv32e40p_program))) = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma prefix_ex : avoids_root 195%nat (filter is_comb (firstn 1786 (processes cv32e40p_program))) = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma suffix_ex : avoids_root 195%nat (filter is_comb (skipn 1979 (processes cv32e40p_program))) = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma suffix_mux : avoids_root 1269%nat (filter is_comb (skipn 1790 (processes cv32e40p_program))) = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma suffix_mux_at_wire : avoids_root 1269%nat (filter is_comb (skipn 1978 (processes cv32e40p_program))) = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma prefix_alu_wire : avoids_root 1278%nat (filter is_comb (firstn 1789 (processes cv32e40p_program))) = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma suffix_alu_wire : avoids_root 1278%nat (filter is_comb (skipn 1950 (processes cv32e40p_program))) = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma suffix_alu_result : avoids_root 1314%nat (filter is_comb (skipn 1949 (processes cv32e40p_program))) = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma wire s proc src dst : process_body proc = SAssign false (EVar 32 src) (LVar 32 dst) ->
    norm 32 (read_signal (run_process cv32e40p_program s proc) dst) = norm 32 (read_signal s src).
  Proof. intros H. rewrite (assign_value s proc 32 dst (EVar 32 src) H). cbn [eval_expr]. apply norm_twice. Qed.
  Definition ALUSelected s :=
    norm 1 (read_signal (cut 1789 s) 1198%nat) = 1 /\
    norm 1 (read_signal (cut 1789 s) 1210%nat) = 0 /\
    norm 1 (read_signal (cut 1789 s) 1260%nat) = 0.
  #[local] Opaque before_process comb_round run_process.
  Theorem round_rf_port s : norm 32 (read_signal (round s) 897%nat) = norm 32 (read_signal s 695%nat).
  Proof.
    unfold round. rewrite (comb_cut_root cv32e40p_program 1680 process_1680 s 897%nat eq_refl eq_refl suffix_rf).
    rewrite (wire _ process_1680 695%nat 897%nat eq_refl).
    rewrite before_process_keeps_root by exact prefix_fw. reflexivity.
  Qed.
  Theorem round_forward s : norm 32 (read_signal (round s) 695%nat) = norm 32 (read_signal s 195%nat).
  Proof.
    unfold round. rewrite (comb_cut_root cv32e40p_program 1786 process_1786 s 695%nat eq_refl eq_refl suffix_fw).
    rewrite (wire _ process_1786 195%nat 695%nat eq_refl).
    rewrite before_process_keeps_root by exact prefix_ex. reflexivity.
  Qed.
  Theorem round_ex_alu s : ALUSelected s ->
    norm 32 (read_signal (round s) 195%nat) = norm 32 (read_signal s 1278%nat).
  Proof.
    intros (Ha&Hm&Hc). unfold round.
    rewrite (comb_cut_root cv32e40p_program 1978 process_1978 s 195%nat eq_refl eq_refl suffix_ex).
    rewrite (wire _ process_1978 1269%nat 195%nat eq_refl).
    rewrite <- (cut_final_root cv32e40p_program 1978 s 1269%nat suffix_mux_at_wire).
    rewrite (comb_cut_root cv32e40p_program 1789 process_1789 s 1269%nat eq_refl eq_refl suffix_mux).
    rewrite actual_ex_alu_value by assumption.
    rewrite before_process_keeps_root by exact prefix_alu_wire. reflexivity.
  Qed.
  Theorem round_alu_wire s : norm 32 (read_signal (round s) 1278%nat) = norm 32 (read_signal (round s) 1314%nat).
  Proof.
    unfold round. rewrite (comb_cut_root cv32e40p_program 1949 process_1949 s 1278%nat eq_refl eq_refl suffix_alu_wire).
    rewrite (wire _ process_1949 1314%nat 1278%nat eq_refl).
    rewrite <- (cut_final_root cv32e40p_program 1949 s 1314%nat suffix_alu_result). reflexivity.
  Qed.
  Theorem four_rounds_alu_to_rf s : ALUSelected (round s) ->
    norm 32 (read_signal (round (round (round (round s)))) 897%nat) =
    norm 32 (read_signal (round s) 1314%nat).
  Proof. intros H. rewrite round_rf_port, round_forward, round_ex_alu by exact H. apply round_alu_wire. Qed.
  Definition phase_round4 ev pre := comb_iter cv32e40p_program 4
    (write_signal pre (changed_signal ev) (new_value ev)).
  Definition sampled_alu ev pre := norm 32 (read_signal (round (phase_round4 ev pre)) 1314%nat).
  Lemma driven_four_rounds ev pre : phase_driven_state cv32e40p_program ev pre =
    round (round (round (round (phase_round4 ev pre)))).
  Proof. reflexivity. Qed.
  #[local] Opaque phase_driven_state lfp_candidate.
  Theorem phase_rf_data_from_actual_alu ev pre : ALUSelected (round (phase_round4 ev pre)) ->
    norm 32 (read_signal (phase_driven_state cv32e40p_program ev pre) 897%nat) = sampled_alu ev pre.
  Proof. intros H. rewrite driven_four_rounds. exact (four_rounds_alu_to_rf (phase_round4 ev pre) H). Qed.
  Print Assumptions phase_rf_data_from_actual_alu.
End CV32E40PAddiWritebackCone.
