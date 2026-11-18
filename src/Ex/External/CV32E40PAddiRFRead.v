(** Actual integer RF read port, including instruction rs1 extraction.
    No expected RF read-data premise and no full CPU evaluation. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVCombCut Lang.ExtendedSVBitSlice
  Ex.Generated.CV32E40PExtendedAST Ex.Generated.CV32E40PGeneratedRFProcessPorts
  Ex.External.CV32E40PAddiAdderInputs
  Ex.External.CV32E40PAddiAdderBits Ex.External.CV32E40PAddiAdder
  Ex.External.CV32E40PAddiRFFields Ex.External.CV32E40PAddiOperandCone
  Ex.External.CV32E40PAddiIDEXAccept Ex.External.CV32E40PAddiDestination.
Import ExtendedSV ExtendedSVCombCut ExtendedSVBitSlice CV32E40PExtendedAST
  CV32E40PAddiAdderInputs CV32E40PAddiAdderBits CV32E40PAddiAdder
  CV32E40PAddiRFFields CV32E40PAddiOperandCone CV32E40PAddiIDEXAccept
  CV32E40PAddiDestination.
Local Open Scope Z_scope.
Module CV32E40PAddiRFRead.
  Definition instruction_rs1 ins := norm 5 (Z.shiftr (norm 32 ins) 15).
  Lemma actual_rs1 s : norm 1 (read_signal s 768%nat) = 0 ->
    norm 6 (read_signal (run_process cv32e40p_program s process_1394) 765%nat) =
      instruction_rs1 (read_signal s 718%nat).
  Proof.
    intros H. rewrite (assign_value s process_1394 6 765%nat (rhs process_1394) eq_refl).
    unfold rhs, instruction_rs1. cbn [process_1394 process_body eval_expr expr_width].
    rewrite H. change (norm 5 15) with 15.
    rewrite Z.shiftl_0_l, Z.lor_0_l, norm_twice. apply extend_rd.
  Qed.
  Lemma actual_read_port s r : (r < 32)%nat ->
    norm 6 (read_signal s 887%nat) = Z.of_nat r ->
    norm 32 (read_signal (run_process cv32e40p_program s process_1398) 888%nat) =
      rf_field (read_signal s 902%nat) r.
  Proof.
    intros Hr Haddr.
    rewrite (CV32E40PGeneratedRFProcessPorts.port_0_process s).
    unfold CV32E40PGeneratedRFPorts.port_0_rhs. cbn [eval_expr expr_width].
    rewrite Haddr.
    change (norm 3 5) with 5. change (norm 3 0) with 0.
    change (norm 32 5) with 5. change (norm 32 0) with 0.
    assert (Hhi : Z.shiftr (Z.of_nat r) 5 = 0).
    { rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. change (0 <= Z.of_nat r < 32). lia. }
    rewrite Hhi. change (norm 1 0 =? 0) with true.
    rewrite !Z.shiftr_0_r.
    assert (H5 : norm 5 (Z.of_nat r) = Z.of_nat r).
    { apply norm_small. change (0 <= Z.of_nat r < 32). lia. }
    assert (H32 : norm 32 (Z.of_nat r) = Z.of_nat r).
    { apply norm_small. change (0 <= Z.of_nat r < 4294967296). lia. }
    rewrite H5, H32, Z.shiftl_mul_pow2 by lia.
    replace (Z.of_nat r * 2^5) with (32 * Z.of_nat r) by ring.
    assert (Hoff : norm 32 (32 * Z.of_nat r) = 32 * Z.of_nat r).
    { apply norm_small. change (0 <= 32 * Z.of_nat r < 4294967296). lia. }
    rewrite Hoff, lane_offset_exact by exact Hr.
    rewrite !norm_twice.
    change (read_slice (norm 1024 (read_signal s 902%nat)) (32 * Z.of_nat r) 32 =
      read_slice (read_signal s 902%nat) (32 * Z.of_nat r) 32).
    apply slice_norm; lia.
  Qed.
  Lemma actual_address_wire s :
    norm 6 (read_signal (run_process cv32e40p_program s process_1397) 887%nat) =
    norm 6 (read_signal s 765%nat).
  Proof.
    rewrite (assign_value s process_1397 6 887%nat (rhs process_1397) eq_refl).
    change (norm 6 (norm 6 (read_signal s 765%nat)) = norm 6 (read_signal s 765%nat)).
    apply norm_twice.
  Qed.
  Lemma actual_data_wire s :
    norm 32 (read_signal (run_process cv32e40p_program s process_1399) 776%nat) =
    norm 32 (read_signal s 888%nat).
  Proof.
    rewrite (assign_value s process_1399 32 776%nat (rhs process_1399) eq_refl).
    change (norm 32 (norm 32 (read_signal s 888%nat)) = norm 32 (read_signal s 888%nat)).
    apply norm_twice.
  Qed.
  #[local] Opaque before_process comb_round run_process.
  Theorem round_rf_source s :
    norm 1 (read_signal (round s) 768%nat) = 0 ->
    norm 32 (read_signal (round s) 776%nat) =
      rf_field (read_signal s 902%nat)
        (Z.to_nat (instruction_rs1 (read_signal (round s) 718%nat))).
  Proof.
    intros Hinteger.
    assert (Ha : norm 6 (read_signal (cut 1398 s) 887%nat) =
      instruction_rs1 (read_signal (round s) 718%nat)).
    { unfold cut, round.
      rewrite <- (cut_final_root cv32e40p_program 1398 s 887%nat ltac:(vm_compute; reflexivity)).
      rewrite (comb_cut_root cv32e40p_program 1397 process_1397 s 887%nat
        eq_refl eq_refl ltac:(vm_compute; reflexivity)), actual_address_wire.
      rewrite <- (cut_final_root cv32e40p_program 1397 s 765%nat ltac:(vm_compute; reflexivity)).
      rewrite (comb_cut_root cv32e40p_program 1394 process_1394 s 765%nat
        eq_refl eq_refl ltac:(vm_compute; reflexivity)), actual_rs1.
      - rewrite <- (cut_final_root cv32e40p_program 1394 s 718%nat ltac:(vm_compute; reflexivity)). reflexivity.
      - rewrite <- (cut_final_root cv32e40p_program 1394 s 768%nat ltac:(vm_compute; reflexivity)). exact Hinteger. }
    pose proof (norm_range 5 (Z.shiftr (norm 32 (read_signal (round s) 718%nat)) 15)) as Hrange.
    change (0 <= instruction_rs1 (read_signal (round s) 718%nat) < 32) in Hrange.
    set (r := Z.to_nat (instruction_rs1 (read_signal (round s) 718%nat))) in *.
    assert (Hr : (r < 32)%nat) by (unfold r; lia).
    assert (Hrval : Z.of_nat r = instruction_rs1 (read_signal (round s) 718%nat))
      by (unfold r; rewrite Z2Nat.id by lia; reflexivity).
    rewrite <- Hrval in Ha.
    unfold round at 1.
    rewrite (comb_cut_root cv32e40p_program 1399 process_1399 s 776%nat
      eq_refl eq_refl ltac:(vm_compute; reflexivity)), actual_data_wire.
    rewrite <- (cut_final_root cv32e40p_program 1399 s 888%nat ltac:(vm_compute; reflexivity)).
    rewrite (comb_cut_root cv32e40p_program 1398 process_1398 s 888%nat
      eq_refl eq_refl ltac:(vm_compute; reflexivity)).
    change (norm 32 (read_signal (run_process cv32e40p_program (cut 1398 s) process_1398) 888%nat) =
      rf_field (read_signal s 902%nat) r).
    rewrite (actual_read_port (cut 1398 s) r Hr Ha).
    unfold cut. rewrite before_process_keeps_root by (vm_compute; reflexivity). reflexivity.
  Qed.
  Theorem forwarding_cut_rf_source s :
    norm 1 (read_signal (round s) 768%nat) = 0 ->
    norm 32 (read_signal (cut 1629 s) 776%nat) =
      rf_field (read_signal s 902%nat)
        (Z.to_nat (instruction_rs1 (read_signal (round s) 718%nat))).
  Proof.
    intros Hmode. unfold cut.
    rewrite <- (cut_final_root cv32e40p_program 1629 s 776%nat ltac:(vm_compute; reflexivity)).
    apply round_rf_source. exact Hmode.
  Qed.
  Print Assumptions forwarding_cut_rf_source.
End CV32E40PAddiRFRead.
