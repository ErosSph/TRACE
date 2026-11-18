(** Actual integer RF B read port and rs2 extraction.  This is the symmetric
    companion of [CV32E40PAddiRFRead]'s A-port certificate.  It follows the
    original decoder/RF/forwarding processes 1401, 1404--1406 and does not
    replace the DUT with a handwritten transition. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVCombCut Lang.ExtendedSVBitSlice
 Ex.Generated.CV32E40PExtendedAST Ex.Generated.CV32E40PGeneratedRFProcessPorts
 Ex.External.CV32E40PAddiAdderInputs
 Ex.External.CV32E40PAddiAdderBits Ex.External.CV32E40PAddiDestination
 Ex.External.CV32E40PAddiRFFields Ex.External.CV32E40PAddiOperandCone
 Ex.External.CV32E40PAddiIDEXAccept.
Import ExtendedSV ExtendedSVCombCut ExtendedSVBitSlice CV32E40PExtendedAST
 CV32E40PAddiAdderInputs CV32E40PAddiAdderBits CV32E40PAddiDestination
 CV32E40PAddiRFFields CV32E40PAddiOperandCone
 CV32E40PAddiIDEXAccept.CV32E40PAddiIDEXAccept.
Local Open Scope Z_scope.
Module CV32E40PRFReadB.
 Definition instruction_rs2 ins := norm 5 (Z.shiftr (norm 32 ins) 20).
 Lemma actual_rs2 s : norm 1 (read_signal s 769%nat) = 0 ->
   norm 6 (read_signal (run_process cv32e40p_program s process_1401) 766%nat) =
     instruction_rs2 (read_signal s 718%nat).
 Proof.
   intros H. rewrite (assign_value s process_1401 6 766%nat (rhs process_1401) eq_refl).
   unfold rhs, instruction_rs2. cbn [process_1401 process_body eval_expr expr_width].
   rewrite H. change (norm 5 20) with 20.
   rewrite Z.shiftl_0_l, Z.lor_0_l, norm_twice. apply extend_rd.
 Qed.
 Lemma actual_address_wire_b s :
   norm 6 (read_signal (run_process cv32e40p_program s process_1404) 889%nat) =
   norm 6 (read_signal s 766%nat).
 Proof.
   rewrite (assign_value s process_1404 6 889%nat (rhs process_1404) eq_refl).
   change (norm 6 (norm 6 (read_signal s 766%nat)) = norm 6 (read_signal s 766%nat)).
   apply norm_twice.
 Qed.
 Lemma actual_read_port_b s r : (r < 32)%nat ->
   norm 6 (read_signal s 889%nat) = Z.of_nat r ->
   norm 32 (read_signal (run_process cv32e40p_program s process_1405) 890%nat) =
     rf_field (read_signal s 902%nat) r.
 Proof.
   intros Hr Haddr.
   rewrite (CV32E40PGeneratedRFProcessPorts.port_1_process s).
   unfold CV32E40PGeneratedRFPorts.port_1_rhs. cbn [eval_expr expr_width].
   rewrite Haddr.
   change (norm 3 5) with 5. change (norm 3 0) with 0.
   change (norm 32 5) with 5. change (norm 32 0) with 0.
   assert (Hhi : Z.shiftr (Z.of_nat r) 5 = 0).
   { rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small.
     change (0 <= Z.of_nat r < 32). lia. }
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
 Lemma actual_data_wire_b s :
   norm 32 (read_signal (run_process cv32e40p_program s process_1406) 777%nat) =
   norm 32 (read_signal s 890%nat).
 Proof.
   rewrite (assign_value s process_1406 32 777%nat (rhs process_1406) eq_refl).
   change (norm 32 (norm 32 (read_signal s 890%nat)) = norm 32 (read_signal s 890%nat)).
   apply norm_twice.
 Qed.
 #[local] Opaque before_process comb_round run_process.
 Theorem round_rf_source_b s :
   norm 1 (read_signal (round s) 769%nat) = 0 ->
   norm 32 (read_signal (round s) 777%nat) =
     rf_field (read_signal s 902%nat)
       (Z.to_nat (instruction_rs2 (read_signal (round s) 718%nat))).
 Proof.
   intros Hinteger.
   assert (Ha : norm 6 (read_signal (cut 1405 s) 889%nat) =
     instruction_rs2 (read_signal (round s) 718%nat)).
   { unfold cut, round.
     rewrite <- (cut_final_root cv32e40p_program 1405 s 889%nat ltac:(vm_compute; reflexivity)).
     rewrite (comb_cut_root cv32e40p_program 1404 process_1404 s 889%nat
       eq_refl eq_refl ltac:(vm_compute; reflexivity)), actual_address_wire_b.
     rewrite <- (cut_final_root cv32e40p_program 1404 s 766%nat ltac:(vm_compute; reflexivity)).
     rewrite (comb_cut_root cv32e40p_program 1401 process_1401 s 766%nat
       eq_refl eq_refl ltac:(vm_compute; reflexivity)), actual_rs2.
     - rewrite <- (cut_final_root cv32e40p_program 1401 s 718%nat ltac:(vm_compute; reflexivity)).
       reflexivity.
     - rewrite <- (cut_final_root cv32e40p_program 1401 s 769%nat ltac:(vm_compute; reflexivity)).
       exact Hinteger. }
   pose proof (norm_range 5 (Z.shiftr (norm 32 (read_signal (round s) 718%nat)) 20)) as Hrange.
   change (0 <= instruction_rs2 (read_signal (round s) 718%nat) < 32) in Hrange.
   set (r := Z.to_nat (instruction_rs2 (read_signal (round s) 718%nat))) in *.
   assert (Hr : (r < 32)%nat) by (unfold r; lia).
   assert (Hrval : Z.of_nat r = instruction_rs2 (read_signal (round s) 718%nat))
     by (unfold r; rewrite Z2Nat.id by lia; reflexivity).
   rewrite <- Hrval in Ha.
   unfold round at 1.
   rewrite (comb_cut_root cv32e40p_program 1406 process_1406 s 777%nat
     eq_refl eq_refl ltac:(vm_compute; reflexivity)), actual_data_wire_b.
   rewrite <- (cut_final_root cv32e40p_program 1406 s 890%nat ltac:(vm_compute; reflexivity)).
   rewrite (comb_cut_root cv32e40p_program 1405 process_1405 s 890%nat
     eq_refl eq_refl ltac:(vm_compute; reflexivity)).
   change (norm 32 (read_signal (run_process cv32e40p_program (cut 1405 s) process_1405) 890%nat) =
     rf_field (read_signal s 902%nat) r).
   rewrite (actual_read_port_b (cut 1405 s) r Hr Ha).
   unfold cut. rewrite before_process_keeps_root by (vm_compute; reflexivity). reflexivity.
 Qed.
 Theorem forwarding_cut_rf_source_b s :
   norm 1 (read_signal (round s) 769%nat) = 0 ->
   norm 32 (read_signal (cut 1634 s) 777%nat) =
     rf_field (read_signal s 902%nat)
       (Z.to_nat (instruction_rs2 (read_signal (round s) 718%nat))).
 Proof.
   intros Hmode. unfold cut.
   rewrite <- (cut_final_root cv32e40p_program 1634 s 777%nat ltac:(vm_compute; reflexivity)).
   apply round_rf_source_b. exact Hmode.
 Qed.
 Print Assumptions forwarding_cut_rf_source_b.
End CV32E40PRFReadB.
