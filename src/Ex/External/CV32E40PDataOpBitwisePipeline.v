(** Actual FullCore bitwise ALU and RF path. Control reachability and operand
    freshness are still separate obligations; no global invariant is claimed. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVBlocking Lang.ExtendedSVCombCut
 Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiALUOutput
 Ex.External.CV32E40PAddiAdderInputs Ex.External.CV32E40PAddiOperands
 Ex.External.CV32E40PAddiOperandCone Ex.External.CV32E40PAddiWritebackCone
 Ex.External.CV32E40PAddiRFFields Ex.External.CV32E40PAddiRFLocal
 Ex.External.CV32E40PAddiRFPhase.
Import ListNotations ExtendedSV ExtendedSVBlocking ExtendedSVCombCut
 CV32E40PExtendedAST CV32E40PAddiALUOutput CV32E40PAddiAdderInputs
 CV32E40PAddiOperands CV32E40PAddiOperandCone CV32E40PAddiWritebackCone
 CV32E40PAddiRFFields CV32E40PAddiRFLocal CV32E40PAddiRFPhase
 CV32E40PAddiIDEXAccept.CV32E40PAddiIDEXAccept
 CV32E40PAddiDecoder.CV32E40PAddiDecoder
 CV32E40PAddiWritebackMux.CV32E40PAddiWritebackMux.
Local Open Scope Z_scope.
Module CV32E40PDataOpBitwisePipeline.
 Inductive LogicOp := LogicAnd | LogicOr | LogicXor.
 Definition opcode op := match op with LogicAnd => 21 | LogicOr => 46 | LogicXor => 47 end.
 Definition logic op := match op with LogicAnd => Z.land | LogicOr => Z.lor | LogicXor => Z.lxor end.
 Definition local_result op s := norm 32 (logic op
   (norm 32 (read_signal s 1304%nat)) (norm 32 (read_signal s 1305%nat))).

 Lemma actual_logic_process op s : norm 7 (read_signal s 1303%nat) = opcode op ->
   norm 32 (read_signal (run_process cv32e40p_program s process_1896) 1314%nat) = local_result op s.
 Proof.
   intros H. rewrite blocking_run_process by reflexivity.
   change (statement_fuel cv32e40p_program) with 512%nat.
   cbn [process_1896 process_body]. rewrite exec_sequence, fold_one, exec_sequence, fold_two, exec_case.
   cbn [eval_expr].
   rewrite (preserves_inputs 510 (SAssign false (EConst 32 0) (LVar 32 1314%nat)) _ 1303%nat eq_refl).
   cbn [blocking_state]. rewrite H. destruct op;
     cbn [opcode select_case_stmt eval_expr];
     change (norm 7 21) with 21; change (norm 7 46) with 46;
     change (norm 7 47) with 47; cbn [Z.eqb Pos.eqb];
     cbv beta iota zeta delta [exec_stmt blocking_state apply_update resolve_update resolve_lvalue
       update_signal update_offset update_width update_value eval_expr];
     rewrite read_signal_write_same, norm_write_low, !norm_twice;
     repeat rewrite read_signal_write_other by discriminate; reflexivity.
 Qed.
 #[local] Opaque before_process comb_round run_process.
 Theorem fullcore_logic_output op s :
   norm 7 (read_signal (cut 1896 s) 1303%nat) = opcode op ->
   norm 32 (read_signal (round s) 1314%nat) = local_result op (cut 1896 s).
 Proof.
   intros H. unfold round.
   rewrite (comb_cut_root cv32e40p_program 1896 process_1896 s 1314%nat
     eq_refl eq_refl ltac:(vm_compute; reflexivity)).
   apply actual_logic_process. exact H.
 Qed.
 Definition sampled_logic op ev pre := local_result op (cut 1896 (phase_round4 ev pre)).
 #[local] Opaque phase_driven_state PhaseSemantics.
 Theorem actual_rf_data_is_logic op ev pre :
   norm 7 (read_signal (cut 1896 (phase_round4 ev pre)) 1303%nat) = opcode op ->
   ALUSelected (round (phase_round4 ev pre)) ->
   norm 32 (read_signal (phase_driven_state cv32e40p_program ev pre) 897%nat) = sampled_logic op ev pre.
 Proof.
   intros H Hselect. rewrite phase_rf_data_from_actual_alu by exact Hselect.
   unfold sampled_alu, sampled_logic. apply fullcore_logic_output. exact H.
 Qed.
 Theorem actual_logic_writeback_all_registers op ev pre rd :
   changed_signal ev <> 902%nat ->
   rf_trigger pre (phase_driven_state cv32e40p_program ev pre) = true ->
   norm 1 (read_signal (phase_driven_state cv32e40p_program ev pre) 885%nat) <> 0 ->
   (forall r, (0 < r < 32)%nat -> lane_enabled (phase_driven_state cv32e40p_program ev pre) 906%nat r = 0) ->
   (forall r, (0 < r < 32)%nat ->
     (lane_enabled (phase_driven_state cv32e40p_program ev pre) 907%nat r <> 0 <-> r = rd)) ->
   norm 7 (read_signal (cut 1896 (phase_round4 ev pre)) 1303%nat) = opcode op ->
   ALUSelected (round (phase_round4 ev pre)) ->
   forall r, (r < 32)%nat ->
     rf_field (read_signal (PhaseSemantics cv32e40p_program ev pre) 902%nat) r =
       if Nat.eq_dec r 0 then 0 else if Nat.eq_dec r rd then sampled_logic op ev pre
       else rf_field (read_signal pre 902%nat) r.
 Proof.
   intros Hev Hedge Hreset Ha Hb Hop Hselect.
   apply fullcore_single_port_b_write; try assumption.
   now apply actual_rf_data_is_logic.
 Qed.
 Print Assumptions actual_logic_writeback_all_registers.
End CV32E40PDataOpBitwisePipeline.
