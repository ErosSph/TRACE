(** Arithmetic value through original FullCore combinational order and RF edge.
    Control, trigger and one-hot write-enable obligations remain explicit.
    No premise assumes the expected ALU result or RF write-data value. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVCombCut Ex.Generated.CV32E40PExtendedAST
  Ex.External.CV32E40PAddiOperandCone Ex.External.CV32E40PAddiFullCoreALU
  Ex.External.CV32E40PAddiWritebackCone Ex.External.CV32E40PAddiRFFields
  Ex.External.CV32E40PAddiRFLocal Ex.External.CV32E40PAddiRFPhase.
Import ExtendedSV ExtendedSVCombCut CV32E40PExtendedAST CV32E40PAddiOperandCone
  CV32E40PAddiFullCoreALU CV32E40PAddiWritebackCone CV32E40PAddiRFFields
  CV32E40PAddiRFLocal CV32E40PAddiRFPhase.
Local Open Scope Z_scope.
Module CV32E40PAddiALUWriteback.
  Definition sampled_sum ev pre := norm 32
    (read_signal (cut 621 (phase_round4 ev pre)) 1304%nat +
     read_signal (cut 621 (phase_round4 ev pre)) 1305%nat).
  #[local] Opaque phase_driven_state comb_round before_process PhaseSemantics.
  Theorem actual_rf_data_is_sum ev pre :
    ScalarADD (phase_round4 ev pre) ->
    ALUSelected (round (phase_round4 ev pre)) ->
    norm 32 (read_signal (phase_driven_state cv32e40p_program ev pre) 897%nat) =
      sampled_sum ev pre.
  Proof.
    intros Hadd Hselect. rewrite phase_rf_data_from_actual_alu by exact Hselect.
    unfold sampled_alu, sampled_sum. apply fullcore_alu_scalar_add. exact Hadd.
  Qed.
  Theorem actual_add_writeback_all_registers ev pre rd :
    changed_signal ev <> 902%nat ->
    rf_trigger pre (phase_driven_state cv32e40p_program ev pre) = true ->
    norm 1 (read_signal (phase_driven_state cv32e40p_program ev pre) 885%nat) <> 0 ->
    (forall r, (0 < r < 32)%nat ->
      lane_enabled (phase_driven_state cv32e40p_program ev pre) 906%nat r = 0) ->
    (forall r, (0 < r < 32)%nat ->
      (lane_enabled (phase_driven_state cv32e40p_program ev pre) 907%nat r <> 0 <-> r = rd)) ->
    ScalarADD (phase_round4 ev pre) ->
    ALUSelected (round (phase_round4 ev pre)) ->
    forall r, (r < 32)%nat ->
      rf_field (read_signal (PhaseSemantics cv32e40p_program ev pre) 902%nat) r =
        if Nat.eq_dec r 0 then 0
        else if Nat.eq_dec r rd then sampled_sum ev pre
        else rf_field (read_signal pre 902%nat) r.
  Proof.
    intros Hev Hedge Hreset Ha Hb Hadd Hselect.
    apply fullcore_single_port_b_write; try assumption.
    apply actual_rf_data_is_sum; assumption.
  Qed.
  Print Assumptions actual_add_writeback_all_registers.
End CV32E40PAddiALUWriteback.
