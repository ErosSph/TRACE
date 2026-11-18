(** Actual FullCore RF edge -> ISA ADDI register file, including all nonzero
    registers. This is a local preservation theorem, NOT a reachability proof.
    Architectural operand alignment and reachable controls remain obligations. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVCombCut
  Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiALUWriteback
  Ex.External.CV32E40PAddiRFFields Ex.External.CV32E40PAddiRFLocal
  Ex.External.CV32E40PAddiRFPhase Ex.External.CV32E40PAddiOperandCone
  Ex.External.CV32E40PAddiFullCoreALU Ex.External.CV32E40PAddiWritebackCone
  Ex.External.CV32E40PAddiAdder Ex.External.CV32E40PReq40StateRel
  Ex.RvCore.FormalSpec Ex.RvCore.Machine.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Word.Properties.
Require Import riscv.Utility.Utility.
Import ExtendedSV ExtendedSVCombCut CV32E40PExtendedAST
  CV32E40PAddiALUWriteback CV32E40PAddiRFFields CV32E40PAddiRFLocal
  CV32E40PAddiRFPhase CV32E40PAddiOperandCone CV32E40PAddiFullCoreALU
  CV32E40PAddiWritebackCone CV32E40PAddiAdder CV32E40PReq40StateRel.
Local Open Scope Z_scope.
Module CV32E40PAddiRFPreservation.
#[local] Opaque phase_driven_state comb_round before_process PhaseSemantics.
Section ISA.
  Context {word : Interface.word 32} {BW : Bitwidth 32}.
  Context {Registers : map.map Z word} {Mem : map.map word byte}.
  Context {word_ok : word.ok word} {registers_ok : map.ok Registers}
          {mem_ok : map.ok Mem}.

  Definition RFRelated (rtl : State) (isa : FormalSpec.State) :=
    forall r, (r < 32)%nat ->
      rf_field (read_signal rtl 902%nat) r = isa_rf_value isa (Z.of_nat r).

  Definition OperandsRelated ev pre (isa : FormalSpec.State) rs imm :=
    norm 32 (read_signal (cut 621 (phase_round4 ev pre)) 1304%nat) =
      isa_rf_value isa rs /\
    norm 32 (read_signal (cut 621 (phase_round4 ev pre)) 1305%nat) = norm 32 imm.

  Lemma sampled_sum_is_isa_result ev pre isa rs imm :
    legal_reg rs -> OperandsRelated ev pre isa rs imm ->
    sampled_sum ev pre = word.unsigned (addi_result_word isa rs imm).
  Proof.
    intros Hrs [Ha Hb]. rewrite addi_result_word_unsigned by exact Hrs.
    unfold sampled_sum. rewrite norm_mod.
    change (2 ^ Z.of_nat 32) with (2 ^ 32).
    rewrite !norm_mod in Ha, Hb.
    change (read_signal (cut 621 (phase_round4 ev pre)) 1304%nat mod 2^32 = isa_rf_value isa rs) in Ha.
    change (read_signal (cut 621 (phase_round4 ev pre)) 1305%nat mod 2^32 = norm 32 imm) in Hb.
    rewrite Z.add_mod by lia.
    rewrite Ha, Hb, norm_mod, Z.add_mod_idemp_r by lia. reflexivity.
  Qed.

  #[local] Opaque phase_driven_state comb_round before_process PhaseSemantics.
  Theorem actual_rf_edge_preserves_isa_relation ev pre isa rd rs imm :
    (rd < 32)%nat -> legal_reg rs -> RFRelated pre isa ->
    OperandsRelated ev pre isa rs imm ->
    changed_signal ev <> 902%nat ->
    rf_trigger pre (phase_driven_state cv32e40p_program ev pre) = true ->
    norm 1 (read_signal (phase_driven_state cv32e40p_program ev pre) 885%nat) <> 0 ->
    (forall r, (0 < r < 32)%nat ->
      lane_enabled (phase_driven_state cv32e40p_program ev pre) 906%nat r = 0) ->
    (forall r, (0 < r < 32)%nat ->
      (lane_enabled (phase_driven_state cv32e40p_program ev pre) 907%nat r <> 0 <-> r = rd)) ->
    ScalarADD (phase_round4 ev pre) ->
    ALUSelected (round (phase_round4 ev pre)) ->
    RFRelated (PhaseSemantics cv32e40p_program ev pre)
      (addi_isa_post isa (Z.of_nat rd) rs imm).
  Proof.
    intros Hrd Hrs Hrel Hops Hev Hfire Hreset Ha Hb Hadd Hselect r Hr.
    rewrite (actual_add_writeback_all_registers ev pre rd Hev Hfire Hreset Ha Hb Hadd Hselect r Hr).
    rewrite addi_isa_post_rf by (unfold legal_reg; lia).
    rewrite (sampled_sum_is_isa_result ev pre isa rs imm Hrs Hops).
    destruct (Nat.eq_dec r 0) as [->|Hrz].
    - unfold isa_rf_value. destruct (Z.eq_dec (Z.of_nat rd) 0);
        repeat destruct Z.eq_dec; try reflexivity; lia.
    - destruct (Nat.eq_dec r rd) as [Heq|Hne];
        destruct (Z.eq_dec (Z.of_nat rd) 0);
        destruct (Z.eq_dec (Z.of_nat r) (Z.of_nat rd)); try lia;
        try reflexivity; apply Hrel; exact Hr.
  Qed.
End ISA.
Print Assumptions actual_rf_edge_preserves_isa_relation.
End CV32E40PAddiRFPreservation.
