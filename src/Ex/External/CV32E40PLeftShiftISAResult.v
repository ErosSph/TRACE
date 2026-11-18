(** Two left-shift reference cases with bounds from the actual RV32I
    decoder. This is an ISA arithmetic bridge, not a CPU source-value oracle. *)
From Coq Require Import ZArith Bool Lia.
Require Import Ex.RvCore.FormalSpec Ex.RvCore.Machine Lang.ExtendedSV
  Ex.External.CV32E40PISAWordLeftShift Ex.External.CV32E40PRightShiftISAResult
  Ex.External.CV32E40PDataOpPendingRegisters Ex.External.CV32E40PDataOpExecution
  Ex.External.CV32E40PReq40StateRel Ex.External.CV32E40PReq41Instruction
  Ex.External.CV32E40PAddiAdder Ex.External.CV32E40PAddiAdderResult.
Require Import riscv.Proofs.VerifyDecode coqutil.Word.Interface coqutil.Word.Properties
  coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte.
Import ExtendedSV CV32E40PISAWordLeftShift CV32E40PRightShiftISAResult
  CV32E40PDataOpPendingRegisters CV32E40PDataOpExecution CV32E40PReq40StateRel
  CV32E40PReq41Instruction CV32E40PAddiAdder CV32E40PAddiAdderResult.
Local Open Scope Z_scope.
Module CV32E40PLeftShiftISAResult.
Definition LeftShiftDataOp i : Prop := match i with
  | Decode.Slli _ _ _ | Decode.Sll _ _ _ => True | _ => False end.
Definition LeftShiftLegal i : Prop := match i with
  | Decode.Slli _ _ sh => 0 <= sh < 32 | _ => True end.
Lemma decoded_left_shift_legal code i : LeftShiftDataOp i ->
  Decode.decode Decode.RV32I code = Decode.IInstruction i -> LeftShiftLegal i.
Proof.
  intros HI HD.
  destruct (verify_decode Decode.RV32I code eq_refl) as [HV|HB];
    [rewrite HD in HV|congruence].
  destruct i; cbn [LeftShiftDataOp] in HI; try contradiction.
  all: cbv [verify respects_bounds apply_InstructionMapper Verifier
    map_U map_I map_I_shift_66 map_R verify_U verify_I verify_I_shift_66 verify_R
    bitwidth verify_iset] in HV.
  all: cbn [LeftShiftLegal]; intuition lia.
Qed.
Definition left_shift_value x amount := norm 32 (Z.shiftl (norm 32 x) amount).
Theorem left_shift_value_is_isa (isa : FormalSpec.State) i :
  LeftShiftDataOp i -> LeftShiftLegal i ->
  left_shift_value (left_value isa i) (norm 5 (right_value isa i)) =
    word.unsigned (result_word isa i).
Proof.
  intros HI HL. destruct i; cbn [LeftShiftDataOp] in HI; try contradiction.
  all: cbn [LeftShiftLegal] in HL.
  all: cbn [left_shift_value left_value right_value source_registers result_word].
  all: try rewrite immediate_shift_amount by exact HL.
  all: try match goal with |- context [norm 5 (word.unsigned ?w)] =>
    rewrite (norm_mod 5 (word.unsigned w)) end.
  all: cbn [Utility.sll Utility.regToShamt MkMachineWidth.MachineWidth_XLEN].
  all: apply reference_left_shift.
  all: try exact HL.
  all: change (0 <= word.unsigned (formal_register_word isa rs2) mod 32 < 32).
  all: apply Z.mod_pos_bound; lia.
Qed.
Print Assumptions decoded_left_shift_legal.
Print Assumptions left_shift_value_is_isa.
End CV32E40PLeftShiftISAResult.
