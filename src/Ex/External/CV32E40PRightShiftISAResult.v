(** The four right-shift ISA cases, with legality derived from the real
    reference decoder. These lemmas describe ISA arithmetic only; they do
    not assume or certify CPU operands or a post-state. *)
From Coq Require Import ZArith Bool Lia.
Require Import Ex.RvCore.FormalSpec Ex.RvCore.Machine
  Lang.ExtendedSV Ex.External.CV32E40PISAWordRightShift
  Ex.External.CV32E40PDataOpPendingRegisters Ex.External.CV32E40PDataOpExecution
  Ex.External.CV32E40PReq40StateRel Ex.External.CV32E40PReq41Instruction
  Ex.External.CV32E40PAddiAdder Ex.External.CV32E40PAddiAdderResult.
Require Import riscv.Proofs.VerifyDecode coqutil.Word.Interface coqutil.Word.Properties
  coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte.
Import ExtendedSV CV32E40PISAWordRightShift CV32E40PDataOpPendingRegisters
  CV32E40PDataOpExecution CV32E40PReq40StateRel CV32E40PReq41Instruction
  CV32E40PAddiAdder CV32E40PAddiAdderResult.
Local Open Scope Z_scope.
Module CV32E40PRightShiftISAResult.
Definition RightShiftDataOp i : Prop := match i with
  | Decode.Srli _ _ _ | Decode.Srai _ _ _ | Decode.Srl _ _ _ | Decode.Sra _ _ _ => True
  | _ => False end.
Definition ImmediateShiftLegal i : Prop := match i with
  | Decode.Srli _ _ sh | Decode.Srai _ _ sh => 0 <= sh < 32
  | _ => True end.
Lemma decoded_right_shift_legal code i : RightShiftDataOp i ->
  Decode.decode Decode.RV32I code = Decode.IInstruction i -> ImmediateShiftLegal i.
Proof.
  intros HI HD.
  destruct (verify_decode Decode.RV32I code eq_refl) as [HV|HB];
    [rewrite HD in HV|congruence].
  destruct i; cbn [RightShiftDataOp] in HI; try contradiction.
  all: cbv [verify respects_bounds apply_InstructionMapper Verifier
    map_U map_I map_I_shift_66 map_R verify_U verify_I verify_I_shift_66 verify_R
    bitwidth verify_iset] in HV.
  all: cbn [ImmediateShiftLegal]; intuition lia.
Qed.

Definition right_shift_value (arithmetic : bool) (x amount : Z) :=
  norm 32 (Z.shiftr (if arithmetic then signed_value 32 x else norm 32 x) amount).
Lemma immediate_shift_amount sh : 0 <= sh < 32 -> norm 5 (sh mod 2^32) = sh.
Proof.
  intros HS. rewrite norm_mod. change ((sh mod 4294967296) mod 32 = sh).
  rewrite (Z.mod_small sh 4294967296) by lia.
  rewrite (Z.mod_small sh 32) by exact HS. reflexivity.
Qed.

Section ISA.
Context {word : Interface.word 32} {BW : Bitwidth 32}.
Context {Registers : map.map Decode.Register word} {Mem : map.map word byte}.
Context {word_ok : word.ok word} {registers_ok : map.ok Registers} {mem_ok : map.ok Mem}.
Lemma current_right_shift_legal (isa : FormalSpec.State) i :
  RightShiftDataOp i -> CurrentInstruction isa i -> ImmediateShiftLegal i.
Proof.
  intros HI [_ [bytes [_ HD]]]. eapply decoded_right_shift_legal; eauto.
Qed.
End ISA.
Theorem right_shift_value_is_isa (isa : FormalSpec.State) i :
  RightShiftDataOp i -> ImmediateShiftLegal i ->
  right_shift_value (scalar_opcode i =? 36) (left_value isa i)
    (norm 5 (right_value isa i)) = word.unsigned (result_word isa i).
Proof.
  intros HI HL. destruct i; cbn [RightShiftDataOp] in HI; try contradiction.
  all: cbn [ImmediateShiftLegal] in HL.
  all: cbn [right_shift_value scalar_opcode left_value right_value source_registers result_word].
  all: try change (37 =? 36) with false.
  all: try change (36 =? 36) with true.
  all: unfold right_shift_value; cbn beta iota.
  all: try rewrite immediate_shift_amount by exact HL.
  all: try match goal with |- context [norm 5 (word.unsigned ?w)] =>
    rewrite (norm_mod 5 (word.unsigned w)) end.
  all: cbn [Utility.srl Utility.sra Utility.regToShamt MkMachineWidth.MachineWidth_XLEN].
  all: first [apply reference_logical_right_shift | apply reference_arithmetic_right_shift].
  all: try exact HL.
  all: change (0 <= word.unsigned (formal_register_word isa rs2) mod 32 < 32).
  all: apply Z.mod_pos_bound; lia.
Qed.
Print Assumptions decoded_right_shift_legal.
Print Assumptions right_shift_value_is_isa.
End CV32E40PRightShiftISAResult.
