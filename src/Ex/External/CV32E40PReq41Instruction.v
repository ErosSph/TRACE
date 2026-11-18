(** Req41: symbolic RV32I-38 instruction and fetch boundary.

    Unlike Req39's finite fixtures, [Supported38] classifies constructor
    shapes.  Consequently every register and immediate carried by a
    supported constructor remains universally quantified.  Encoding
    legality is supplied by [CurrentInstruction]: an out-of-range field
    cannot satisfy the real fetch/decode equation.

    The generic [run1_current_instruction] theorem is shared by all six
    instruction families.  It proves that FormalSpec really fetches and
    decodes the labelled instruction before executing it; family proofs do
    not get to replace [run1] with an assumed post-state. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Ex.RvCore.FormalSpec Ex.RvCore.Machine.
Require Import riscv.Spec.Decode riscv.Spec.Execute.
Require Import riscv.Utility.Monads riscv.Utility.Utility.
Require Import coqutil.Map.Interface coqutil.Word.Interface
  coqutil.Word.Properties coqutil.Datatypes.HList.

Import ListNotations.
Local Open Scope Z_scope.

Module CV32E40PReq41Instruction.

  Inductive InstructionFamily : Set :=
  | FamilyDataOp | FamilyLoad | FamilyStore
  | FamilyBranch | FamilyJump | FamilyFenceI.

  Definition family_of (inst : Decode.InstructionI) : option InstructionFamily :=
    match inst with
    | Decode.Lb _ _ _ | Decode.Lh _ _ _ | Decode.Lw _ _ _
    | Decode.Lbu _ _ _ | Decode.Lhu _ _ _ => Some FamilyLoad
    | Decode.Sb _ _ _ | Decode.Sh _ _ _ | Decode.Sw _ _ _ => Some FamilyStore
    | Decode.Beq _ _ _ | Decode.Bne _ _ _ | Decode.Blt _ _ _
    | Decode.Bge _ _ _ | Decode.Bltu _ _ _ | Decode.Bgeu _ _ _ =>
        Some FamilyBranch
    | Decode.Jalr _ _ _ | Decode.Jal _ _ => Some FamilyJump
    | Decode.Fence_i => Some FamilyFenceI
    | Decode.Fence _ _ | Decode.InvalidI => None
    | _ => Some FamilyDataOp
    end.

  Definition supported38b (inst : Decode.InstructionI) : bool :=
    match family_of inst with Some _ => true | None => false end.

  Definition Supported38 (inst : Decode.InstructionI) : Prop :=
    supported38b inst = true.

  Definition InFamily (family : InstructionFamily)
      (inst : Decode.InstructionI) : Prop :=
    family_of inst = Some family.

  Lemma supported38_has_unique_family : forall inst,
      Supported38 inst -> exists! family, InFamily family inst.
  Proof.
    intros inst Hsupported.
    unfold Supported38, supported38b in Hsupported.
    destruct (family_of inst) as [family|] eqn:Hfamily;
      [exists family; split; [exact Hfamily|]|discriminate].
    intros other Hother. congruence.
  Qed.

  Lemma family_is_supported : forall family inst,
      InFamily family inst -> Supported38 inst.
  Proof.
    intros family inst Hfamily.
    unfold InFamily in Hfamily.
    unfold Supported38, supported38b. now rewrite Hfamily.
  Qed.

  (** The fields below are metadata used by generators and audits.  They do
      not normalize operands to a concrete fixture. *)
  Definition destination_register (inst : Decode.InstructionI) : option Z :=
    match inst with
    | Decode.Lb rd _ _ | Decode.Lh rd _ _ | Decode.Lw rd _ _
    | Decode.Lbu rd _ _ | Decode.Lhu rd _ _
    | Decode.Addi rd _ _ | Decode.Slli rd _ _ | Decode.Slti rd _ _
    | Decode.Sltiu rd _ _ | Decode.Xori rd _ _ | Decode.Ori rd _ _
    | Decode.Andi rd _ _ | Decode.Srli rd _ _ | Decode.Srai rd _ _
    | Decode.Auipc rd _ | Decode.Add rd _ _ | Decode.Sub rd _ _
    | Decode.Sll rd _ _ | Decode.Slt rd _ _ | Decode.Sltu rd _ _
    | Decode.Xor rd _ _ | Decode.Srl rd _ _ | Decode.Sra rd _ _
    | Decode.Or rd _ _ | Decode.And rd _ _ | Decode.Lui rd _
    | Decode.Jalr rd _ _ | Decode.Jal rd _ => Some rd
    | _ => None
    end.

  Definition source_registers (inst : Decode.InstructionI) : list Z :=
    match inst with
    | Decode.Lb _ rs1 _ | Decode.Lh _ rs1 _ | Decode.Lw _ rs1 _
    | Decode.Lbu _ rs1 _ | Decode.Lhu _ rs1 _
    | Decode.Addi _ rs1 _ | Decode.Slli _ rs1 _ | Decode.Slti _ rs1 _
    | Decode.Sltiu _ rs1 _ | Decode.Xori _ rs1 _ | Decode.Ori _ rs1 _
    | Decode.Andi _ rs1 _ | Decode.Srli _ rs1 _ | Decode.Srai _ rs1 _
    | Decode.Jalr _ rs1 _ => [rs1]
    | Decode.Sb rs1 rs2 _ | Decode.Sh rs1 rs2 _ | Decode.Sw rs1 rs2 _
    | Decode.Add _ rs1 rs2 | Decode.Sub _ rs1 rs2 | Decode.Sll _ rs1 rs2
    | Decode.Slt _ rs1 rs2 | Decode.Sltu _ rs1 rs2
    | Decode.Xor _ rs1 rs2 | Decode.Srl _ rs1 rs2 | Decode.Sra _ rs1 rs2
    | Decode.Or _ rs1 rs2 | Decode.And _ rs1 rs2
    | Decode.Beq rs1 rs2 _ | Decode.Bne rs1 rs2 _ | Decode.Blt rs1 rs2 _
    | Decode.Bge rs1 rs2 _ | Decode.Bltu rs1 rs2 _ | Decode.Bgeu rs1 rs2 _ =>
        [rs1; rs2]
    | _ => []
    end.

  Definition immediate_field (inst : Decode.InstructionI) : option Z :=
    match inst with
    | Decode.Lb _ _ imm | Decode.Lh _ _ imm | Decode.Lw _ _ imm
    | Decode.Lbu _ _ imm | Decode.Lhu _ _ imm
    | Decode.Addi _ _ imm | Decode.Slli _ _ imm | Decode.Slti _ _ imm
    | Decode.Sltiu _ _ imm | Decode.Xori _ _ imm | Decode.Ori _ _ imm
    | Decode.Andi _ _ imm | Decode.Srli _ _ imm | Decode.Srai _ _ imm
    | Decode.Auipc _ imm | Decode.Sb _ _ imm | Decode.Sh _ _ imm
    | Decode.Sw _ _ imm | Decode.Lui _ imm
    | Decode.Beq _ _ imm | Decode.Bne _ _ imm | Decode.Blt _ _ imm
    | Decode.Bge _ _ imm | Decode.Bltu _ _ imm | Decode.Bgeu _ _ imm
    | Decode.Jalr _ _ imm | Decode.Jal _ imm => Some imm
    | _ => None
    end.

Section WithContext.
  Context {word : Interface.word 32} {BW : Bitwidth 32}.
  Context {Registers : map.map Decode.Register word}
          {Mem : map.map word byte}.
  Context {word_ok : word.ok word} {registers_ok : map.ok Registers}
          {mem_ok : map.ok Mem}.

  (** Relational rather than computational because instruction memory is an
      abstract finite map.  This is the exact generic version of Req40's
      [ADDIAtPC]. *)
  Record CurrentInstruction (s : FormalSpec.State)
      (inst : Decode.InstructionI) : Prop := {
    current_pc_aligned : word.unsigned (getPc s) mod 4 = 0;
    current_fetch_decode : exists bytes : tuple byte 4,
      Memory.load_bytes 4 (getInstMem s) (getPc s) = Some bytes /\
      Decode.decode Decode.RV32I (LittleEndian.combine 4 bytes) =
        Decode.IInstruction inst
  }.

  Lemma current_instruction_unique : forall s left right,
      CurrentInstruction s left -> CurrentInstruction s right -> left = right.
  Proof.
    intros s left right Hleft Hright.
    destruct Hleft as [_ [left_bytes [Hleft_load Hleft_decode]]].
    destruct Hright as [_ [right_bytes [Hright_load Hright_decode]]].
    rewrite Hleft_load in Hright_load. inversion Hright_load; subst.
    now rewrite Hleft_decode in Hright_decode; inversion Hright_decode.
  Qed.

  (** One fetch/decode theorem for every symbolic family.  The instruction
      execution is deliberately left symbolic; family files may reason
      about its RF, memory and control-flow footprint independently. *)
  Theorem run1_current_instruction : forall s inst,
      CurrentInstruction s inst ->
      FormalSpec.run1 s =
        Monads.Bind (Execute.execute (Decode.IInstruction inst))
          (fun _ => Machine.endCycleNormal) s.
  Proof.
    intros [regs pc nextpc imem dmem] inst Hcurrent.
    destruct Hcurrent as [Halign [bytes [Hload Hdecode]]].
    cbn [getPc getInstMem] in Halign, Hload.
    change (Decode.decode Decode.RV32I
      (LittleEndian.combine_deprecated 4 bytes) =
      Decode.IInstruction inst) in Hdecode.
    unfold FormalSpec.run1.
    cbn [Monads.Bind Monads.OState_Monad].
    unfold Machine.getPC. cbn [IsRiscvProgram].
    cbn [Monads.Bind Monads.Return Monads.OState_Monad
         Monads.OStateOperations.get].
    unfold Machine.loadWord, Machine.loadN, Machine.assert_aligned,
      Machine.fail_if_None.
    cbn [IsRiscvProgram].
    unfold loadN, assert_aligned, fail_if_None.
    cbn [getPc getInstMem].
    assert (HAL : negb (reg_eqb (remu pc (ZToReg 4)) (ZToReg 0)) = false).
    { change (negb (word.eqb (word.modu pc (word.of_Z 4))
                    (word.of_Z 0)) = false).
      rewrite word.unsigned_eqb.
      rewrite word.unsigned_modu.
      2: { rewrite word.unsigned_of_Z. unfold word.wrap.
           rewrite Z.mod_small by lia. lia. }
      rewrite !word.unsigned_of_Z. unfold word.wrap.
      change (4 mod 2 ^ 32) with 4.
      change (0 mod 2 ^ 32) with 0.
      rewrite Halign. reflexivity. }
    rewrite HAL.
    cbn [Monads.Bind Monads.Return Monads.OState_Monad
         Monads.OStateOperations.get].
    cbn [getInstMem]. rewrite Hload. cbn.
    setoid_rewrite Hdecode. reflexivity.
  Qed.

  Definition ISAStep (s : FormalSpec.State) (inst : Decode.InstructionI)
      (s' : FormalSpec.State) : Prop :=
    Monads.Bind (Execute.execute (Decode.IInstruction inst))
      (fun _ => Machine.endCycleNormal) s = (Some tt, s').

  Theorem current_instruction_run1_step : forall s inst s',
      CurrentInstruction s inst -> ISAStep s inst s' ->
      FormalSpec.run1 s = (Some tt, s').
  Proof.
    intros s inst s' Hcurrent Hstep.
    rewrite (run1_current_instruction s inst Hcurrent).
    exact Hstep.
  Qed.

End WithContext.

End CV32E40PReq41Instruction.
