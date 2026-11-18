(**
    RV32I data-operation coverage for the optimized Bzeeno baseline.

    This file is the instruction-completion layer above the single ADDI
    baseline.  It deliberately starts with the ISA reference side:

    - every RV32I integer data-operation instruction has a concrete encoding;
    - the encoding is decoded by riscv-coq as the intended instruction.

    The next layer connects these cases to the optimized Bzeeno RTL trace.
    Keeping this file separate from the raw no-opt baseline makes performance
    experiments reproducible: instruction coverage can be validated quickly,
    while [BzeenoBaselineADDI_BruteForce.v] remains the unoptimized timing
    baseline.
 *)
From Coq Require Import ZArith.BinInt Lists.List Lia.
Require Import Lib.Lib. Import SZNotations.
Require Import Lang.Lang.
Require riscv.Spec.Decode.
Require riscv.Utility.Encode.
Require Import Ex.RvCore.FormalSpec Ex.RvCore.Machine.
Require Import Ex.External.BzeenoSpec Ex.External.BzeenoFormalSim.
Require Import Ex.External.BzeenoBaselineADDI.
Require Import riscv.Utility.Words32Naive riscv.Utility.DefaultMemImpl32.
Require Import riscv.Utility.MkMachineWidth.
Require riscv.Spec.Execute riscv.Spec.ExecuteI.
Require Import riscv.Utility.Utility.
Require riscv.Utility.Monads.
Require Import coqutil.Map.Z_keyed_SortedListMap.
Require Import coqutil.Word.Interface.

Import ListNotations.
Local Open Scope Z_scope.

Module BzeenoBaselineDataOps.
  Import BzeenoBaselineADDI.

  Definition enc_i (i : Decode.InstructionI) : Z :=
    Encode.encode (Decode.IInstruction i).

  Definition opcode_of (inst : Z) : Z := inst mod 2 ^ 7.
  Definition funct3_of (inst : Z) : Z := (inst / 2 ^ 12) mod 2 ^ 3.
  Definition funct7_of (inst : Z) : Z := (inst / 2 ^ 25) mod 2 ^ 7.

  Definition rtl_control_of (i : Decode.InstructionI) : State :=
    let inst := enc_i i in
    control_dataop_outputs (opcode_of inst) (funct3_of inst) (funct7_of inst).

  Definition rtl_imm_of (i : Decode.InstructionI) : SZ :=
    let inst := enc_i i in
    imm_dataop_value inst (opcode_of inst).

  (**
      The RV32I base set has 40 common instructions.  This file covers the
      21 integer data-operation instructions:

      - U-type data movement/arithmetic: LUI, AUIPC;
      - I-type ALU: ADDI, SLTI, SLTIU, XORI, ORI, ANDI, SLLI, SRLI, SRAI;
      - R-type ALU: ADD, SUB, SLL, SLT, SLTU, XOR, SRL, SRA, OR, AND.

      Load/store, branch, jump, fence, and system instructions are intentionally
      excluded from this group because they require memory side effects or PC
      control-flow invariants.
   *)
  Definition data_ops : list Decode.InstructionI :=
    [ Decode.Lui 1 4096;
      Decode.Auipc 1 4096;
      Decode.Addi 1 0 1;
      Decode.Slti 1 0 1;
      Decode.Sltiu 1 0 1;
      Decode.Xori 1 0 1;
      Decode.Ori 1 0 1;
      Decode.Andi 1 0 1;
      Decode.Slli 1 0 1;
      Decode.Srli 1 0 1;
      Decode.Srai 1 0 1;
      Decode.Add 1 0 0;
      Decode.Sub 1 0 0;
      Decode.Sll 1 0 0;
      Decode.Slt 1 0 0;
      Decode.Sltu 1 0 0;
      Decode.Xor 1 0 0;
      Decode.Srl 1 0 0;
      Decode.Sra 1 0 0;
      Decode.Or 1 0 0;
      Decode.And 1 0 0 ].

  Example data_ops_count :
    length data_ops = 21%nat.
  Proof. reflexivity. Qed.

  Definition decodes_as (i : Decode.InstructionI) : Prop :=
    Decode.decode Decode.RV32I (enc_i i) = Decode.IInstruction i.

  Example decode_lui :
    decodes_as (Decode.Lui 1 4096).
  Proof. vm_compute. reflexivity. Qed.

  Example decode_auipc :
    decodes_as (Decode.Auipc 1 4096).
  Proof. vm_compute. reflexivity. Qed.

  Example decode_addi :
    decodes_as (Decode.Addi 1 0 1).
  Proof. vm_compute. reflexivity. Qed.

  Example decode_slti :
    decodes_as (Decode.Slti 1 0 1).
  Proof. vm_compute. reflexivity. Qed.

  Example decode_sltiu :
    decodes_as (Decode.Sltiu 1 0 1).
  Proof. vm_compute. reflexivity. Qed.

  Example decode_xori :
    decodes_as (Decode.Xori 1 0 1).
  Proof. vm_compute. reflexivity. Qed.

  Example decode_ori :
    decodes_as (Decode.Ori 1 0 1).
  Proof. vm_compute. reflexivity. Qed.

  Example decode_andi :
    decodes_as (Decode.Andi 1 0 1).
  Proof. vm_compute. reflexivity. Qed.

  Example decode_slli :
    decodes_as (Decode.Slli 1 0 1).
  Proof. vm_compute. reflexivity. Qed.

  Example decode_srli :
    decodes_as (Decode.Srli 1 0 1).
  Proof. vm_compute. reflexivity. Qed.

  Example decode_srai :
    decodes_as (Decode.Srai 1 0 1).
  Proof. vm_compute. reflexivity. Qed.

  Example decode_add :
    decodes_as (Decode.Add 1 0 0).
  Proof. vm_compute. reflexivity. Qed.

  Example decode_sub :
    decodes_as (Decode.Sub 1 0 0).
  Proof. vm_compute. reflexivity. Qed.

  Example decode_sll :
    decodes_as (Decode.Sll 1 0 0).
  Proof. vm_compute. reflexivity. Qed.

  Example decode_slt :
    decodes_as (Decode.Slt 1 0 0).
  Proof. vm_compute. reflexivity. Qed.

  Example decode_sltu :
    decodes_as (Decode.Sltu 1 0 0).
  Proof. vm_compute. reflexivity. Qed.

  Example decode_xor :
    decodes_as (Decode.Xor 1 0 0).
  Proof. vm_compute. reflexivity. Qed.

  Example decode_srl :
    decodes_as (Decode.Srl 1 0 0).
  Proof. vm_compute. reflexivity. Qed.

  Example decode_sra :
    decodes_as (Decode.Sra 1 0 0).
  Proof. vm_compute. reflexivity. Qed.

  Example decode_or :
    decodes_as (Decode.Or 1 0 0).
  Proof. vm_compute. reflexivity. Qed.

  Example decode_and :
    decodes_as (Decode.And 1 0 0).
  Proof. vm_compute. reflexivity. Qed.

  Theorem all_data_ops_decode :
    Forall decodes_as data_ops.
  Proof.
    repeat constructor;
      vm_compute;
      reflexivity.
  Qed.

  Example rtl_control_lui :
    rtl_control_of (Decode.Lui 1 4096) =
      control_data_outputs 1 0 0 0 0 0 12.
  Proof. vm_compute. reflexivity. Qed.

  Example rtl_control_auipc :
    rtl_control_of (Decode.Auipc 1 4096) =
      control_data_outputs 1 1 1 0 0 0 0.
  Proof. vm_compute. reflexivity. Qed.

  Example rtl_control_addi :
    rtl_control_of (Decode.Addi 1 0 1) = control_addi_outputs.
  Proof. vm_compute. reflexivity. Qed.

  Example rtl_control_slti :
    rtl_control_of (Decode.Slti 1 0 1) =
      control_data_outputs 1 1 0 1 1 1 0.
  Proof. vm_compute. reflexivity. Qed.

  Example rtl_control_sltiu :
    rtl_control_of (Decode.Sltiu 1 0 1) =
      control_data_outputs 1 1 0 1 0 1 0.
  Proof. vm_compute. reflexivity. Qed.

  Example rtl_control_xori :
    rtl_control_of (Decode.Xori 1 0 1) =
      control_data_outputs 1 1 0 0 0 0 4.
  Proof. vm_compute. reflexivity. Qed.

  Example rtl_control_ori :
    rtl_control_of (Decode.Ori 1 0 1) =
      control_data_outputs 1 1 0 0 0 0 10.
  Proof. vm_compute. reflexivity. Qed.

  Example rtl_control_andi :
    rtl_control_of (Decode.Andi 1 0 1) =
      control_data_outputs 1 1 0 0 0 0 2.
  Proof. vm_compute. reflexivity. Qed.

  Example rtl_control_slli :
    rtl_control_of (Decode.Slli 1 0 1) =
      control_data_outputs 1 0 0 0 0 0 5.
  Proof. vm_compute. reflexivity. Qed.

  Example rtl_control_srli :
    rtl_control_of (Decode.Srli 1 0 1) =
      control_data_outputs 1 0 0 0 0 0 13.
  Proof. vm_compute. reflexivity. Qed.

  Example rtl_control_srai :
    rtl_control_of (Decode.Srai 1 0 1) =
      control_data_outputs 1 0 0 0 0 0 29.
  Proof. vm_compute. reflexivity. Qed.

  Example rtl_control_add :
    rtl_control_of (Decode.Add 1 0 0) =
      control_data_outputs 0 0 0 0 0 0 0.
  Proof. vm_compute. reflexivity. Qed.

  Example rtl_control_sub :
    rtl_control_of (Decode.Sub 1 0 0) =
      control_data_outputs 0 0 0 0 0 0 8.
  Proof. vm_compute. reflexivity. Qed.

  Example rtl_control_sll :
    rtl_control_of (Decode.Sll 1 0 0) =
      control_data_outputs 0 0 0 0 0 0 5.
  Proof. vm_compute. reflexivity. Qed.

  Example rtl_control_slt :
    rtl_control_of (Decode.Slt 1 0 0) =
      control_data_outputs 0 0 0 1 1 0 0.
  Proof. vm_compute. reflexivity. Qed.

  Example rtl_control_sltu :
    rtl_control_of (Decode.Sltu 1 0 0) =
      control_data_outputs 0 0 0 1 0 0 0.
  Proof. vm_compute. reflexivity. Qed.

  Example rtl_control_xor :
    rtl_control_of (Decode.Xor 1 0 0) =
      control_data_outputs 0 0 0 0 0 0 4.
  Proof. vm_compute. reflexivity. Qed.

  Example rtl_control_srl :
    rtl_control_of (Decode.Srl 1 0 0) =
      control_data_outputs 0 0 0 0 0 0 13.
  Proof. vm_compute. reflexivity. Qed.

  Example rtl_control_sra :
    rtl_control_of (Decode.Sra 1 0 0) =
      control_data_outputs 0 0 0 0 0 0 29.
  Proof. vm_compute. reflexivity. Qed.

  Example rtl_control_or :
    rtl_control_of (Decode.Or 1 0 0) =
      control_data_outputs 0 0 0 0 0 0 10.
  Proof. vm_compute. reflexivity. Qed.

  Example rtl_control_and :
    rtl_control_of (Decode.And 1 0 0) =
      control_data_outputs 0 0 0 0 0 0 2.
  Proof. vm_compute. reflexivity. Qed.

  Theorem all_data_ops_reach_parameterized_control :
    Forall
      (fun i => rtl_control_of i <> control_nop_outputs)
      data_ops.
  Proof.
    repeat constructor;
      vm_compute;
      congruence.
  Qed.

  Example rtl_imm_lui :
    rtl_imm_of (Decode.Lui 1 4096) = #{4096,32,false}.
  Proof. vm_compute. reflexivity. Qed.

  Example rtl_imm_auipc :
    rtl_imm_of (Decode.Auipc 1 4096) = #{4096,32,false}.
  Proof. vm_compute. reflexivity. Qed.

  Example rtl_imm_addi :
    rtl_imm_of (Decode.Addi 1 0 1) = #{1,32,false}.
  Proof. vm_compute. reflexivity. Qed.

  Example rtl_imm_shift :
    rtl_imm_of (Decode.Srai 1 0 1) = #{1,32,false}.
  Proof. vm_compute. reflexivity. Qed.

  Local Opaque FormalSpec.zeroed FormalSpec.zeroed_until.

  Definition exec0 : FormalSpec.State :=
    FormalSpec.initial_state FormalSpec.zeroed.

  Definition exec_of (i : Decode.InstructionI) : option unit * FormalSpec.State :=
    Execute.execute (Decode.IInstruction i) exec0.

  Definition exec_data_fields (i : Decode.InstructionI) (expected_x1 : Z) : Prop :=
    fst (exec_of i) = Some tt /\
    BzeenoFormalSim.formal_reg_value (getRegs (snd (exec_of i))) 1 =
      expected_x1.

  Ltac prove_exec_data :=
    unfold exec_data_fields, exec_of, exec0;
    cbn [Execute.execute];
    unfold ExecuteI.execute;
    cbn;
    unfold Monads.OStateOperations.put, BzeenoFormalSim.formal_reg_value;
    cbn;
    repeat split; reflexivity.

  Example exec_lui : exec_data_fields (Decode.Lui 1 4096) 4096.
  Proof. prove_exec_data. Qed.

  Example exec_auipc : exec_data_fields (Decode.Auipc 1 4096) 4096.
  Proof. prove_exec_data. Qed.

  Example exec_addi : exec_data_fields (Decode.Addi 1 0 1) 1.
  Proof. prove_exec_data. Qed.

  Example exec_slti : exec_data_fields (Decode.Slti 1 0 1) 1.
  Proof. prove_exec_data. Qed.

  Example exec_sltiu : exec_data_fields (Decode.Sltiu 1 0 1) 1.
  Proof. prove_exec_data. Qed.

  Example exec_xori : exec_data_fields (Decode.Xori 1 0 1) 1.
  Proof. prove_exec_data. Qed.

  Example exec_ori : exec_data_fields (Decode.Ori 1 0 1) 1.
  Proof. prove_exec_data. Qed.

  Example exec_andi : exec_data_fields (Decode.Andi 1 0 1) 0.
  Proof. prove_exec_data. Qed.

  Example exec_slli : exec_data_fields (Decode.Slli 1 0 1) 0.
  Proof. prove_exec_data. Qed.

  Example exec_srli : exec_data_fields (Decode.Srli 1 0 1) 0.
  Proof. prove_exec_data. Qed.

  Example exec_srai : exec_data_fields (Decode.Srai 1 0 1) 0.
  Proof. prove_exec_data. Qed.

  Example exec_add : exec_data_fields (Decode.Add 1 0 0) 0.
  Proof. prove_exec_data. Qed.

  Example exec_sub : exec_data_fields (Decode.Sub 1 0 0) 0.
  Proof. prove_exec_data. Qed.

  Example exec_sll : exec_data_fields (Decode.Sll 1 0 0) 0.
  Proof. prove_exec_data. Qed.

  Example exec_slt : exec_data_fields (Decode.Slt 1 0 0) 0.
  Proof. prove_exec_data. Qed.

  Example exec_sltu : exec_data_fields (Decode.Sltu 1 0 0) 0.
  Proof. prove_exec_data. Qed.

  Example exec_xor : exec_data_fields (Decode.Xor 1 0 0) 0.
  Proof. prove_exec_data. Qed.

  Example exec_srl : exec_data_fields (Decode.Srl 1 0 0) 0.
  Proof. prove_exec_data. Qed.

  Example exec_sra : exec_data_fields (Decode.Sra 1 0 0) 0.
  Proof. prove_exec_data. Qed.

  Example exec_or : exec_data_fields (Decode.Or 1 0 0) 0.
  Proof. prove_exec_data. Qed.

  Example exec_and : exec_data_fields (Decode.And 1 0 0) 0.
  Proof. prove_exec_data. Qed.
End BzeenoBaselineDataOps.
