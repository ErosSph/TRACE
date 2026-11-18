(** Concrete CURRENT ID/EX fields for the mixed data-op invariant candidate.
    No future execution or post-state certificate occurs in this definition.
    Initialization is proved here; arbitrary-cycle preservation remains open. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Ex.RvCore.FormalSpec Ex.RvCore.Machine
 Ex.External.CV32E40PJointInterface Ex.External.CV32E40PDataOpProgramScope
 Ex.External.CV32E40PReq41Instruction Ex.External.CV32E40PReq39Trace
 Ex.External.CV32E40PAddiReachability Ex.External.CV32E40PAddiInitialRelated
 Ex.External.CV32E40PReq40StateRel Ex.External.CV32E40PAddiAdder.
Require Import coqutil.Word.Interface.
Import ExtendedSV CV32E40PJointInterface CV32E40PDataOpProgramScope
 CV32E40PReq41Instruction CV32E40PReq39Trace CV32E40PAddiReachability CV32E40PAddiInitialRelated
 CV32E40PReq40StateRel CV32E40PAddiAdder.
Local Open Scope Z_scope.
Module CV32E40PDataOpPendingRegisters.
 (** cv32e40p_pkg.sv ALU enum; decoder.sv LUI/AUIPC/OPIMM/OP arms. *)
 Definition scalar_opcode i : Z := match i with
 | Decode.Lui _ _ | Decode.Auipc _ _ | Decode.Addi _ _ _ | Decode.Add _ _ _ => 24
 | Decode.Sub _ _ _ => 25
 | Decode.Slti _ _ _ | Decode.Slt _ _ _ => 2
 | Decode.Sltiu _ _ _ | Decode.Sltu _ _ _ => 3
 | Decode.Xori _ _ _ | Decode.Xor _ _ _ => 47
 | Decode.Ori _ _ _ | Decode.Or _ _ _ => 46
 | Decode.Andi _ _ _ | Decode.And _ _ _ => 21
 | Decode.Slli _ _ _ | Decode.Sll _ _ _ => 39
 | Decode.Srli _ _ _ | Decode.Srl _ _ _ => 37
 | Decode.Srai _ _ _ | Decode.Sra _ _ _ => 36
 | _ => 0 end.
 Definition is_shift i := match i with
 | Decode.Slli _ _ _ | Decode.Sll _ _ _ | Decode.Srli _ _ _
 | Decode.Srl _ _ _ | Decode.Srai _ _ _ | Decode.Sra _ _ _ => true
 | _ => false end.
 Definition left_value (isa : FormalSpec.State) i : Z := match i with
 | Decode.Lui _ _ => 0
 | Decode.Auipc _ _ => word.unsigned (getPc isa)
 | _ => match source_registers i with
        | List.cons rs _ => word.unsigned (formal_register_word isa rs)
        | _ => 0 end end.
 Definition right_value (isa : FormalSpec.State) i : Z := match i with
 | Decode.Lui _ imm | Decode.Auipc _ imm | Decode.Addi _ _ imm
 | Decode.Slti _ _ imm | Decode.Sltiu _ _ imm | Decode.Xori _ _ imm
 | Decode.Ori _ _ imm | Decode.Andi _ _ imm
 | Decode.Slli _ _ imm | Decode.Srli _ _ imm | Decode.Srai _ _ imm =>
   imm mod 2^32
 | _ => match source_registers i with
        | List.cons _ (List.cons rs _) => word.unsigned (formal_register_word isa rs)
        | _ => 0 end end.
 Definition PendingRegisters s (isa : FormalSpec.State) i :=
   let rtl := trace_rtl (physical_state s) in
   DataOp21 i /\
   (exists rd, destination_register i = Some rd /\
     norm 6 (read_signal rtl 598%nat) = rd) /\
   norm 1 (read_signal rtl 599%nat) = 1 /\
   norm 1 (read_signal rtl 600%nat) = 1 /\
   norm 7 (read_signal rtl 601%nat) = scalar_opcode i /\
   norm 32 (read_signal rtl 589%nat) = left_value isa i /\
   (if is_shift i
    then norm 5 (read_signal rtl 590%nat) = norm 5 (right_value isa i)
    else norm 32 (read_signal rtl 590%nat) = right_value isa i).
 Definition ConcreteJoint image s isa fifo := DataOpJoint PendingRegisters image s isa fifo.
 Theorem reset_concrete_joint image : DataOpProgram image ->
   ConcreteJoint image reset_retirement (initial_isa image) List.nil.
 Proof. apply reset_dataop_joint. Qed.
 Theorem dataop_opcode_not_clip i : DataOp21 i -> scalar_opcode i <> 22 /\ scalar_opcode i <> 23.
 Proof. destruct i; cbn [DataOp21 dataop21b scalar_opcode]; intuition discriminate. Qed.
 Theorem shift_ignores_encoding_high_bits n :
   norm 5 (1024 + n) = norm 5 n.
 Proof.
   rewrite !norm_mod.
   change ((1024 + n) mod 32 = n mod 32).
   rewrite Z.add_mod by lia.
   change ((0 + n mod 32) mod 32 = n mod 32).
   rewrite Z.add_0_l, Z.mod_mod by lia. reflexivity.
 Qed.
Print Assumptions reset_concrete_joint.
End CV32E40PDataOpPendingRegisters.
