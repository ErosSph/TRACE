(** Scope B: arbitrary mixtures of decoded RV32I data operations.
    This is a fetch/scope theorem, NOT a CPU invariant or progress proof. *)
From Coq Require Import ZArith List.
Require Import Ex.RvCore.FormalSpec
 Ex.External.CV32E40PReq39Trace Ex.External.CV32E40PReq41Instruction
 Ex.External.CV32E40PAddiNopROM Ex.External.CV32E40PAddiNopISAInvariant.
Require Import coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte.
Import CV32E40PReq39Trace CV32E40PReq41Instruction
 CV32E40PAddiNopROM CV32E40PAddiNopISAInvariant.
Local Open Scope Z_scope.
Module CV32E40PDataOpProgramScope.
 Definition dataop21b (i : Decode.InstructionI) : bool := match i with
 | Decode.Lui _ _ | Decode.Auipc _ _
 | Decode.Addi _ _ _ | Decode.Slti _ _ _ | Decode.Sltiu _ _ _
 | Decode.Xori _ _ _ | Decode.Ori _ _ _ | Decode.Andi _ _ _
 | Decode.Slli _ _ _ | Decode.Srli _ _ _ | Decode.Srai _ _ _
 | Decode.Add _ _ _ | Decode.Sub _ _ _ | Decode.Sll _ _ _
 | Decode.Slt _ _ _ | Decode.Sltu _ _ _ | Decode.Xor _ _ _
 | Decode.Srl _ _ _ | Decode.Sra _ _ _ | Decode.Or _ _ _ | Decode.And _ _ _ => true
 | _ => false end.
 Definition DataOp21 i : Prop := dataop21b i = true.
 Definition GoodDataOp code : Prop := exists i,
   DataOp21 i /\ Decode.decode Decode.RV32I (code mod 2^32) = Decode.IInstruction i.
 Definition DataOpProgram image : Prop := Forall GoodDataOp image.
 Theorem dataop21_family i : DataOp21 i <-> InFamily FamilyDataOp i.
 Proof. unfold DataOp21, InFamily. destruct i; cbn [dataop21b family_of]; intuition discriminate. Qed.
 Theorem addi_scope_included code : GoodADDI code -> GoodDataOp code.
 Proof.
   intros (rd & rs & imm & Hrd & Hrs & Himm & HD).
   exists (Decode.Addi rd rs imm). split; [reflexivity|exact HD].
 Qed.
 Lemma nop_in_scope : GoodDataOp nop.
 Proof. apply addi_scope_included. exact nop_is_addi. Qed.
 Lemma nth_in_scope image n : DataOpProgram image -> GoodDataOp (nth n image nop).
 Proof.
   intros H. induction H in n |- *; destruct n; cbn; auto using nop_in_scope.
 Qed.
 Theorem arbitrary_address_fetch_scope image pc : DataOpProgram image ->
   GoodDataOp (instruction_from_image image pc).
 Proof.
   intros H. unfold instruction_from_image.
   destruct (andb (Z.leb 0 pc) (Z.eqb (pc mod 4) 0)); auto using nth_in_scope, nop_in_scope.
 Qed.
 Section ISA.
 Context {word : Interface.word 32} {BW : Bitwidth 32}.
 Context {Registers : map.map Decode.Register word} {Mem : map.map word byte}.
 Context {word_ok : word.ok word} {registers_ok : map.ok Registers} {mem_ok : map.ok Mem}.
 #[local] Opaque nop_rom.
 Theorem scoped_current_instruction image (s : FormalSpec.State) :
   DataOpProgram image -> ISAInvariant image s ->
   exists i, DataOp21 i /\ CurrentInstruction s i.
 Proof.
   intros HP (HM & HA & HN).
   destruct (arbitrary_address_fetch_scope image (word.unsigned (getPc s)) HP)
     as (i & HI & HD). exists i. split; [exact HI|].
   constructor; [exact HA|].
   exists (LittleEndian.split 4 (instruction_from_image image (word.unsigned (getPc s)))).
   split.
   - rewrite HM. apply nop_rom_fetch. exact HA.
   - rewrite LittleEndian.combine_split. exact HD.
 Qed.
 End ISA.
 Print Assumptions scoped_current_instruction.
End CV32E40PDataOpProgramScope.
