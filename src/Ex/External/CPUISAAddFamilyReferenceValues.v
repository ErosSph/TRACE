(** Values at original ISA execution cuts for ADD and ADDI. No RTL roots,
    expected CPU states or CPU invariant are used to compute these values. *)
From Coq Require Import ZArith List.
Require Import Ex.External.CPUReferenceValues Ex.External.CPUReferenceCuts
 Ex.External.CPUGeneratedJointTemplate Ex.External.CPUOriginalISAReference
 Ex.RvCore.FormalSpec Ex.RvCore.Machine coqutil.Word.Interface coqutil.Word.Bitwidth
 coqutil.Map.Interface coqutil.Byte riscv.Utility.Utility.
Import ListNotations CPUReferenceValues CPUReferenceCuts CPUGeneratedJointTemplate CPUOriginalISAReference.
Module CPUISAAddFamilyReferenceValues.
Section ISA.
Context {word:Interface.word 32}{BW:Bitwidth 32}{Registers:map.map Z word}{Mem:map.map word byte}.
Context {Token:Type}.
Variables token_pc token_word:Token->Z.
Variable token_key:Token->nat.

Definition computed_value token(before:FormalSpec.State):option Z:=
 match Decode.decode Decode.RV32I(token_word token)with
 | Decode.IInstruction(Decode.Add _ rs1 rs2)=>
   match Machine.getRegister rs1 before,Machine.getRegister rs2 before with
   | (Some x,_),(Some y,_)=>Some(word.unsigned(Utility.add x y))
   | _,_=>None end
 | Decode.IInstruction(Decode.Addi _ rs imm)=>
   match Machine.getRegister rs before with
   | (Some x,_)=>Some(word.unsigned(Utility.add x(Utility.ZToReg imm)))
   | _=>None end
 | _=>None end.
Definition values(initial:FormalSpec.State)ledger token:=
 lookup(instruction_effect token_pc token_word)token_key computed_value initial ledger token.

Theorem computed_add token before rd rs1 rs2 x y:
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Add rd rs1 rs2) ->
 Machine.getRegister rs1 before=(Some x,before) ->Machine.getRegister rs2 before=(Some y,before) ->
 computed_value token before=Some(word.unsigned(Utility.add x y)).
Proof. intros HD HX HY;unfold computed_value;now rewrite HD,HX,HY. Qed.

Theorem computed_addi token before rd rs imm x:
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Addi rd rs imm) ->
 Machine.getRegister rs before=(Some x,before) ->
 computed_value token before=Some(word.unsigned(Utility.add x(Utility.ZToReg imm))).
Proof. intros HD HX;unfold computed_value;now rewrite HD,HX. Qed.

Theorem at_cut initial ledger index token before:
 NoDup(map token_key ledger) ->BeforeInstruction token_pc token_word initial ledger index token before ->
 values initial ledger token=computed_value token before.
Proof. intros HN HC;unfold values;now apply(at_reference_cut
 (instruction_effect token_pc token_word)token_key computed_value initial ledger index token before). Qed.

Theorem addi_at_cut initial ledger index token before rd rs imm x:
 NoDup(map token_key ledger) ->BeforeInstruction token_pc token_word initial ledger index token before ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Addi rd rs imm) ->
 Machine.getRegister rs before=(Some x,before) ->
 values initial ledger token=Some(word.unsigned(Utility.add x(Utility.ZToReg imm))).
Proof. intros HN HC HD HX;rewrite(at_cut initial ledger index token before HN HC).
 exact(computed_addi token before rd rs imm x HD HX). Qed.

Theorem moving_commit_boundary initial retired committed pending token:
 values initial(retired++(committed++pending))token=
 values initial((retired++committed)++pending)token.
Proof. now rewrite app_assoc. Qed.

Theorem extending_ledger_keeps_existing initial ledger accepted token:
 In(token_key token)(map token_key ledger) ->
 values initial(ledger++accepted)token=values initial ledger token.
Proof. unfold values;apply append_keeps_existing. Qed.
End ISA.
End CPUISAAddFamilyReferenceValues.
Print Assumptions CPUISAAddFamilyReferenceValues.computed_add.
Print Assumptions CPUISAAddFamilyReferenceValues.computed_addi.
Print Assumptions CPUISAAddFamilyReferenceValues.at_cut.
Print Assumptions CPUISAAddFamilyReferenceValues.addi_at_cut.
Print Assumptions CPUISAAddFamilyReferenceValues.moving_commit_boundary.
Print Assumptions CPUISAAddFamilyReferenceValues.extending_ledger_keeps_existing.
