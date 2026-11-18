(** Original ADD values are computed at unique ISA execution-chain cuts.
    Retired tokens stay in the reference ledger while their hardware slots
    can still hold them; moving the commit boundary does not lose the value. *)
From Coq Require Import ZArith List.
Require Import Ex.External.CPUReferenceValues Ex.External.CPUReferenceCuts
 Ex.External.CPUGeneratedJointTemplate Ex.External.CPUOriginalISAReference
 Ex.RvCore.FormalSpec Ex.RvCore.Machine coqutil.Word.Interface coqutil.Word.Properties
 coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte riscv.Utility.Utility.
Import ListNotations CPUReferenceValues CPUReferenceCuts CPUGeneratedJointTemplate CPUOriginalISAReference.
Module CPUISAAddReferenceValues.
Section ISA.
Context {word:Interface.word 32}{BW:Bitwidth 32}{Registers:map.map Z word}{Mem:map.map word byte}.
Context {Token:Type}.
Variables token_pc token_word:Token->Z.
Variable token_key:Token->nat.

Definition add_value token(before:FormalSpec.State):option Z:=
 match Decode.decode Decode.RV32I(token_word token)with
 | Decode.IInstruction(Decode.Add _ rs1 rs2)=>
   match Machine.getRegister rs1 before,Machine.getRegister rs2 before with
   | (Some x,_),(Some y,_)=>Some(word.unsigned(Utility.add x y))
   | _,_=>None end
 | _=>None end.
Definition values(initial:FormalSpec.State)ledger token:=
 lookup(instruction_effect token_pc token_word)token_key add_value initial ledger token.

Theorem add_value_from_original_reads token before rd rs1 rs2 x y:
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Add rd rs1 rs2) ->
 Machine.getRegister rs1 before=(Some x,before) ->Machine.getRegister rs2 before=(Some y,before) ->
 add_value token before=Some(word.unsigned(Utility.add x y)).
Proof. intros HD HX HY;unfold add_value;now rewrite HD,HX,HY. Qed.

Theorem at_cut initial ledger index token before rd rs1 rs2 x y:
 NoDup(map token_key ledger) ->BeforeInstruction token_pc token_word initial ledger index token before ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Add rd rs1 rs2) ->
 Machine.getRegister rs1 before=(Some x,before) ->Machine.getRegister rs2 before=(Some y,before) ->
 values initial ledger token=Some(word.unsigned(Utility.add x y)).
Proof.
 intros HN HC HD HX HY;unfold values.
 rewrite(at_reference_cut(instruction_effect token_pc token_word)token_key add_value initial ledger index token before HN HC).
 exact(add_value_from_original_reads token before rd rs1 rs2 x y HD HX HY).
Qed.

Theorem at_pending_head initial retired before token pending rd rs1 rs2 x y:
 EffectChain(instruction_effect token_pc token_word)initial retired before ->
 Forall(fun earlier=>token_key earlier<>token_key token)retired ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Add rd rs1 rs2) ->
 Machine.getRegister rs1 before=(Some x,before) ->Machine.getRegister rs2 before=(Some y,before) ->
 values initial(retired++token::pending)token=Some(word.unsigned(Utility.add x y)).
Proof.
 intros HC HK HD HX HY;unfold values.
 rewrite(committed_prefix(instruction_effect token_pc token_word)token_key add_value initial retired before(token::pending)token HC HK),
  (at_head(instruction_effect token_pc token_word)token_key add_value before token pending).
 exact(add_value_from_original_reads token before rd rs1 rs2 x y HD HX HY).
Qed.

Theorem moving_commit_boundary initial retired committed pending token:
 values initial(retired++(committed++pending))token=
 values initial((retired++committed)++pending)token.
Proof. now rewrite app_assoc. Qed.

Theorem extending_ledger_keeps_existing initial ledger accepted token:
 In(token_key token)(map token_key ledger) ->
 values initial(ledger++accepted)token=values initial ledger token.
Proof. unfold values;apply append_keeps_existing. Qed.
End ISA.
End CPUISAAddReferenceValues.
Print Assumptions CPUISAAddReferenceValues.add_value_from_original_reads.
Print Assumptions CPUISAAddReferenceValues.at_cut.
Print Assumptions CPUISAAddReferenceValues.at_pending_head.
Print Assumptions CPUISAAddReferenceValues.moving_commit_boundary.
Print Assumptions CPUISAAddReferenceValues.extending_ledger_keeps_existing.
