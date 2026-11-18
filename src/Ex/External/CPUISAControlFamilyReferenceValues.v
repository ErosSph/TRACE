(** An independent extension of the checked ADD/ADDI reference values.
    JAL's link is read from the ORIGINAL reference machine's next PC.
    Equating it with PC+4 requires a separately proved ISA state relation.
    No RTL state or old CPU invariant is used to choose a reference value. *)
From Coq Require Import ZArith List.
Require Import Ex.External.CPUReferenceValues Ex.External.CPUReferenceCuts
 Ex.External.CPUGeneratedJointTemplate Ex.External.CPUOriginalISAReference
 Ex.External.CPUISAAddFamilyReferenceValues Ex.RvCore.FormalSpec
 coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte
 riscv.Utility.Utility.
Import ListNotations CPUReferenceValues CPUReferenceCuts CPUGeneratedJointTemplate CPUOriginalISAReference.

Module CPUISAControlFamilyReferenceValues.
Section ISA.
Context {word:Interface.word 32}{BW:Bitwidth 32}{Registers:map.map Z word}{Mem:map.map word byte}.
Context {Token:Type}.
Variables token_pc token_word:Token->Z.
Variable token_key:Token->nat.

Definition computed_value token(before:FormalSpec.State):option Z:=
 match Decode.decode Decode.RV32I(token_word token)with
 |Decode.IInstruction(Decode.Jal _ _)=>Some(word.unsigned(getNextPc before))
 |_=>CPUISAAddFamilyReferenceValues.computed_value token_word token before
 end.
Definition values(initial:FormalSpec.State)ledger token:=
 lookup(instruction_effect token_pc token_word)token_key computed_value initial ledger token.
Definition ControlFamily token:Prop:=
 (exists rd rs1 rs2,Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Add rd rs1 rs2)) \/
 (exists rd rs imm,Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Addi rd rs imm)) \/
 (exists rd imm,Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Jal rd imm)).

Theorem computed_add token before rd rs1 rs2 x y:
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Add rd rs1 rs2) ->
 Machine.getRegister rs1 before=(Some x,before) ->
 Machine.getRegister rs2 before=(Some y,before) ->
 computed_value token before=Some(word.unsigned(Utility.add x y)).
Proof. intros HD HX HY;unfold computed_value;rewrite HD.
 exact(CPUISAAddFamilyReferenceValues.computed_add token_word token before rd rs1 rs2 x y HD HX HY).
Qed.

Theorem computed_addi token before rd rs imm x:
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Addi rd rs imm) ->
 Machine.getRegister rs before=(Some x,before) ->
 computed_value token before=Some(word.unsigned(Utility.add x(Utility.ZToReg imm))).
Proof. intros HD HX;unfold computed_value;rewrite HD.
 exact(CPUISAAddFamilyReferenceValues.computed_addi token_word token before rd rs imm x HD HX).
Qed.

Theorem computed_jal token before rd imm:
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Jal rd imm) ->
 computed_value token before=Some(word.unsigned(getNextPc before)).
Proof. intro HD;unfold computed_value;now rewrite HD. Qed.

Theorem computed_value_implies_family token before value:
 computed_value token before=Some value ->ControlFamily token.
Proof.
 unfold computed_value,CPUISAAddFamilyReferenceValues.computed_value;
 destruct(Decode.decode Decode.RV32I(token_word token))eqn:HD;try discriminate;
 destruct iInstruction;try discriminate;intro H;unfold ControlFamily;
 first[left;repeat eexists;exact HD|right;left;repeat eexists;exact HD|
 right;right;repeat eexists;exact HD].
Qed.

Theorem at_cut initial ledger index token before:
 NoDup(map token_key ledger) ->BeforeInstruction token_pc token_word initial ledger index token before ->
 values initial ledger token=computed_value token before.
Proof. intros HN HC;unfold values;now apply(at_reference_cut
 (instruction_effect token_pc token_word)token_key computed_value initial ledger index token before). Qed.

Theorem jal_at_cut initial ledger index token before rd imm:
 NoDup(map token_key ledger) ->BeforeInstruction token_pc token_word initial ledger index token before ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Jal rd imm) ->
 values initial ledger token=Some(word.unsigned(getNextPc before)).
Proof. intros HN HC HD;rewrite(at_cut initial ledger index token before HN HC).
 exact(computed_jal token before rd imm HD). Qed.

Theorem moving_commit_boundary initial retired committed pending token:
 values initial(retired++(committed++pending))token=
 values initial((retired++committed)++pending)token.
Proof. now rewrite app_assoc. Qed.

Theorem extending_ledger_keeps_existing initial ledger accepted token:
 In(token_key token)(map token_key ledger) ->
 values initial(ledger++accepted)token=values initial ledger token.
Proof. unfold values;apply append_keeps_existing. Qed.
End ISA.
End CPUISAControlFamilyReferenceValues.
Print Assumptions CPUISAControlFamilyReferenceValues.computed_add.
Print Assumptions CPUISAControlFamilyReferenceValues.computed_addi.
Print Assumptions CPUISAControlFamilyReferenceValues.computed_jal.
Print Assumptions CPUISAControlFamilyReferenceValues.computed_value_implies_family.
Print Assumptions CPUISAControlFamilyReferenceValues.at_cut.
Print Assumptions CPUISAControlFamilyReferenceValues.jal_at_cut.
Print Assumptions CPUISAControlFamilyReferenceValues.moving_commit_boundary.
Print Assumptions CPUISAControlFamilyReferenceValues.extending_ledger_keeps_existing.
