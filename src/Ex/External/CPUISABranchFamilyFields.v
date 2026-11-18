(** Original ISA fields of the six conditional branches (generalises the
    accepted [CPUISABranchFields] BEQ lemma). No CPU state. *)
From Coq Require Import ZArith List Bool.
Require Import riscv.Proofs.DecodeByExtension Ex.External.CPUInstructionFields
 Ex.External.CPUISABranchFields Ex.External.CPUISABranchFamilyEffects.
Import CPUInstructionFields CPUISABranchFamilyEffects.
Local Open Scope Z_scope.
Module CPUISABranchFamilyFields.
Definition funct3 op:Z:=match op with BranchEq=>0|BranchNe=>1|BranchLt=>4|BranchGe=>5|BranchLtu=>6|BranchGeu=>7 end.

Lemma decode_i_Beq_fields code rs1 rs2 imm:
 decodeI 32 code=Decode.Beq rs1 rs2 imm ->
 field_reference code Opcode=99 /\field_reference code Funct3=funct3 BranchEq /\
 field_reference code Rs1=rs1 /\field_reference code Rs2=rs2 /\CPUISABranchFields.immediate code=imm.
Proof.
 unfold decodeI;cbv beta zeta.
 repeat match goal with|-context[if ?test then _ else _]=>destruct test eqn:? end;
 intro H;try discriminate.
 pose proof(f_equal(fun i=>match i with Decode.Beq r _ _=>r|_=>0 end)H)as H1.
 pose proof(f_equal(fun i=>match i with Decode.Beq _ r _=>r|_=>0 end)H)as H2.
 pose proof(f_equal(fun i=>match i with Decode.Beq _ _ v=>v|_=>0 end)H)as HI.
 cbv beta iota in H1,H2,HI.
 repeat match goal with
 | HB:andb _ _=true|-_=>apply andb_true_iff in HB;destruct HB
 end.
 split;[|split;[|split;[exact H1|split;[exact H2|exact HI]]]].
 - change(BitOps.bitSlice code 0 7=99).
   match goal with HJ:Z.eqb(BitOps.bitSlice code 0 7)Decode.opcode_BRANCH=true|-_=>apply Z.eqb_eq in HJ;exact HJ end.
 - change(BitOps.bitSlice code 12 15=funct3 BranchEq).
   match goal with HJ:Z.eqb(BitOps.bitSlice code 12 15)Decode.funct3_BEQ=true|-_=>apply Z.eqb_eq in HJ;exact HJ end.
Qed.
Lemma decode_i_Bne_fields code rs1 rs2 imm:
 decodeI 32 code=Decode.Bne rs1 rs2 imm ->
 field_reference code Opcode=99 /\field_reference code Funct3=funct3 BranchNe /\
 field_reference code Rs1=rs1 /\field_reference code Rs2=rs2 /\CPUISABranchFields.immediate code=imm.
Proof.
 unfold decodeI;cbv beta zeta.
 repeat match goal with|-context[if ?test then _ else _]=>destruct test eqn:? end;
 intro H;try discriminate.
 pose proof(f_equal(fun i=>match i with Decode.Bne r _ _=>r|_=>0 end)H)as H1.
 pose proof(f_equal(fun i=>match i with Decode.Bne _ r _=>r|_=>0 end)H)as H2.
 pose proof(f_equal(fun i=>match i with Decode.Bne _ _ v=>v|_=>0 end)H)as HI.
 cbv beta iota in H1,H2,HI.
 repeat match goal with
 | HB:andb _ _=true|-_=>apply andb_true_iff in HB;destruct HB
 end.
 split;[|split;[|split;[exact H1|split;[exact H2|exact HI]]]].
 - change(BitOps.bitSlice code 0 7=99).
   match goal with HJ:Z.eqb(BitOps.bitSlice code 0 7)Decode.opcode_BRANCH=true|-_=>apply Z.eqb_eq in HJ;exact HJ end.
 - change(BitOps.bitSlice code 12 15=funct3 BranchNe).
   match goal with HJ:Z.eqb(BitOps.bitSlice code 12 15)Decode.funct3_BNE=true|-_=>apply Z.eqb_eq in HJ;exact HJ end.
Qed.
Lemma decode_i_Blt_fields code rs1 rs2 imm:
 decodeI 32 code=Decode.Blt rs1 rs2 imm ->
 field_reference code Opcode=99 /\field_reference code Funct3=funct3 BranchLt /\
 field_reference code Rs1=rs1 /\field_reference code Rs2=rs2 /\CPUISABranchFields.immediate code=imm.
Proof.
 unfold decodeI;cbv beta zeta.
 repeat match goal with|-context[if ?test then _ else _]=>destruct test eqn:? end;
 intro H;try discriminate.
 pose proof(f_equal(fun i=>match i with Decode.Blt r _ _=>r|_=>0 end)H)as H1.
 pose proof(f_equal(fun i=>match i with Decode.Blt _ r _=>r|_=>0 end)H)as H2.
 pose proof(f_equal(fun i=>match i with Decode.Blt _ _ v=>v|_=>0 end)H)as HI.
 cbv beta iota in H1,H2,HI.
 repeat match goal with
 | HB:andb _ _=true|-_=>apply andb_true_iff in HB;destruct HB
 end.
 split;[|split;[|split;[exact H1|split;[exact H2|exact HI]]]].
 - change(BitOps.bitSlice code 0 7=99).
   match goal with HJ:Z.eqb(BitOps.bitSlice code 0 7)Decode.opcode_BRANCH=true|-_=>apply Z.eqb_eq in HJ;exact HJ end.
 - change(BitOps.bitSlice code 12 15=funct3 BranchLt).
   match goal with HJ:Z.eqb(BitOps.bitSlice code 12 15)Decode.funct3_BLT=true|-_=>apply Z.eqb_eq in HJ;exact HJ end.
Qed.
Lemma decode_i_Bge_fields code rs1 rs2 imm:
 decodeI 32 code=Decode.Bge rs1 rs2 imm ->
 field_reference code Opcode=99 /\field_reference code Funct3=funct3 BranchGe /\
 field_reference code Rs1=rs1 /\field_reference code Rs2=rs2 /\CPUISABranchFields.immediate code=imm.
Proof.
 unfold decodeI;cbv beta zeta.
 repeat match goal with|-context[if ?test then _ else _]=>destruct test eqn:? end;
 intro H;try discriminate.
 pose proof(f_equal(fun i=>match i with Decode.Bge r _ _=>r|_=>0 end)H)as H1.
 pose proof(f_equal(fun i=>match i with Decode.Bge _ r _=>r|_=>0 end)H)as H2.
 pose proof(f_equal(fun i=>match i with Decode.Bge _ _ v=>v|_=>0 end)H)as HI.
 cbv beta iota in H1,H2,HI.
 repeat match goal with
 | HB:andb _ _=true|-_=>apply andb_true_iff in HB;destruct HB
 end.
 split;[|split;[|split;[exact H1|split;[exact H2|exact HI]]]].
 - change(BitOps.bitSlice code 0 7=99).
   match goal with HJ:Z.eqb(BitOps.bitSlice code 0 7)Decode.opcode_BRANCH=true|-_=>apply Z.eqb_eq in HJ;exact HJ end.
 - change(BitOps.bitSlice code 12 15=funct3 BranchGe).
   match goal with HJ:Z.eqb(BitOps.bitSlice code 12 15)Decode.funct3_BGE=true|-_=>apply Z.eqb_eq in HJ;exact HJ end.
Qed.
Lemma decode_i_Bltu_fields code rs1 rs2 imm:
 decodeI 32 code=Decode.Bltu rs1 rs2 imm ->
 field_reference code Opcode=99 /\field_reference code Funct3=funct3 BranchLtu /\
 field_reference code Rs1=rs1 /\field_reference code Rs2=rs2 /\CPUISABranchFields.immediate code=imm.
Proof.
 unfold decodeI;cbv beta zeta.
 repeat match goal with|-context[if ?test then _ else _]=>destruct test eqn:? end;
 intro H;try discriminate.
 pose proof(f_equal(fun i=>match i with Decode.Bltu r _ _=>r|_=>0 end)H)as H1.
 pose proof(f_equal(fun i=>match i with Decode.Bltu _ r _=>r|_=>0 end)H)as H2.
 pose proof(f_equal(fun i=>match i with Decode.Bltu _ _ v=>v|_=>0 end)H)as HI.
 cbv beta iota in H1,H2,HI.
 repeat match goal with
 | HB:andb _ _=true|-_=>apply andb_true_iff in HB;destruct HB
 end.
 split;[|split;[|split;[exact H1|split;[exact H2|exact HI]]]].
 - change(BitOps.bitSlice code 0 7=99).
   match goal with HJ:Z.eqb(BitOps.bitSlice code 0 7)Decode.opcode_BRANCH=true|-_=>apply Z.eqb_eq in HJ;exact HJ end.
 - change(BitOps.bitSlice code 12 15=funct3 BranchLtu).
   match goal with HJ:Z.eqb(BitOps.bitSlice code 12 15)Decode.funct3_BLTU=true|-_=>apply Z.eqb_eq in HJ;exact HJ end.
Qed.
Lemma decode_i_Bgeu_fields code rs1 rs2 imm:
 decodeI 32 code=Decode.Bgeu rs1 rs2 imm ->
 field_reference code Opcode=99 /\field_reference code Funct3=funct3 BranchGeu /\
 field_reference code Rs1=rs1 /\field_reference code Rs2=rs2 /\CPUISABranchFields.immediate code=imm.
Proof.
 unfold decodeI;cbv beta zeta.
 repeat match goal with|-context[if ?test then _ else _]=>destruct test eqn:? end;
 intro H;try discriminate.
 pose proof(f_equal(fun i=>match i with Decode.Bgeu r _ _=>r|_=>0 end)H)as H1.
 pose proof(f_equal(fun i=>match i with Decode.Bgeu _ r _=>r|_=>0 end)H)as H2.
 pose proof(f_equal(fun i=>match i with Decode.Bgeu _ _ v=>v|_=>0 end)H)as HI.
 cbv beta iota in H1,H2,HI.
 repeat match goal with
 | HB:andb _ _=true|-_=>apply andb_true_iff in HB;destruct HB
 end.
 split;[|split;[|split;[exact H1|split;[exact H2|exact HI]]]].
 - change(BitOps.bitSlice code 0 7=99).
   match goal with HJ:Z.eqb(BitOps.bitSlice code 0 7)Decode.opcode_BRANCH=true|-_=>apply Z.eqb_eq in HJ;exact HJ end.
 - change(BitOps.bitSlice code 12 15=funct3 BranchGeu).
   match goal with HJ:Z.eqb(BitOps.bitSlice code 12 15)Decode.funct3_BGEU=true|-_=>apply Z.eqb_eq in HJ;exact HJ end.
Qed.
Lemma decode_i_branch_fields code op rs1 rs2 imm:
 decodeI 32 code=instruction op rs1 rs2 imm ->
 field_reference code Opcode=99 /\field_reference code Funct3=funct3 op /\
 field_reference code Rs1=rs1 /\field_reference code Rs2=rs2 /\CPUISABranchFields.immediate code=imm.
Proof. destruct op;[exact(decode_i_Beq_fields code rs1 rs2 imm)|exact(decode_i_Bne_fields code rs1 rs2 imm)
 |exact(decode_i_Blt_fields code rs1 rs2 imm)|exact(decode_i_Bge_fields code rs1 rs2 imm)
 |exact(decode_i_Bltu_fields code rs1 rs2 imm)|exact(decode_i_Bgeu_fields code rs1 rs2 imm)]. Qed.

Theorem original_decode_branch_fields code op rs1 rs2 imm:
 Decode.decode Decode.RV32I code=Decode.IInstruction(instruction op rs1 rs2 imm) ->
 field_reference code Opcode=99 /\field_reference code Funct3=funct3 op /\
 field_reference code Rs1=rs1 /\field_reference code Rs2=rs2 /\CPUISABranchFields.immediate code=imm.
Proof.
 rewrite <-decode_seq_correct;unfold decode_seq;cbn[bitwidth supportsM supportsA supportsF].
 destruct(isValidI(decodeI 32 code))eqn:HV.
 - intro H;injection H as H;now apply(decode_i_branch_fields code op rs1 rs2 imm).
 - destruct(isValidCSR(decodeCSR 32 code));discriminate.
Qed.

(** Every decoded conditional branch is one of the six. *)
Definition is_branch(i:Decode.InstructionI):bool:=match i with
 |Decode.Beq _ _ _|Decode.Bne _ _ _|Decode.Blt _ _ _|Decode.Bge _ _ _|Decode.Bltu _ _ _|Decode.Bgeu _ _ _=>true|_=>false end.
Theorem branch_cases i:is_branch i=true ->exists op rs1 rs2 imm,i=instruction op rs1 rs2 imm.
Proof. destruct i;try discriminate;intros _;
 [exists BranchEq|exists BranchNe|exists BranchLt|exists BranchGe|exists BranchLtu|exists BranchGeu];eexists _,_,_;reflexivity. Qed.
Theorem instruction_is_branch op rs1 rs2 imm:is_branch(instruction op rs1 rs2 imm)=true.
Proof. destruct op;reflexivity. Qed.
End CPUISABranchFamilyFields.
Print Assumptions CPUISABranchFamilyFields.decode_i_branch_fields.
Print Assumptions CPUISABranchFamilyFields.original_decode_branch_fields.
Print Assumptions CPUISABranchFamilyFields.branch_cases.
Print Assumptions CPUISABranchFamilyFields.instruction_is_branch.
