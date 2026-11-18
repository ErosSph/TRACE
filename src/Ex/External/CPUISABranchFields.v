(** Original ISA BEQ fields. No CPU state or hardware invariant. *)
From Coq Require Import ZArith List Bool.
Require Import riscv.Proofs.DecodeByExtension Ex.External.CPUInstructionFields.
Import CPUInstructionFields.
Local Open Scope Z_scope.
Module CPUISABranchFields.
(** The original decoder's B-type immediate, before sign extension. *)
Definition raw code:=
 Z.lor(Z.lor(Z.lor(Z.shiftl(BitOps.bitSlice code 31 32)12)
 (Z.shiftl(BitOps.bitSlice code 25 31)5))(Z.shiftl(BitOps.bitSlice code 8 12)1))
 (Z.shiftl(BitOps.bitSlice code 7 8)11).
Definition immediate code:=BitOps.signExtend 13(raw code).

Lemma decode_i_beq_fields code rs1 rs2 imm:
 decodeI 32 code=Decode.Beq rs1 rs2 imm ->
 field_reference code Opcode=99 /\field_reference code Funct3=0 /\
 field_reference code Rs1=rs1 /\field_reference code Rs2=rs2 /\immediate code=imm.
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
 - change(BitOps.bitSlice code 12 15=0).
   match goal with HJ:Z.eqb(BitOps.bitSlice code 12 15)Decode.funct3_BEQ=true|-_=>apply Z.eqb_eq in HJ;exact HJ end.
Qed.

Theorem original_decode_beq_fields code rs1 rs2 imm:
 Decode.decode Decode.RV32I code=Decode.IInstruction(Decode.Beq rs1 rs2 imm) ->
 field_reference code Opcode=99 /\field_reference code Funct3=0 /\
 field_reference code Rs1=rs1 /\field_reference code Rs2=rs2 /\immediate code=imm.
Proof.
 rewrite <-decode_seq_correct;unfold decode_seq;cbn[bitwidth supportsM supportsA supportsF].
 destruct(isValidI(decodeI 32 code))eqn:HV.
 - intro H;injection H as H;now apply(decode_i_beq_fields code rs1 rs2 imm).
 - destruct(isValidCSR(decodeCSR 32 code));discriminate.
Qed.
End CPUISABranchFields.
Print Assumptions CPUISABranchFields.decode_i_beq_fields.
Print Assumptions CPUISABranchFields.original_decode_beq_fields.
