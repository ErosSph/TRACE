(** Original ISA JALR fields: opcode 103, funct3 0, rd, rs1 and the I-type
    immediate. No CPU state or hardware invariant. *)
From Coq Require Import ZArith List Bool.
Require Import riscv.Proofs.DecodeByExtension Ex.External.CPUInstructionFields.
Import CPUInstructionFields.
Local Open Scope Z_scope.
Module CPUISAJalrFields.
Definition immediate code:=BitOps.signExtend 12(BitOps.bitSlice code 20 32).

Lemma decode_i_jalr_fields code rd rs1 imm:
 decodeI 32 code=Decode.Jalr rd rs1 imm ->
 field_reference code Opcode=103 /\field_reference code Funct3=0 /\
 field_reference code Rd=rd /\field_reference code Rs1=rs1 /\immediate code=imm.
Proof.
 unfold decodeI;cbv beta zeta.
 repeat match goal with|-context[if ?test then _ else _]=>destruct test eqn:? end;
 intro H;try discriminate.
 pose proof(f_equal(fun i=>match i with Decode.Jalr r _ _=>r|_=>0 end)H)as H1.
 pose proof(f_equal(fun i=>match i with Decode.Jalr _ r _=>r|_=>0 end)H)as H2.
 pose proof(f_equal(fun i=>match i with Decode.Jalr _ _ v=>v|_=>0 end)H)as HI.
 cbv beta iota in H1,H2,HI.
 repeat match goal with
 | HB:andb _ _=true|-_=>apply andb_true_iff in HB;destruct HB
 end.
 split;[|split;[|split;[exact H1|split;[exact H2|exact HI]]]].
 - change(BitOps.bitSlice code 0 7=103).
   match goal with HJ:Z.eqb(BitOps.bitSlice code 0 7)Decode.opcode_JALR=true|-_=>apply Z.eqb_eq in HJ;exact HJ end.
 - change(BitOps.bitSlice code 12 15=0).
   match goal with HJ:Z.eqb(BitOps.bitSlice code 12 15)Decode.funct3_JALR=true|-_=>apply Z.eqb_eq in HJ;exact HJ end.
Qed.

Theorem original_decode_jalr_fields code rd rs1 imm:
 Decode.decode Decode.RV32I code=Decode.IInstruction(Decode.Jalr rd rs1 imm) ->
 field_reference code Opcode=103 /\field_reference code Funct3=0 /\
 field_reference code Rd=rd /\field_reference code Rs1=rs1 /\immediate code=imm.
Proof.
 rewrite <-decode_seq_correct;unfold decode_seq;cbn[bitwidth supportsM supportsA supportsF].
 destruct(isValidI(decodeI 32 code))eqn:HV.
 - intro H;injection H as H;now apply(decode_i_jalr_fields code rd rs1 imm).
 - destruct(isValidCSR(decodeCSR 32 code));discriminate.
Qed.
End CPUISAJalrFields.
Print Assumptions CPUISAJalrFields.decode_i_jalr_fields.
Print Assumptions CPUISAJalrFields.original_decode_jalr_fields.
