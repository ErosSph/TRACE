(** ADDI requirements are extracted from the original, unchanged ISA decoder. *)
From Coq Require Import ZArith List Bool.
Require Import riscv.Proofs.DecodeByExtension Ex.External.CPUInstructionFields.
Import CPUInstructionFields.
Local Open Scope Z_scope.
Module CPUISAAddiFields.

Lemma decode_i_addi_fields code rd rs1 imm:
 decodeI 32 code=Decode.Addi rd rs1 imm ->
 field_reference code Opcode=19 /\ field_reference code Funct3=0 /\
 field_reference code Rd=rd /\ field_reference code Rs1=rs1 /\
 BitOps.signExtend 12 (BitOps.bitSlice code 20 32)=imm.
Proof.
 unfold decodeI;cbv beta zeta.
 repeat match goal with |-context[if ?condition then _ else _]=>destruct condition eqn:? end;
 intro H;try discriminate.
 all: inversion H;subst;unfold field_reference,field_offset,field_width;cbn.
 all: repeat match goal with
 | H:andb _ _=true |- _ =>apply andb_true_iff in H;destruct H
 | H:Z.eqb _ _=true |- _ =>apply Z.eqb_eq in H
 end;intuition congruence.
Qed.

Theorem original_decode_addi_fields code rd rs1 imm:
 Decode.decode Decode.RV32I code=Decode.IInstruction(Decode.Addi rd rs1 imm) ->
 field_reference code Opcode=19 /\ field_reference code Funct3=0 /\
 field_reference code Rd=rd /\ field_reference code Rs1=rs1 /\
 BitOps.signExtend 12 (BitOps.bitSlice code 20 32)=imm.
Proof.
 rewrite <-decode_seq_correct;unfold decode_seq;cbn[bitwidth supportsM supportsA supportsF].
 destruct(isValidI(decodeI 32 code))eqn:HV.
 - intro H;injection H as H;now apply(decode_i_addi_fields code rd rs1 imm).
 - destruct(isValidCSR(decodeCSR 32 code));discriminate.
Qed.
End CPUISAAddiFields.
Print Assumptions CPUISAAddiFields.decode_i_addi_fields.
Print Assumptions CPUISAAddiFields.original_decode_addi_fields.
