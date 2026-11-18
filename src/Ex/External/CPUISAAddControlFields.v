(** Control requirements are extracted from the unchanged ISA decoder. *)
From Coq Require Import ZArith List Bool.
Require Import riscv.Proofs.DecodeByExtension Ex.External.CPUInstructionFields.
Import CPUInstructionFields.
Local Open Scope Z_scope.
Module CPUISAAddControlFields.

Lemma decode_i_add_fields code rd rs1 rs2:
 decodeI 32 code=Decode.Add rd rs1 rs2 ->
 field_reference code Opcode=51 /\field_reference code Funct3=0 /\field_reference code Funct7=0.
Proof.
 unfold decodeI;cbv beta zeta.
 repeat match goal with |- context[if ?condition then _ else _]=>destruct condition eqn:? end;
 intro H;try discriminate.
 all: unfold field_reference,field_offset,field_width;cbn.
 all: repeat match goal with
 | H:andb _ _=true |- _ =>apply andb_true_iff in H;destruct H
 | H:Z.eqb _ _=true |- _ =>apply Z.eqb_eq in H
 end;intuition congruence.
Qed.

Theorem original_decode_add_fields code rd rs1 rs2:
 Decode.decode Decode.RV32I code=Decode.IInstruction(Decode.Add rd rs1 rs2) ->
 field_reference code Opcode=51 /\field_reference code Funct3=0 /\field_reference code Funct7=0.
Proof.
 rewrite <-decode_seq_correct;unfold decode_seq;cbn[bitwidth supportsM supportsA supportsF].
 destruct(isValidI(decodeI 32 code))eqn:HV.
 - intro H;injection H as H;now apply(decode_i_add_fields code rd rs1 rs2).
 - destruct(isValidCSR(decodeCSR 32 code));discriminate.
Qed.
End CPUISAAddControlFields.
Print Assumptions CPUISAAddControlFields.original_decode_add_fields.
