(** Register identities come from the unchanged ISA decoder, not RTL names. *)
From Coq Require Import ZArith List Bool.
Require Import riscv.Proofs.DecodeByExtension Ex.External.CPUInstructionFields.
Import CPUInstructionFields.
Module CPUISAAddOperandFields.

Lemma decode_i_add_registers code rd rs1 rs2:
 decodeI 32 code=Decode.Add rd rs1 rs2 ->
 field_reference code Rd=rd /\field_reference code Rs1=rs1 /\field_reference code Rs2=rs2.
Proof.
 unfold decodeI;cbv beta zeta.
 repeat match goal with |-context[if ?condition then _ else _]=>destruct condition eqn:? end;
 intro H;try discriminate.
 all: inversion H;subst;unfold field_reference,field_offset,field_width;cbn;repeat split;reflexivity.
Qed.

Theorem original_decode_add_registers code rd rs1 rs2:
 Decode.decode Decode.RV32I code=Decode.IInstruction(Decode.Add rd rs1 rs2) ->
 field_reference code Rd=rd /\field_reference code Rs1=rs1 /\field_reference code Rs2=rs2.
Proof.
 rewrite <-decode_seq_correct;unfold decode_seq;cbn[bitwidth supportsM supportsA supportsF].
 destruct(isValidI(decodeI 32 code))eqn:HV.
 - intro H;injection H as H;now apply(decode_i_add_registers code rd rs1 rs2).
 - destruct(isValidCSR(decodeCSR 32 code));discriminate.
Qed.
End CPUISAAddOperandFields.
Print Assumptions CPUISAAddOperandFields.original_decode_add_registers.
