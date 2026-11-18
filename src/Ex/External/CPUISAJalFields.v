(** Original ISA JAL fields. No CPU state or hardware invariant. *)
From Coq Require Import ZArith List Bool.
Require Import riscv.Proofs.DecodeByExtension Ex.External.CPUInstructionFields.
Import CPUInstructionFields.
Local Open Scope Z_scope.
Module CPUISAJalFields.
Definition immediate code:=BitOps.signExtend 21
 (Z.lor(Z.lor(Z.lor(Z.shiftl(BitOps.bitSlice code 31 32)20)
 (Z.shiftl(BitOps.bitSlice code 21 31)1))(Z.shiftl(BitOps.bitSlice code 20 21)11))
 (Z.shiftl(BitOps.bitSlice code 12 20)12)).

Lemma decode_i_jal_fields code rd imm:
 decodeI 32 code=Decode.Jal rd imm ->
 field_reference code Opcode=111 /\field_reference code Rd=rd /\immediate code=imm.
Proof.
 unfold decodeI;cbv beta zeta.
 repeat match goal with|-context[if ?test then _ else _]=>destruct test eqn:? end;
 intro H;try discriminate.
 pose proof(f_equal(fun i=>match i with Decode.Jal r _=>r|_=>0 end)H)as HR.
 pose proof(f_equal(fun i=>match i with Decode.Jal _ v=>v|_=>0 end)H)as HI.
 split.
 - change(BitOps.bitSlice code 0 7=111).
   match goal with HJ:Z.eqb _ Decode.opcode_JAL=true|-_=>apply Z.eqb_eq in HJ;exact HJ end.
 - split;[exact HR|exact HI].
Qed.

Theorem original_decode_jal_fields code rd imm:
 Decode.decode Decode.RV32I code=Decode.IInstruction(Decode.Jal rd imm) ->
 field_reference code Opcode=111 /\field_reference code Rd=rd /\immediate code=imm.
Proof.
 rewrite <-decode_seq_correct;unfold decode_seq;cbn[bitwidth supportsM supportsA supportsF].
 destruct(isValidI(decodeI 32 code))eqn:HV.
 - intro H;injection H as H;now apply(decode_i_jal_fields code rd imm).
 - destruct(isValidCSR(decodeCSR 32 code));discriminate.
Qed.
End CPUISAJalFields.
