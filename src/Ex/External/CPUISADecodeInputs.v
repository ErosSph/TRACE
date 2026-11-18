(** Original decoder -> ordered source-register bit fields. No DUT or CPU
    invariant is used. A hardware word still needs actual token ownership. *)
From Coq Require Import ZArith List.
Require Import riscv.Proofs.DecodeByExtension
 Ex.External.CV32E40PReq41Instruction Ex.External.CPUInstructionFields.
Import ListNotations CV32E40PReq41Instruction CPUInstructionFields.
Local Open Scope Z_scope.
Module CPUISADecodeInputs.
Definition register_fields code :=
 [Utility.bitSlice code 15 20;Utility.bitSlice code 20 25].

Lemma decode_i_register_fields code:
 source_registers(decodeI 32 code)=
 firstn(length(source_registers(decodeI 32 code)))(register_fields code).
Proof.
 unfold decodeI;cbv beta zeta.
 repeat match goal with |- context[if ?condition then _ else _]=>destruct condition end;
 reflexivity.
Qed.

Theorem original_decode_register_fields code instruction:
 Decode.decode Decode.RV32I code=Decode.IInstruction instruction ->
 source_registers instruction=
 firstn(length(source_registers instruction))(register_fields code).
Proof.
 rewrite <-decode_seq_correct;unfold decode_seq;
 cbn[bitwidth supportsM supportsA supportsF].
 destruct(isValidI(decodeI 32 code))eqn:HV.
 - intro H;inversion H;subst;apply decode_i_register_fields.
 - destruct(isValidCSR(decodeCSR 32 code));discriminate.
Qed.

Theorem first_register_field code instruction address rest:
 Decode.decode Decode.RV32I code=Decode.IInstruction instruction ->
 source_registers instruction=address::rest ->address=Utility.bitSlice code 15 20.
Proof.
 intros HD HS;pose proof(original_decode_register_fields code instruction HD)as HF.
 rewrite HS in HF;cbn[register_fields length firstn]in HF;now inversion HF.
Qed.

Theorem second_register_field code instruction first address rest:
 Decode.decode Decode.RV32I code=Decode.IInstruction instruction ->
 source_registers instruction=first::address::rest ->address=Utility.bitSlice code 20 25.
Proof.
 intros HD HS;pose proof(original_decode_register_fields code instruction HD)as HF.
 rewrite HS in HF;cbn[register_fields length firstn]in HF;now inversion HF.
Qed.

Theorem actual_first_address code instruction observed address rest:
 observed=field_reference code Rs1 ->
 Decode.decode Decode.RV32I code=Decode.IInstruction instruction ->
 source_registers instruction=address::rest ->observed=address.
Proof. intros HE HD HS;rewrite HE;exact(eq_sym(first_register_field code instruction address rest HD HS)). Qed.

Theorem actual_second_address code instruction observed first address rest:
 observed=field_reference code Rs2 ->
 Decode.decode Decode.RV32I code=Decode.IInstruction instruction ->
 source_registers instruction=first::address::rest ->observed=address.
Proof. intros HE HD HS;rewrite HE;exact(eq_sym(second_register_field code instruction first address rest HD HS)). Qed.
End CPUISADecodeInputs.
Print Assumptions CPUISADecodeInputs.original_decode_register_fields.
Print Assumptions CPUISADecodeInputs.first_register_field.
Print Assumptions CPUISADecodeInputs.second_register_field.
Print Assumptions CPUISADecodeInputs.actual_first_address.
Print Assumptions CPUISADecodeInputs.actual_second_address.
