(** A physical RF read rule; no ISA freshness or register relation assumed. *)
From Coq Require Import ZArith List Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVBankRead Lang.ExtendedSVBankIndex
 Lang.ExtendedSVRegisterBank Lang.ExtendedSVBitSlice Lang.ExtendedSVWordInvariant.
Import ExtendedSV ExtendedSVBankRead ExtendedSVBankIndex ExtendedSVRegisterBank
 ExtendedSVBitSlice ExtendedSVWordInvariant.
Local Open Scope Z_scope.
Module ExtendedSVZeroGuardedRead.
Definition value bank index:=if Z.eqb index 0 then 0 else lane_read 32 bank index.
Definition offset address:=ESel 10(EBinary 32 BShiftL(EExtend 32 false(EVar 5 address))(EConst 32 5))(EConst 32 0).
Definition expression total bank address:=ECond 32
 (EBinary 1 BEq(EConst 5 0)(EVar 5 address))(EConst 32 0)
 (ESel 32(EVar total bank)(offset address)).
Theorem read_value total bank address s:(1024<=total)%nat ->
 norm 32(eval_expr s(expression total bank address))=
 value(read_signal s bank)(norm 5(read_signal s address)).
Proof.
 intro HT;unfold expression,value.
 change(norm 32(norm 32(if Z.eqb(norm 1(if Z.eqb 0(norm 5(read_signal s address))then 1 else 0))0
 then eval_expr s(ESel 32(EVar total bank)(offset address))else 0))=
 if Z.eqb(norm 5(read_signal s address))0 then 0 else lane_read 32(read_signal s bank)(norm 5(read_signal s address))).
 rewrite(Z.eqb_sym(norm 5(read_signal s address))0).
 rewrite norm_idempotent.
 destruct(Z.eqb 0(norm 5(read_signal s address)))eqn:HE.
 - reflexivity.
 - change(norm 32(eval_expr s(ESel 32(EVar total bank)(offset address)))=
     lane_read 32(read_signal s bank)(norm 5(read_signal s address))).
   rewrite(eval_packed_lane bank total(offset address)HT eq_refl s);unfold offset;rewrite shifted_index.
   unfold lane_read,read_slice;apply norm_idempotent.
Qed.
End ExtendedSVZeroGuardedRead.
Print Assumptions ExtendedSVZeroGuardedRead.read_value.
