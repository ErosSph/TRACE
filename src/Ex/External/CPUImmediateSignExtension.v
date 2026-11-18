(** CPU-independent RTL concatenation versus the reference ISA sign extension. *)
From Coq Require Import ZArith Lia Bool.
Require Import Lang.ExtendedSV coqutil.Z.BitOps coqutil.Z.bitblast.
Import ExtendedSV.
Local Open Scope Z_scope.
Module CPUImmediateSignExtension.
Lemma sign_bit_word code : norm 1(Z.shiftr code 31)=
 if Z.testbit code 31 then 1 else 0.
Proof.
 unfold norm,mask. change(Z.land(Z.shiftr code 31)(Z.ones 1)=if Z.testbit code 31 then 1 else 0).
 rewrite Z.land_ones by lia.
 rewrite <-Z.bit0_mod,Z.shiftr_spec by lia.
 change(Z.b2z(Z.testbit code 31)=if Z.testbit code 31 then 1 else 0).
 destruct(Z.testbit code 31);reflexivity.
Qed.
Lemma immediate_sign_bit code :Z.testbit(norm 12(Z.shiftr code 20))11=Z.testbit code 31.
Proof.
 unfold norm,mask. rewrite Z.land_spec,Z.shiftr_spec by lia.
 change(andb(Z.testbit code 31)true=Z.testbit code 31). apply andb_true_r.
Qed.
Theorem concat_i_sign_extension code :
 norm 32(Z.lor(Z.shiftl(if Z.eqb(norm 1(Z.shiftr code 31))0 then 0 else 1048575)12)
 (norm 12(Z.shiftr code 20)))=
 norm 32(BitOps.signExtend 12(norm 12(Z.shiftr code 20))).
Proof.
 rewrite sign_bit_word,BitOps.signExtend_alt_bitwise by lia.
 unfold BitOps.signExtend_bitwise. change(12-1)with 11.
 rewrite immediate_sign_bit. destruct(Z.testbit code 31);cbn [Z.eqb].
 - change 1048575 with(Z.ones 20). unfold norm,mask.
   change(2^Z.of_nat 12-1)with(Z.ones 12).
   change(2^Z.of_nat 32-1)with(Z.ones 32). Z.bitblast.
 - unfold norm,mask.
   change(2^Z.of_nat 12-1)with(Z.ones 12).
   change(2^Z.of_nat 32-1)with(Z.ones 32). Z.bitblast.
Qed.
End CPUImmediateSignExtension.
Print Assumptions CPUImmediateSignExtension.concat_i_sign_extension.
