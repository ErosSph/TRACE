(** CPU-independent packed 32-bit program images and a checked address pattern.
    No CPU invariant, instruction history or design-specific proof is imported. *)
From Coq Require Import ZArith List Lia Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVBitSlice Lang.ExtendedSVWordInvariant.
Import ExtendedSV ExtendedSVBitSlice ExtendedSVWordInvariant ListNotations.
Local Open Scope Z_scope.
Module ExtendedSVPackedROM.
Lemma norm_in_range width value:0<=value<2^Z.of_nat width ->norm width value=value.
Proof.
 intro H;unfold norm,mask.
 replace(2^Z.of_nat width-1)with(Z.ones(Z.of_nat width))by(rewrite Z.ones_equiv;reflexivity).
 rewrite Z.land_ones by lia;apply Z.mod_small;exact H.
Qed.
Fixpoint pack (words:list Z):Z:=match words with
| []=>0|x::xs=>Z.lor x(Z.shiftl(pack xs)32)end.
Lemma high_bit w x bit:Word w x ->Z.of_nat w<=bit ->Z.testbit x bit=false.
Proof.
 intros HW HB;unfold Word in HW;rewrite HW at 1;unfold norm,mask.
 rewrite Z.land_spec,mask_bit_high by lia;apply andb_false_r.
Qed.
Lemma packed_bit words i bit:Forall(Word 32)words ->0<=bit<32 ->
 Z.testbit(pack words)(32*Z.of_nat i+bit)=Z.testbit(nth i words 0)bit.
Proof.
 revert i;induction words as[|x xs IH];intros i HW HB.
 - destruct i;cbn[pack nth];rewrite !Z.bits_0;reflexivity.
 - inversion HW as[|? ? HX HT];subst;destruct i as[|i].
   + cbn[pack nth Z.of_nat];rewrite Z.lor_spec,Z.shiftl_spec by lia.
     replace(32*0+bit)with bit by lia.
     rewrite(Z.testbit_neg_r(pack xs)(bit-32))by lia;apply orb_false_r.
   + cbn[pack nth];rewrite Z.lor_spec,Z.shiftl_spec by lia.
     rewrite(high_bit 32 x (32*Z.of_nat(S i)+bit)HX)by lia.
     rewrite orb_false_l;replace(32*Z.of_nat(S i)+bit-32)with(32*Z.of_nat i+bit)by lia.
     now apply IH.
Qed.
Theorem packed_slice capacity words i:Forall(Word 32)words ->(i<capacity)%nat ->
 norm 32(Z.shiftr(norm(32*capacity)(pack words))(32*Z.of_nat i))=norm 32(nth i words 0).
Proof.
 intros HW HI;apply Z.bits_inj;intro bit;destruct(Z_lt_ge_dec bit 0)as[HN|HN].
 - rewrite !Z.testbit_neg_r by lia;reflexivity.
 - unfold norm,mask;rewrite !Z.land_spec;destruct(Z_lt_ge_dec bit 32)as[HB|HB].
   + rewrite mask_bit_low by lia;rewrite !andb_true_r,Z.shiftr_spec by lia.
     rewrite Z.land_spec,mask_bit_low by
       (rewrite Nat2Z.inj_mul;change(0<=bit+32*Z.of_nat i<32*Z.of_nat capacity);lia).
     rewrite andb_true_r;replace(bit+32*Z.of_nat i)with(32*Z.of_nat i+bit)by lia.
     apply packed_bit;[exact HW|lia].
   + rewrite mask_bit_high by lia;now rewrite !andb_false_r.
Qed.
Definition lookup capacity offset_width image address:=norm 32(eval_expr []
 (ESel 32(EConst(32*capacity)image)
 (ESel offset_width(EBinary 32 BShiftL(EExtend 32 false
 (ESel 30(EConst 32 address)(EConst 5 2)))(EConst 32 5))(EConst 32 0)))).
Theorem aligned_lookup capacity offset_width image i:
 Z.of_nat i<2^25 ->32*Z.of_nat i<2^Z.of_nat offset_width ->
 lookup capacity offset_width image(4*Z.of_nat i)=
 norm 32(Z.shiftr(norm(32*capacity)image)(32*Z.of_nat i)).
Proof.
 intros HI HO;unfold lookup;cbn[eval_expr];rewrite !norm_idempotent.
 change(norm 5 2)with 2;change(norm 32 5)with 5;change(norm 32 0)with 0.
 rewrite(norm_in_range 32(4*Z.of_nat i))by(change(0<=4*Z.of_nat i<4294967296);change(Z.of_nat i<33554432)in HI;lia).
 rewrite(Z.shiftr_div_pow2(4*Z.of_nat i)2)by lia;change(2^2)with 4.
 rewrite(Z.mul_comm 4(Z.of_nat i)),Z.div_mul by discriminate.
 rewrite(norm_in_range 30(Z.of_nat i))by(change(0<=Z.of_nat i<1073741824);change(Z.of_nat i<33554432)in HI;lia).
 rewrite(norm_in_range 32(Z.of_nat i))by(change(0<=Z.of_nat i<4294967296);change(Z.of_nat i<33554432)in HI;lia).
 rewrite Z.shiftl_mul_pow2 by lia;change(2^5)with 32.
 rewrite(norm_in_range 32(Z.of_nat i*32))by(change(0<=Z.of_nat i*32<4294967296);change(Z.of_nat i<33554432)in HI;lia).
 rewrite Z.shiftr_0_r,(norm_in_range offset_width(Z.of_nat i*32))by lia.
 f_equal;f_equal;lia.
Qed.
Theorem lookup_packed capacity offset_width words i:
 Forall(Word 32)words ->(i<capacity)%nat ->Z.of_nat i<2^25 ->
 32*Z.of_nat i<2^Z.of_nat offset_width ->
 lookup capacity offset_width(pack words)(4*Z.of_nat i)=norm 32(nth i words 0).
Proof. intros HW HC HI HO;rewrite aligned_lookup by assumption;now apply packed_slice. Qed.
Lemma norm32_mod x:norm 32 x=x mod 2^32.
Proof.
 unfold norm,mask;change(2^Z.of_nat 32-1)with(2^32-1).
 replace(2^32-1)with(Z.ones 32)by(rewrite Z.ones_equiv;reflexivity).
 now rewrite Z.land_ones by lia.
Qed.
End ExtendedSVPackedROM.
Print Assumptions ExtendedSVPackedROM.lookup_packed.
