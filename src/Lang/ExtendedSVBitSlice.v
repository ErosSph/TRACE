(** Bit-level facts for the exact packed-array update used by ExtendedSV. *)
From Coq Require Import ZArith Lia Bool btauto.Btauto.
Require Import Lang.ExtendedSV.
Import ExtendedSV.
Local Open Scope Z_scope.

Module ExtendedSVBitSlice.
  Definition read_slice (value offset width : Z) : Z :=
    Z.land (Z.shiftr value offset) (2 ^ width - 1).

  Lemma mask_bit_low : forall width bit,
      0 <= bit < width -> Z.testbit (2 ^ width - 1) bit = true.
  Proof.
    intros width bit H. replace (2 ^ width - 1) with (Z.ones width)
      by (rewrite Z.ones_equiv; lia).
    now apply Z.ones_spec_low.
  Qed.

  Lemma mask_bit_high : forall width bit,
      0 <= width <= bit -> Z.testbit (2 ^ width - 1) bit = false.
  Proof.
    intros width bit H. replace (2 ^ width - 1) with (Z.ones width)
      by (rewrite Z.ones_equiv; lia).
    now apply Z.ones_spec_high.
  Qed.

  Theorem read_slice_write_same : forall old offset width value,
      0 <= offset -> 0 <= width ->
      read_slice (write_slice old offset width value) offset width =
        read_slice value 0 width.
  Proof.
    intros old offset width value Hoffset Hwidth.
    apply Z.bits_inj. intros bit.
    destruct (Z_lt_ge_dec bit 0) as [Hnegative|Hbit].
    - repeat rewrite Z.testbit_neg_r by lia. reflexivity.
    - unfold read_slice. rewrite !Z.land_spec.
      destruct (Z_lt_ge_dec bit width) as [Hlow|Hhigh].
      + rewrite mask_bit_low by lia.
        rewrite !Bool.andb_true_r, !Z.shiftr_spec by lia.
        unfold write_slice. rewrite Z.lor_spec, !Z.land_spec.
        rewrite Z.lnot_spec by lia. rewrite !Z.shiftl_spec by lia.
        replace (bit + offset - offset) with bit by lia.
        rewrite mask_bit_low by lia. replace (bit + 0) with bit by lia.
        btauto.
      + rewrite mask_bit_high by lia. now rewrite !Bool.andb_false_r.
  Qed.

  Theorem read_slice_write_disjoint : forall old read_offset read_width
      write_offset write_width value,
      0 <= read_offset -> 0 <= read_width ->
      0 <= write_offset -> 0 <= write_width ->
      (read_offset + read_width <= write_offset \/
       write_offset + write_width <= read_offset) ->
      read_slice (write_slice old write_offset write_width value)
        read_offset read_width = read_slice old read_offset read_width.
  Proof.
    intros old ro rw wo ww value Hro Hrw Hwo Hww Hdis.
    apply Z.bits_inj. intros bit.
    destruct (Z_lt_ge_dec bit 0) as [Hnegative|Hbit].
    - repeat rewrite Z.testbit_neg_r by lia. reflexivity.
    - unfold read_slice. rewrite !Z.land_spec.
      destruct (Z_lt_ge_dec bit rw) as [Hlow|Hhigh].
      + rewrite mask_bit_low by lia. rewrite !Bool.andb_true_r.
        rewrite !Z.shiftr_spec by lia.
        unfold write_slice. rewrite Z.lor_spec, !Z.land_spec.
        rewrite Z.lnot_spec by lia. rewrite !Z.shiftl_spec by lia.
        assert (Hmask : Z.testbit (2 ^ ww - 1) (bit + ro - wo) = false).
        { destruct Hdis as [Hbefore|Hafter].
          - apply Z.testbit_neg_r. lia.
          - apply mask_bit_high. lia. }
        rewrite Hmask. btauto.
      + rewrite mask_bit_high by lia. now rewrite !Bool.andb_false_r.
  Qed.
End ExtendedSVBitSlice.
