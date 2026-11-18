(** Zero-based finite bank encoding used by opt-in array lowering. Bounds
    are checked before translation; bit-slice laws supply local read/write
    contracts. No claim of full SystemVerilog/X equivalence is made here. *)
From Coq Require Import ZArith Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVBitSlice.
Import ExtendedSV ExtendedSVBitSlice.
Local Open Scope Z_scope.
Module CPUArrayContracts.
Definition bank_read width packed index := read_slice packed (width * index) width.
Definition bank_write width packed index data := write_slice packed (width * index) width data.
Theorem write_read_same width packed index data :
 0 <= width -> 0 <= index ->
 bank_read width (bank_write width packed index data) index = read_slice data 0 width.
Proof.
 intros Hw Hi. unfold bank_read,bank_write.
 apply read_slice_write_same; nia.
Qed.
Theorem write_read_other width packed index other data :
 0 < width -> 0 <= index -> 0 <= other -> index <> other ->
 bank_read width (bank_write width packed index data) other = bank_read width packed other.
Proof.
 intros Hw Hi Ho Hneq. unfold bank_read,bank_write.
 apply read_slice_write_disjoint; nia.
Qed.
Theorem index_dtype_covers_bank index_width raw :
 0 <= norm index_width raw < 2 ^ Z.of_nat index_width.
Proof.
 unfold norm,mask.
 replace (2 ^ Z.of_nat index_width - 1) with (Z.ones (Z.of_nat index_width))
   by (rewrite Z.ones_equiv; reflexivity).
 rewrite Z.land_ones by lia.
 apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.
Theorem norm_in_range width value :
 0 <= value < 2 ^ Z.of_nat width -> norm width value = value.
Proof.
 intros H. unfold norm,mask.
 replace (2 ^ Z.of_nat width - 1) with (Z.ones (Z.of_nat width))
   by (rewrite Z.ones_equiv; reflexivity).
 rewrite Z.land_ones by lia. apply Z.mod_small. exact H.
Qed.
End CPUArrayContracts.
Print Assumptions CPUArrayContracts.write_read_other.
Print Assumptions CPUArrayContracts.index_dtype_covers_bank.
