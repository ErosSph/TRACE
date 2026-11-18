(** A captured update list is idempotent even with overlapping, unequal masks.
    Values/offsets are fixed captures. This does NOT establish that re-executing
    a process captures the same list, nor make arbitrary feedback idempotent. *)
From Coq Require Import List ZArith Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVStateLength.
Import ListNotations ExtendedSV ExtendedSVStateLength.
Module ExtendedSVArbitraryMaskedReplay.

Definition covers (u:Update) (root:signal) (bit:Z) :=
 Nat.eqb (update_signal u) root && Z.testbit (update_mask u) bit.
Definition captured_value_bit (u:Update) (bit:Z) :=
 Z.testbit (Z.shiftl (update_value u) (update_offset u)) bit.

Lemma apply_update_bit s u root bit :
 Z.testbit (read_signal (apply_update s u) root) bit =
 if covers u root bit then captured_value_bit u bit
 else Z.testbit (read_signal s root) bit.
Proof.
 destruct (Z_lt_ge_dec bit 0) as [HN|HN].
 - unfold covers,captured_value_bit.
   rewrite !Z.testbit_neg_r by lia. now destruct (Nat.eqb (update_signal u) root).
 - unfold apply_update,covers,captured_value_bit.
   destruct (Nat.eq_dec (update_signal u) root) as [HR|HR].
   + subst root. rewrite read_signal_write_same,Nat.eqb_refl. cbn [andb].
     unfold write_slice,update_mask.
     rewrite Z.lor_spec,!Z.land_spec,Z.lnot_spec by lia.
     destruct (Z.testbit (Z.shiftl (2 ^ Z.of_nat (update_width u)-1) (update_offset u)) bit);
     destruct (Z.testbit (read_signal s (update_signal u)) bit);
     destruct (Z.testbit (Z.shiftl (update_value u) (update_offset u)) bit);reflexivity.
   + rewrite read_signal_write_other by congruence.
     rewrite (proj2 (Nat.eqb_neq _ _) HR). reflexivity.
Qed.

Fixpoint final_captured_bit (updates:list Update) root bit : option bool :=
 match updates with
 | []=>None
 | u::rest=>match final_captured_bit rest root bit with
   | Some value=>Some value
   | None=>if covers u root bit then Some(captured_value_bit u bit) else None
   end
 end.

Theorem captured_list_bit s updates root bit :
 Z.testbit (read_signal (apply_updates s updates) root) bit =
 match final_captured_bit updates root bit with
 | Some value=>value
 | None=>Z.testbit (read_signal s root) bit
 end.
Proof.
 induction updates as [|u rest IH] in s |- *; cbn; [reflexivity|].
 rewrite IH. destruct (final_captured_bit rest root bit); [reflexivity|].
 rewrite apply_update_bit. destruct (covers u root bit); reflexivity.
Qed.

Lemma write_signal_length_max s root value :
 length(write_signal s root value)=Nat.max (length s) (S root).
Proof.
 induction root as [|root IH] in s |- *; destruct s; cbn;
 rewrite ?IH,?Nat.max_0_r; reflexivity.
Qed.

Fixpoint update_extent (updates:list Update) :=
 match updates with []=>0%nat|u::rest=>Nat.max (S(update_signal u)) (update_extent rest) end.

Lemma captured_list_length s updates :
 length(apply_updates s updates)=Nat.max (length s) (update_extent updates).
Proof.
 induction updates as [|u rest IH] in s |- *; cbn.
 - now rewrite Nat.max_0_r.
 - rewrite IH. unfold apply_update. rewrite write_signal_length_max.
   change (Nat.max (Nat.max (length s) (S(update_signal u))) (update_extent rest) =
     Nat.max (length s) (Nat.max (S(update_signal u)) (update_extent rest))).
   now rewrite Nat.max_assoc.
Qed.

Theorem arbitrary_captured_replay_is_idempotent updates s :
 apply_updates (apply_updates s updates) updates=apply_updates s updates.
Proof.
 apply state_ext.
 - rewrite !captured_list_length. now rewrite <-Nat.max_assoc,Nat.max_id.
 - intro root. apply Z.bits_inj. intro bit. rewrite !captured_list_bit.
   destruct (final_captured_bit updates root bit); reflexivity.
Qed.
End ExtendedSVArbitraryMaskedReplay.
Print Assumptions ExtendedSVArbitraryMaskedReplay.apply_update_bit.
Print Assumptions ExtendedSVArbitraryMaskedReplay.captured_list_bit.
Print Assumptions ExtendedSVArbitraryMaskedReplay.arbitrary_captured_replay_is_idempotent.
