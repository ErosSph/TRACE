(** Bit-level facts about partial (slice) writes (template route, 2026-11-03).

    Generic, design independent.  proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.

    [write_slice old l w v] puts the low [w] bits of [v] at bit positions [l .. l+w-1] of [old] and keeps every other
    bit.  [SliceEq s r l w e] says: bits [l .. l+w-1] of root [r] in state [s] equal the value of [e] truncated to [w] bits. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV.
Import ListNotations ExtendedSV.
Local Open Scope Z_scope.
Module ExtendedSVSliceBits.

Lemma testbit_ones_mask w i : 0 <= i -> Z.testbit (mask w) i = (i <? Z.of_nat w).
Proof.
 intros Hi. unfold mask. replace (2 ^ Z.of_nat w - 1) with (Z.ones (Z.of_nat w)) by (rewrite Z.ones_equiv; lia).
 rewrite Z.testbit_ones_nonneg by lia. destruct (i <? Z.of_nat w) eqn:E; [apply Z.ltb_lt in E; destruct (Z.ltb_spec i (Z.of_nat w)); reflexivity|reflexivity].
Qed.

Lemma testbit_norm w v i : 0 <= i -> Z.testbit (norm w v) i = Z.testbit v i && (i <? Z.of_nat w).
Proof. intros Hi. unfold norm. rewrite Z.land_spec, testbit_ones_mask by lia. reflexivity. Qed.

(** Field mask of [write_slice] (width as an integer). *)
Lemma testbit_field l w m : 0 <= l -> 0 <= w -> 0 <= m ->
 Z.testbit (Z.shiftl (2 ^ w - 1) l) m = (l <=? m) && (m <? l + w).
Proof.
 intros Hl Hw Hm. rewrite Z.shiftl_spec by lia.
 replace (2 ^ w - 1) with (Z.ones w) by (rewrite Z.ones_equiv; lia).
 destruct (Z.leb_spec l m).
 - rewrite Z.testbit_ones_nonneg by lia.
   destruct (Z.ltb_spec (m - l) w), (Z.ltb_spec m (l + w)); try reflexivity; try lia.
   all: destruct (Z.leb_spec 0 (m-l)); try lia; reflexivity.
 - rewrite Z.testbit_neg_r by lia. reflexivity.
Qed.

Lemma write_slice_testbit old l w v m : 0 <= l -> 0 <= w -> 0 <= m ->
 Z.testbit (write_slice old l w v) m =
 if (l <=? m) && (m <? l + w) then Z.testbit v (m - l) else Z.testbit old m.
Proof.
 intros Hl Hw Hm. unfold write_slice.
 rewrite Z.lor_spec, !Z.land_spec, Z.lnot_spec by lia.
 rewrite testbit_field by lia. rewrite Z.shiftl_spec by lia.
 destruct ((l <=? m) && (m <? l + w)); cbn; [|rewrite andb_false_r; rewrite Bool.orb_false_r; rewrite andb_true_r; reflexivity].
 rewrite andb_true_r. rewrite andb_false_r. reflexivity.
Qed.

(** Reading back the written slice. *)
Lemma slice_after_write old l w v : 0 <= l -> 0 <= w ->
 norm (Z.to_nat w) (Z.shiftr (write_slice old l w v) l) = norm (Z.to_nat w) v.
Proof.
 intros Hl Hw. apply Z.bits_inj'. intros n Hn.
 rewrite !testbit_norm by lia. rewrite Z2Nat.id by lia.
 destruct (n <? w) eqn:E; [|rewrite !andb_false_r; reflexivity].
 apply Z.ltb_lt in E. rewrite !andb_true_r.
 rewrite Z.shiftr_spec by lia. rewrite write_slice_testbit by lia.
 replace (n + l - l) with n by lia.
 assert (H1 : (l <=? n + l) = true) by (apply Z.leb_le; lia).
 assert (H2 : (n + l <? l + w) = true) by (apply Z.ltb_lt; lia).
 rewrite H1, H2. reflexivity.
Qed.

(** A disjoint slice is not disturbed. *)
Lemma slice_disjoint old l w v l' w' : 0 <= l -> 0 <= w -> 0 <= l' -> 0 <= w' -> (l' + w' <= l \/ l + w <= l') ->
 norm (Z.to_nat w') (Z.shiftr (write_slice old l w v) l') = norm (Z.to_nat w') (Z.shiftr old l').
Proof.
 intros Hl Hw Hl' Hw' Hd. apply Z.bits_inj'. intros n Hn.
 rewrite !testbit_norm by lia. rewrite Z2Nat.id by lia.
 destruct (n <? w') eqn:E; [|rewrite !andb_false_r; reflexivity].
 apply Z.ltb_lt in E. rewrite !andb_true_r.
 rewrite !Z.shiftr_spec by lia. rewrite write_slice_testbit by lia.
 assert (H : ((l <=? n + l') && (n + l' <? l + w)) = false).
 { destruct (Z.leb_spec l (n+l')), (Z.ltb_spec (n+l') (l+w)); try reflexivity; lia. }
 rewrite H. reflexivity.
Qed.

(** Slice equations. *)
Definition SliceEq (s:State) (r:signal) (l:Z) (w:nat) (e:Expr) : Prop :=
 0 <= l /\ norm w (Z.shiftr (read_signal s r) l) = norm w (eval_expr s e).

Definition SliceHold (s:State) (E:list (signal*Z*nat*Expr)) : Prop :=
 forall r l w e, In (r,l,w,e) E -> SliceEq s r l w e.

(** One-bit slices: the bit itself. *)
Lemma slice_bit s r l e : SliceEq s r l 1 e -> Z.testbit (read_signal s r) l = Z.testbit (eval_expr s e) 0.
Proof.
 intros [Hl H]. assert (H0 := f_equal (fun z => Z.testbit z 0) H). cbv beta in H0.
 rewrite !testbit_norm in H0 by lia. change (0 <? Z.of_nat 1) with true in H0. rewrite !andb_true_r in H0.
 rewrite Z.shiftr_spec in H0 by lia. replace (0 + l) with l in H0 by lia. exact H0.
Qed.

(** Bits of a word from its one-bit slices: if every bit [i < n] of root [r] is slice-defined by [f i], then
    [norm n (read r)] is determined bit by bit. *)
Lemma norm_bits_from_slices s r n (f : Z -> Expr) (g : Z -> bool) :
 (forall i, 0 <= i < Z.of_nat n -> SliceEq s r i 1 (f i)) ->
 (forall i, 0 <= i < Z.of_nat n -> Z.testbit (eval_expr s (f i)) 0 = g i) ->
 forall i, 0 <= i < Z.of_nat n -> Z.testbit (norm n (read_signal s r)) i = g i.
Proof.
 intros H1 H2 i Hi. rewrite testbit_norm by lia.
 destruct (Z.ltb_spec i (Z.of_nat n)); [|lia]. rewrite andb_true_r.
 rewrite (slice_bit s r i (f i) (H1 i Hi)). apply H2, Hi.
Qed.

Lemma norm_nonneg w v : 0 <= norm w v.
Proof.
 unfold norm. apply Z.land_nonneg. right. unfold mask.
 assert (0 < 2 ^ Z.of_nat w) by (apply Z.pow_pos_nonneg; lia). lia.
Qed.

Lemma slice_after_write_nat old l (w:nat) v : 0 <= l ->
 norm w (Z.shiftr (write_slice old l (Z.of_nat w) v) l) = norm w v.
Proof. intros Hl. pose proof (slice_after_write old l (Z.of_nat w) v Hl (Zle_0_nat w)) as H. rewrite Nat2Z.id in H. exact H. Qed.

Lemma slice_disjoint_nat old l (w:nat) v l' (w':nat) : 0 <= l -> 0 <= l' -> (l' + Z.of_nat w' <= l \/ l + Z.of_nat w <= l') ->
 norm w' (Z.shiftr (write_slice old l (Z.of_nat w) v) l') = norm w' (Z.shiftr old l').
Proof. intros Hl Hl' Hd. pose proof (slice_disjoint old l (Z.of_nat w) v l' (Z.of_nat w') Hl (Zle_0_nat w) Hl' (Zle_0_nat w') Hd) as H. rewrite Nat2Z.id in H. exact H. Qed.

End ExtendedSVSliceBits.
Print Assumptions ExtendedSVSliceBits.slice_after_write.
Print Assumptions ExtendedSVSliceBits.slice_disjoint.
