(** Bit reversal and the shift-left-by-reversal identity (design independent, template route, 2026-11-03).

    Many cores implement a left shift as  reverse (right_shift (reverse a)).  The reverse is written one bit per
    process, [rev[i] = a[W-1-i]] (generate loop).  [rev_from_slices] : if every bit [i < W] of root [r] carries the slice
    equation of [rev_slice_expr W k x i] (= [ESel 1 (EVar W x) (EConst k (W-1-i))], the shape of those processes), then
    [norm W (read r) = rev_bits W (norm W (read x))].  [rev_shr_rev]: reverse of (reverse a >> s) is [norm W (a << s)].
    [eval_shr64_low]: low word of the 64-bit logical right shift of a (zero extended) word, as the RTL writes it.
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVSliceBits Lang.ExtendedSVSliceExec Lang.ExtendedSVBankAlignment Lang.ExtendedSVPackedROM.
Import ListNotations ExtendedSV ExtendedSVSliceBits ExtendedSVSliceExec ExtendedSVBankAlignment ExtendedSVPackedROM.
Local Open Scope Z_scope.
Module CPUBitReverse.

(** [rev_bits n x]: bit [i < n] of the result is bit [n-1-i] of [x]; no higher bits. *)
Fixpoint rev_bits (n:nat) (x:Z) : Z :=
 match n with
 | O => 0
 | S k => Z.lor (if Z.testbit x 0 then 2 ^ Z.of_nat k else 0) (rev_bits k (Z.shiftr x 1))
 end.

Definition reverse32 (x:Z) : Z := rev_bits 32 x.

Lemma rev_bits_testbit n : forall x i, 0 <= i ->
 Z.testbit (rev_bits n x) i = (i <? Z.of_nat n) && Z.testbit x (Z.of_nat n - 1 - i).
Proof.
 induction n as [|k IH]; intros x i Hi.
 - cbn [rev_bits]. rewrite Z.testbit_0_l. replace (Z.of_nat 0) with 0 by reflexivity. destruct (Z.ltb_spec i 0); [lia|reflexivity].
 - cbn [rev_bits]. rewrite Z.lor_spec. rewrite IH; [|exact Hi].
   rewrite Nat2Z.inj_succ.
   assert (Hb : Z.testbit (if Z.testbit x 0 then 2 ^ Z.of_nat k else 0) i = (Z.eqb (Z.of_nat k) i) && Z.testbit x 0).
   { destruct (Z.testbit x 0); [rewrite Z.pow2_bits_eqb by lia; rewrite andb_true_r; reflexivity|rewrite Z.testbit_0_l; rewrite andb_false_r; reflexivity]. }
   rewrite Hb.
   destruct (Z.ltb_spec i (Z.of_nat k)).
   + assert (E1 : (i <? Z.succ (Z.of_nat k)) = true) by (apply Z.ltb_lt; lia).
     assert (E3 : Z.eqb (Z.of_nat k) i = false) by (apply Z.eqb_neq; lia).
     rewrite E1, E3. cbn [andb orb]. rewrite Z.shiftr_spec by lia. replace (Z.of_nat k - 1 - i + 1) with (Z.succ (Z.of_nat k) - 1 - i) by lia. reflexivity.
   + destruct (Z.eqb_spec (Z.of_nat k) i) as [<-|N].
     * assert (E1 : (Z.of_nat k <? Z.succ (Z.of_nat k)) = true) by (apply Z.ltb_lt; lia).
       rewrite E1. cbn [andb orb]. replace (Z.succ (Z.of_nat k) - 1 - Z.of_nat k) with 0 by lia. rewrite orb_false_r. reflexivity.
     * assert (E1 : (i <? Z.succ (Z.of_nat k)) = false) by (apply Z.ltb_ge; lia).
       rewrite E1. reflexivity.
Qed.

Lemma rev_bits_norm n x : rev_bits n (norm n x) = rev_bits n x.
Proof.
 apply Z.bits_inj'. intros i Hi. rewrite !rev_bits_testbit by lia.
 destruct (i <? Z.of_nat n) eqn:E; [|reflexivity]. apply Z.ltb_lt in E.
 rewrite testbit_norm by lia.
 assert (H : (Z.of_nat n - 1 - i <? Z.of_nat n) = true) by (apply Z.ltb_lt; lia). rewrite H. cbn [andb]. rewrite andb_true_r. reflexivity.
Qed.

Lemma rev_bits_range n x : norm n (rev_bits n x) = rev_bits n x.
Proof.
 apply Z.bits_inj'. intros i Hi. rewrite testbit_norm by lia. rewrite rev_bits_testbit by lia.
 destruct (i <? Z.of_nat n); cbn [andb]; [rewrite andb_true_r|]; reflexivity.
Qed.

(** Reversal is an involution on words. *)
Lemma rev_bits_invol n x : rev_bits n (rev_bits n x) = norm n x.
Proof.
 apply Z.bits_inj'. intros i Hi. rewrite testbit_norm by lia. rewrite rev_bits_testbit by lia.
 destruct (Z.ltb_spec i (Z.of_nat n)); [|cbn [andb]; rewrite andb_false_r; reflexivity]. rewrite andb_true_l.
 rewrite rev_bits_testbit by lia.
 assert (H1 : (Z.of_nat n - 1 - i <? Z.of_nat n) = true) by (apply Z.ltb_lt; lia). rewrite H1.
 replace (Z.of_nat n - 1 - (Z.of_nat n - 1 - i)) with i by lia. cbn [andb]. rewrite andb_true_r. reflexivity.
Qed.

(** Left shift = reverse . right shift . reverse. *)
Theorem rev_shr_rev n a s : 0 <= s ->
 rev_bits n (Z.shiftr (rev_bits n a) s) = norm n (Z.shiftl a s).
Proof.
 intros Hs. apply Z.bits_inj'. intros i Hi.
 rewrite rev_bits_testbit by lia. rewrite testbit_norm by lia. rewrite Z.shiftl_spec by lia.
 destruct (Z.ltb_spec i (Z.of_nat n)); [|cbn [andb]; rewrite andb_false_r; reflexivity]. rewrite !andb_true_l.
 rewrite Z.shiftr_spec by lia. rewrite rev_bits_testbit by lia.
 destruct (Z.ltb_spec (Z.of_nat n - 1 - i + s) (Z.of_nat n)).
 - rewrite andb_true_l, andb_true_r. f_equal. lia.
 - rewrite andb_false_l, andb_true_r. symmetry. apply Z.testbit_neg_r. lia.
Qed.

Corollary shiftl_via_reverse32 a s : 0 <= s -> reverse32 (Z.shiftr (reverse32 a) s) = Z.shiftl a s mod 4294967296.
Proof. intros Hs. unfold reverse32. rewrite rev_shr_rev by exact Hs. rewrite norm_mod. reflexivity. Qed.

(** ---- expression level: the generate-loop processes ---- *)
Definition rev_slice_expr (W k:nat) (x:signal) (i:Z) : Expr := ESel 1 (EVar W x) (EConst k (Z.of_nat W - 1 - i)).

Definition zseq (n:nat) : list Z := map Z.of_nat (seq 0 n).
Lemma in_zseq n i : In i (zseq n) <-> 0 <= i < Z.of_nat n.
Proof.
 unfold zseq. rewrite in_map_iff. split.
 - intros [m [<- Hm]]. apply in_seq in Hm. lia.
 - intros H. exists (Z.to_nat i). split; [lia|]. apply in_seq. lia.
Qed.

(** The 32 (W) one-bit slice equations as a list a generator can compare with the chain output. *)
Definition rev_slices (r:signal) (W k:nat) (x:signal) : list SEqn :=
 map (fun i => (r, i, 1%nat, rev_slice_expr W k x i)) (zseq W).

Lemma eval_rev_slice_bit s W k x i : 0 <= i < Z.of_nat W -> Z.of_nat W - 1 < 2 ^ Z.of_nat k ->
 Z.testbit (eval_expr s (rev_slice_expr W k x i)) 0 = Z.testbit (read_signal s x) (Z.of_nat W - 1 - i).
Proof.
 intros Hi Hk. unfold rev_slice_expr. cbn [eval_expr].
 rewrite testbit_norm by lia. change (0 <? Z.of_nat 1) with true. rewrite andb_true_r.
 rewrite Z.shiftr_spec by lia. rewrite (norm_in_range k (Z.of_nat W - 1 - i)) by lia.
 rewrite testbit_norm by lia. replace (0 + (Z.of_nat W - 1 - i)) with (Z.of_nat W - 1 - i) by lia.
 assert (H : (Z.of_nat W - 1 - i <? Z.of_nat W) = true) by (apply Z.ltb_lt; lia). rewrite H. apply andb_true_r.
Qed.

Theorem rev_from_slices s r x (W k:nat) :
 Z.of_nat W - 1 < 2 ^ Z.of_nat k ->
 SliceHold s (rev_slices r W k x) ->
 norm W (read_signal s r) = rev_bits W (norm W (read_signal s x)).
Proof.
 intros Hk H. apply Z.bits_inj'. intros i Hi.
 rewrite rev_bits_norm. rewrite rev_bits_testbit by lia. rewrite testbit_norm by lia.
 destruct (Z.ltb_spec i (Z.of_nat W)); [|cbn [andb]; rewrite andb_false_r; reflexivity]. rewrite !andb_true_l.
 assert (Hin : In (r, i, 1%nat, rev_slice_expr W k x i) (rev_slices r W k x)).
 { unfold rev_slices. apply in_map_iff. exists i. split; [reflexivity|]. apply in_zseq. lia. }
 rewrite (slice_bit s r i _ (H _ _ _ _ Hin)). rewrite andb_true_r. apply eval_rev_slice_bit; lia.
Qed.

(** ---- the 64-bit logical right shift, low word ---- *)
Definition shr64_low_expr (R sh:signal) : Expr :=
 ESel 32 (EBinary 64 BShiftR (EVar 64 R) (ESel 5 (EVar 32 sh) (EConst 5 0))) (EConst 32 0).

Lemma norm_norm_le w1 w2 v : (w1 <= w2)%nat -> norm w1 (norm w2 v) = norm w1 v.
Proof.
 intros H. apply Z.bits_inj'. intros i Hi. rewrite !testbit_norm by lia.
 destruct (Z.ltb_spec i (Z.of_nat w1)); [|rewrite !andb_false_r; reflexivity].
 assert (E : (i <? Z.of_nat w2) = true) by (apply Z.ltb_lt; lia). rewrite E. rewrite !andb_true_r. reflexivity.
Qed.

Lemma eval_shr64_low s R sh a n : norm 64 (read_signal s R) = a -> norm 5 (read_signal s sh) = n ->
 eval_expr s (shr64_low_expr R sh) = norm 32 (Z.shiftr a n).
Proof.
 intros Ha Hn. unfold shr64_low_expr. cbn [eval_expr].
 rewrite Ha. change (norm 5 0) with 0. change (norm 32 0) with 0. rewrite !Z.shiftr_0_r.
 rewrite (norm_norm_le 5 32) by lia. rewrite Hn. rewrite (norm_norm_le 32 64) by lia. reflexivity.
Qed.
End CPUBitReverse.
Print Assumptions CPUBitReverse.rev_from_slices.
Print Assumptions CPUBitReverse.rev_shr_rev.
Print Assumptions CPUBitReverse.shiftl_via_reverse32.
Print Assumptions CPUBitReverse.eval_shr64_low.
