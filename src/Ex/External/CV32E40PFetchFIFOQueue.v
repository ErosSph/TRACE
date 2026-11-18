(** Abstract queue view of the real FIFO's packed memory.  This model is an
    obligation target, not an alternate CPU transition. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVBitSlice
  Ex.External.CV32E40PFetchFIFOData Ex.External.CV32E40PFetchFIFOCount
  Ex.External.CV32E40PAddiIDEXAccept.
Import ListNotations ExtendedSV ExtendedSVBitSlice CV32E40PFetchFIFOData
  CV32E40PFetchFIFOCount CV32E40PAddiIDEXAccept.
Local Open Scope Z_scope.
Module CV32E40PFetchFIFOQueue.
  Lemma word_write memory wp value rp :
    word_at (write_slice memory (32 * norm 1 wp) 32 (norm 32 value)) rp =
    if norm 1 rp =? norm 1 wp then norm 32 value else word_at memory rp.
  Proof.
    unfold word_at.
    destruct (bit_cases wp) as [Hw|Hw]; destruct (bit_cases rp) as [Hr|Hr];
      rewrite Hw, Hr; cbn [Z.eqb Pos.eqb];
      try (rewrite read_slice_write_disjoint by lia; reflexivity);
      rewrite read_slice_write_same by lia;
      unfold read_slice; rewrite Z.shiftr_0_r;
      change (norm 32 (norm 32 value) = norm 32 value); apply norm_twice.
  Qed.
  Definition view memory rp count : list Z :=
    if count =? 0 then [] else
    if count =? 1 then [word_at memory rp]
    else [word_at memory rp; word_at memory (1 + norm 1 rp)].
  Definition queue_step (q : list Z) (push pop : bool) data :=
    let accepted_push := push && Nat.ltb (length q) 2 in
    let accepted_pop := pop && negb (Nat.eqb (length q) 0) in
    (if accepted_pop then tl q else q) ++ (if accepted_push then [norm 32 data] else []).
  Definition step_memory memory wp (push : bool) data :=
    if push then write_slice memory (32 * norm 1 wp) 32 (norm 32 data) else memory.
  Definition bitZ (b : bool) := if b then 1 else 0.
  Definition step_view memory rp wp count push pop data :=
    let p := push && (count <? 2) in
    let o := pop && (0 <? count) in
    view (step_memory memory wp p data) (norm 1 (norm 1 rp + bitZ o))
      (count + bitZ p - bitZ o).
  Lemma word_pointer_congr memory p q : norm 1 p = norm 1 q ->
    word_at memory p = word_at memory q.
  Proof. intros H. unfold word_at. now rewrite H. Qed.
  Lemma word_write_zero memory value p :
    word_at (write_slice memory 0 32 (norm 32 value)) p =
      if norm 1 p =? 0 then norm 32 value else word_at memory p.
  Proof. exact (word_write memory 0 value p). Qed.
  Lemma word_write_one memory value p :
    word_at (write_slice memory 32 32 (norm 32 value)) p =
      if norm 1 p =? 1 then norm 32 value else word_at memory p.
  Proof. exact (word_write memory 1 value p). Qed.
  #[local] Opaque word_at norm write_slice.
  Theorem packed_queue_step memory rp wp count push pop data :
    0 <= count <= 2 -> norm 1 wp = norm 1 (norm 1 rp + count) ->
    step_view memory rp wp count push pop data = queue_step (view memory rp count) push pop data.
  Proof.
    intros Hc Hw.
    assert (Hn : count = 0 \/ count = 1 \/ count = 2) by lia.
    destruct Hn as [Hn | [Hn | Hn]]; subst count;
      destruct (bit_cases rp) as [Hr|Hr];
      destruct push, pop;
      unfold step_view, step_memory, queue_step, view, bitZ;
      rewrite ?Hr;
      change (norm 1 0) with 0 in *; change (norm 1 1) with 1 in *;
      change (norm 1 2) with 0 in *; change (norm 1 3) with 1 in *;
      cbn in *; rewrite ?Hr in *;
      change (norm 1 0) with 0 in *; change (norm 1 1) with 1 in *;
      change (norm 1 2) with 0 in *; change (norm 1 3) with 1 in *;
      rewrite ?Hw; cbn;
      rewrite ?word_write_zero, ?word_write_one;
      change (norm 1 0) with 0 in *; change (norm 1 1) with 1 in *;
      change (norm 1 2) with 0 in *; change (norm 1 3) with 1 in *;
      cbn;
      try reflexivity.
    all: try (f_equal; apply word_pointer_congr; rewrite ?norm_twice, ?Hr; reflexivity).
  Qed.
End CV32E40PFetchFIFOQueue.
