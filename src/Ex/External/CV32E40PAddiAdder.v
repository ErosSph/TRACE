(** Scalar byte-spaced carry network used by the actual CV32E40P ALU.
    No assumption about the expected sum is used. *)
From Coq Require Import ZArith Lia List.
Require Import Lang.ExtendedSV Lang.ExtendedSVBitSlice.
Import ExtendedSV ExtendedSVBitSlice ListNotations.
Local Open Scope Z_scope.
Module CV32E40PAddiAdder.
  Ltac div_facts t :=
    lazymatch t with
    | ?x / ?d => div_facts x; div_fact x d
    | ?x mod ?d => div_facts x; div_fact x d
    | ?f ?x => div_facts f; div_facts x
    | _ => idtac
    end
  with div_fact x d :=
    first [match goal with H : x = d * (x / d) + x mod d |- _ => idtac end
    | let E := fresh "D" in let B := fresh "B" in
      pose proof (Z.div_mod x d ltac:(lia)) as E;
      pose proof (Z.mod_pos_bound x d ltac:(lia)) as B].
  Ltac div_lia := match goal with |- ?G => div_facts G end; lia.
  Fixpoint pack_bytes (n : nat) (x : Z) : Z := match n with
    | O => 0 | S n => 2 * (x mod 256) + 512 * pack_bytes n (x / 256) end.
  Fixpoint carry_bits (n : nat) : Z := match n with
    | O => 0 | S n => 1 + 512 * carry_bits n end.
  Fixpoint unpack_bytes (n : nat) (x : Z) : Z := match n with
    | O => 0 | S n => x / 2 mod 256 + 256 * unpack_bytes n (x / 512) end.
  Lemma byte_carry a b c : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= c <= 1 ->
    0 <= (a+b+c)/256 <= 1.
  Proof. intros. div_lia. Qed.
  Lemma low_byte a b c h : 0 <= c <= 1 ->
    (2*a+2*b+1+c+512*h)/2 mod 256 = (a+b+c) mod 256.
  Proof.
    intros H. replace (2*a+2*b+1+c+512*h) with
      ((2*a+2*b+1+c)+ (256*h)*2) by ring.
    rewrite Z.div_add by lia.
    assert ((2*a+2*b+1+c)/2 = a+b+c) by div_lia.
    rewrite H0, (Z.mul_comm 256 h), Z.mod_add by lia. reflexivity.
  Qed.
  Lemma high_bytes a b c h : 0 <= c <= 1 ->
    (2*a+2*b+1+c+512*h)/512 = h+(a+b+c)/256.
  Proof.
    intros H. rewrite (Z.mul_comm 512 h), Z.div_add by lia.
    assert ((2*a+2*b+1+c)/512 = (a+b+c)/256) by div_lia. lia.
  Qed.
  Lemma mod_split x m : 0 < m ->
    x mod (256*m) = x mod 256 + 256 * ((x/256) mod m).
  Proof.
    intros Hm. symmetry. apply (Z.mod_unique _ _ ((x/256)/m)).
    - left. pose proof (Z.mod_pos_bound x 256 ltac:(lia)).
      pose proof (Z.mod_pos_bound (x/256) m Hm). nia.
    - pose proof (Z.div_mod x 256 ltac:(lia)).
      pose proof (Z.div_mod (x/256) m ltac:(lia)). nia.
  Qed.
  Theorem byte_spaced_add n a b c : 0 <= c <= 1 ->
    unpack_bytes n (pack_bytes n a + carry_bits n + pack_bytes n b + c) =
    (a+b+c) mod 256 ^ Z.of_nat n.
  Proof.
    revert a b c. induction n as [|n IH]; intros a b c Hc.
    - cbn. now rewrite Z.mod_1_r.
    - cbn [pack_bytes carry_bits unpack_bytes].
      replace (2*(a mod 256)+512*pack_bytes n (a/256)+
        (1+512*carry_bits n)+(2*(b mod 256)+512*pack_bytes n (b/256))+c)
        with (2*(a mod 256)+2*(b mod 256)+1+c+
          512*(pack_bytes n (a/256)+carry_bits n+pack_bytes n (b/256))) by ring.
      rewrite low_byte, high_bytes by exact Hc.
      rewrite IH by (apply byte_carry; try apply Z.mod_pos_bound; lia).
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      rewrite mod_split by (apply Z.pow_pos_nonneg; lia).
      assert (Hlo : (a mod 256+b mod 256+c) mod 256 = (a+b+c) mod 256).
      { div_lia. }
      assert (Hhi : a/256+b/256+(a mod 256+b mod 256+c)/256 = (a+b+c)/256).
      { pose proof (Z.div_mod a 256 ltac:(lia)).
        pose proof (Z.div_mod b 256 ltac:(lia)). div_lia. }
      now rewrite Hlo, Hhi.
  Qed.
  Definition pack (x : Z) :=
    2 * (x mod 256) + 1024 * (x / 256 mod 256) +
    524288 * (x / 65536 mod 256) + 268435456 * (x / 16777216 mod 256).
  Definition spacers := 134480385.
  Definition unpack (x : Z) :=
    x / 2 mod 256 + 256 * (x / 1024 mod 256) +
    65536 * (x / 524288 mod 256) + 16777216 * (x / 268435456 mod 256).

  Lemma pack_four x : pack_bytes 4 x = pack x.
  Proof.
    cbn [pack_bytes]. rewrite !Z.div_div by lia. unfold pack.
    change (256*256) with 65536. change (65536*256) with 16777216.
    ring.
  Qed.
  Lemma unpack_four x : unpack_bytes 4 x = unpack x.
  Proof.
    cbn [unpack_bytes]. rewrite !Z.div_div by lia. unfold unpack.
    change (512*2) with 1024. change (512*1024) with 524288.
    change (512*524288) with 268435456. ring.
  Qed.

  Theorem scalar_carry_network a b :
    unpack (pack a + spacers + pack b) = (a + b) mod 4294967296.
  Proof.
    pose proof (byte_spaced_add 4 a b 0 ltac:(lia)) as H.
    rewrite unpack_four, !pack_four in H.
    change (carry_bits 4) with spacers in H.
    change (256 ^ Z.of_nat 4) with 4294967296 in H.
    now rewrite !Z.add_0_r in H.
  Qed.

  Lemma norm_mod w x : norm w x = x mod 2 ^ Z.of_nat w.
  Proof.
    unfold norm, mask. replace (2 ^ Z.of_nat w - 1) with (Z.ones (Z.of_nat w))
      by (rewrite Z.ones_equiv; lia). apply Z.land_ones; lia.
  Qed.
  Lemma slice_div x off width : 0 <= off -> 0 <= width ->
    read_slice x off width = (x / 2 ^ off) mod 2 ^ width.
  Proof.
    intros. unfold read_slice. replace (2 ^ width - 1) with (Z.ones width)
      by (rewrite Z.ones_equiv; lia).
    rewrite Z.land_ones, Z.shiftr_div_pow2 by lia. reflexivity.
  Qed.
  Lemma split_mod x b m : 0 < b -> 0 < m ->
    x mod (b*m) = x mod b + b * ((x/b) mod m).
  Proof.
    intros Hb Hm. symmetry. apply (Z.mod_unique _ _ ((x/b)/m)).
    - left. pose proof (Z.mod_pos_bound x b Hb).
      pose proof (Z.mod_pos_bound (x/b) m Hm). nia.
    - pose proof (Z.div_mod x b ltac:(lia)).
      pose proof (Z.div_mod (x/b) m ltac:(lia)). nia.
  Qed.
  Lemma split_slice x off lo hi : 0 <= off -> 0 <= lo -> 0 <= hi ->
    read_slice x off (lo+hi) =
      read_slice x off lo + 2^lo * read_slice x (off+lo) hi.
  Proof.
    intros. rewrite !slice_div by lia. rewrite !Z.pow_add_r by lia.
    rewrite split_mod by (apply Z.pow_pos_nonneg; lia).
    rewrite Z.div_div by (try apply Z.pow_pos_nonneg; pose proof (Z.pow_pos_nonneg 2 off); lia).
    reflexivity.
  Qed.
  Lemma reconstruct36 x : norm 36 x =
    read_slice x 0 1 + 2*read_slice x 1 8 +
    512*(read_slice x 9 1 + 2*read_slice x 10 8) +
    262144*(read_slice x 18 1 + 2*read_slice x 19 8) +
    134217728*(read_slice x 27 1 + 2*read_slice x 28 8).
  Proof.
    change (norm 36 x) with (read_slice x 0 36).
    let split_at o l h :=
      let H := fresh "S" in
      pose proof (split_slice x o l h ltac:(lia) ltac:(lia) ltac:(lia)) as H;
      cbn -[read_slice Z.mul] in H; rewrite H; clear H in
    split_at 0 9 27; split_at 9 9 18; split_at 18 9 9;
    split_at 0 1 8; split_at 9 1 8; split_at 18 1 8; split_at 27 1 8.
    ring.
  Qed.
End CV32E40PAddiAdder.
