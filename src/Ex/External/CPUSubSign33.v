(** Sign bit of the 33-bit subtraction used by comparators (design independent, template route, 2026-11-04).
    A core that computes [{a[31],a} - {b[31],b}] (srv32 SLT/BLT/BGE) and reads bit 32 as "a < b signed" is correct:
    [slt_signbit]; the zero-extended variant [{1'b0,a} - {1'b0,b}] (SLTU/BLTU/BGEU) is [sltu_signbit].
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVBankAlignment.
Import ExtendedSV ExtendedSVBankAlignment.
Local Open Scope Z_scope.
Module CPUSubSign33.
Definition sx (a : Z) : Z := Z.lor (Z.shiftl (norm 1 (Z.shiftr a 31)) (Z.of_nat 32)) a.

Lemma tb31 a : 0 <= a < 2 ^ 32 -> Z.testbit a 31 = true <-> 2 ^ 31 <= a.
Proof.
  intro H. rewrite Z.testbit_odd. rewrite Z.shiftr_div_pow2 by lia.
  destruct (Z_lt_ge_dec a (2 ^ 31)) as [L|G].
  - rewrite (Z.div_small a (2 ^ 31)) by lia. cbn. split; [discriminate | lia].
  - assert (E : a / 2 ^ 31 = 1) by (apply Z.le_antisymm; [apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia | apply Z.div_le_lower_bound; lia]).
    rewrite E. cbn. split; [lia | reflexivity].
Qed.

Lemma n1 a : 0 <= a < 2 ^ 32 -> norm 1 (Z.shiftr a 31) = if Z.testbit a 31 then 1 else 0.
Proof.
  intro H. rewrite norm_mod, Z.shiftr_div_pow2 by lia.
  destruct (Z.testbit a 31) eqn:T.
  - apply tb31 in T; [|exact H]. assert (E : a / 2 ^ 31 = 1) by (apply Z.le_antisymm; [apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia | apply Z.div_le_lower_bound; lia]).
    rewrite E. reflexivity.
  - assert (L : a < 2 ^ 31) by (destruct (Z_lt_ge_dec a (2 ^ 31)) as [L|G]; [exact L|];
      exfalso; assert (X : Z.testbit a 31 = true) by (apply tb31; lia); congruence).
    rewrite (Z.div_small a (2 ^ 31)) by lia. reflexivity.
Qed.

Lemma land_pow2_small n a : 0 <= n -> 0 <= a < 2 ^ n -> Z.land (2 ^ n) a = 0.
Proof.
  intros Hn H. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.pow2_bits_eqb by lia. rewrite Z.bits_0.
  destruct (n =? k) eqn:E; [|reflexivity]. apply Z.eqb_eq in E. subst k.
  destruct (Z.eq_dec a 0) as [->|NZ]; [apply Z.bits_0|].
  assert (HL : Z.log2 a < n) by (apply (proj1 (Z.log2_lt_pow2 a n ltac:(lia))); lia).
  rewrite (Z.bits_above_log2 a n) by lia. reflexivity.
Qed.

Lemma lor_pow2_small n a : 0 <= n -> 0 <= a < 2 ^ n -> Z.lor (2 ^ n) a = 2 ^ n + a.
Proof.
  intros Hn H. pose proof (Z.add_lor_land (2 ^ n) a) as E. rewrite (land_pow2_small n a Hn H) in E. lia.
Qed.

Lemma p31 : 2 ^ 31 = 2147483648. Proof. reflexivity. Qed.
Lemma p32 : 2 ^ 32 = 4294967296. Proof. reflexivity. Qed.
Lemma p33 : 2 ^ 33 = 8589934592. Proof. reflexivity. Qed.
Lemma sx_val a : 0 <= a < 2 ^ 32 -> sx a = signed_value 32 a mod 2 ^ 33.
Proof.
  intro H. unfold sx, signed_value. rewrite n1 by exact H.
  assert (HN : norm 32 a = a) by (rewrite norm_mod; apply Z.mod_small; cbn; lia).
  rewrite HN. cbn [Nat.eqb Nat.pred]. change (Z.of_nat 31) with 31. change (Z.of_nat 32) with 32.
  destruct (Z.testbit a 31) eqn:T.
  - apply tb31 in T; [|exact H].
    assert (Hs : Z.shiftl 1 32 = 2 ^ 32) by reflexivity. rewrite Hs.
    rewrite lor_pow2_small by (cbn in *; lia).
    rewrite ?p31, ?p32, ?p33 in *. apply Z.mod_unique with (q := -1); lia.
  - rewrite Z.shiftl_0_l, Z.lor_0_l. cbn. rewrite Z.mod_small; [reflexivity|]. rewrite ?p31, ?p32, ?p33 in *. lia.
Qed.

Lemma sv_range a : 0 <= a < 2 ^ 32 -> - 2 ^ 31 <= signed_value 32 a < 2 ^ 31.
Proof.
  intro H. unfold signed_value. assert (HN : norm 32 a = a) by (rewrite norm_mod; apply Z.mod_small; cbn; lia).
  rewrite HN. cbn [Nat.eqb Nat.pred]. change (Z.of_nat 31) with 31. change (Z.of_nat 32) with 32.
  destruct (Z.testbit a 31) eqn:T.
  - apply tb31 in T; [|exact H]. rewrite ?p31, ?p32 in *. lia.
  - assert (L : a < 2 ^ 31) by (destruct (Z_lt_ge_dec a (2 ^ 31)) as [L|G]; [exact L|];
      exfalso; assert (X : Z.testbit a 31 = true) by (apply tb31; lia); congruence).
    rewrite ?p31, ?p32 in *. lia.
Qed.

Lemma sign_bit33 D : - 2 ^ 32 < D < 2 ^ 32 -> (Z.shiftr (D mod 2 ^ 33) 32) mod 2 ^ Z.of_nat 1 = if D <? 0 then 1 else 0.
Proof.
  intro H. rewrite ?p32 in H. rewrite Z.shiftr_div_pow2 by lia. rewrite ?p33, ?p32. destruct (Z_lt_dec D 0) as [N|N].
  - assert (E : D mod 8589934592 = D + 8589934592) by (symmetry; apply Z.mod_unique with (q := -1); lia).
    rewrite E. assert (E2 : (D + 8589934592) / 4294967296 = 1) by
      (apply Z.le_antisymm; [apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia | apply Z.div_le_lower_bound; lia]).
    rewrite E2. destruct (D <? 0) eqn:C; [reflexivity|]. apply Z.ltb_ge in C. lia.
  - assert (E : D mod 8589934592 = D) by (apply Z.mod_small; lia).
    rewrite E. assert (E2 : D / 4294967296 = 0) by (apply Z.div_small; lia). rewrite E2.
    destruct (D <? 0) eqn:C; [apply Z.ltb_lt in C; lia|]. reflexivity.
Qed.

Theorem slt_signbit a b : 0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 ->
  norm 1 (Z.shiftr (norm 33 (norm 33 (norm 33 (sx a) - norm 33 (sx b)))) 32) = boolz (signed_value 32 a <? signed_value 32 b).
Proof.
  intros Ha Hb. rewrite (sx_val a Ha), (sx_val b Hb). rewrite !norm_mod. change (Z.of_nat 33) with 33.
  assert (HM : 2 ^ 33 <> 0) by (rewrite p33; lia).
  repeat rewrite Z.mod_mod by exact HM.
  rewrite <- Zminus_mod. repeat rewrite Z.mod_mod by exact HM.
  pose proof (sv_range a Ha). pose proof (sv_range b Hb). rewrite ?p31, ?p32 in *.
  rewrite sign_bit33 by lia. unfold boolz. destruct (signed_value 32 a <? signed_value 32 b) eqn:C1; destruct (signed_value 32 a - signed_value 32 b <? 0) eqn:C2; try reflexivity.
  - apply Z.ltb_lt in C1. apply Z.ltb_ge in C2. lia.
  - apply Z.ltb_ge in C1. apply Z.ltb_lt in C2. lia.
Qed.

Theorem sltu_signbit a b : 0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 ->
  norm 1 (Z.shiftr (norm 33 (norm 33 (norm 33 a - norm 33 b))) 32) = boolz (a <? b).
Proof.
  intros Ha Hb. rewrite !norm_mod. change (Z.of_nat 33) with 33.
  assert (HM : 2 ^ 33 <> 0) by (rewrite p33; lia).
  repeat rewrite Z.mod_mod by exact HM.
  rewrite <- Zminus_mod. repeat rewrite Z.mod_mod by exact HM.
  rewrite ?p32 in *. rewrite sign_bit33 by lia. unfold boolz.
  destruct (a <? b) eqn:C1; destruct (a - b <? 0) eqn:C2; try reflexivity.
  - apply Z.ltb_lt in C1. apply Z.ltb_ge in C2. lia.
  - apply Z.ltb_ge in C1. apply Z.ltb_lt in C2. lia.
Qed.

Lemma sv_def a : 0 <= a < 2 ^ 32 -> signed_value 32 a = if 2 ^ 31 <=? a then a - 2 ^ 32 else a.
Proof.
  intro H. unfold signed_value. assert (HN : norm 32 a = a) by (rewrite norm_mod; apply Z.mod_small; cbn; lia).
  rewrite HN. cbn [Nat.eqb Nat.pred]. change (Z.of_nat 31) with 31. change (Z.of_nat 32) with 32.
  destruct (Z.testbit a 31) eqn:T.
  - apply tb31 in T; [|exact H]. destruct (2 ^ 31 <=? a) eqn:C; [reflexivity|]. apply Z.leb_gt in C. lia.
  - assert (L : a < 2 ^ 31) by (destruct (Z_lt_ge_dec a (2 ^ 31)) as [L|G]; [exact L|];
      exfalso; assert (X : Z.testbit a 31 = true) by (apply tb31; lia); congruence).
    destruct (2 ^ 31 <=? a) eqn:C; [apply Z.leb_le in C; lia|]. reflexivity.
Qed.

Theorem sub33_zero a b : 0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 ->
  (0 =? norm 33 (norm 33 (norm 33 (sx a) - norm 33 (sx b)))) = (a =? b).
Proof.
  intros Ha Hb. rewrite (sx_val a Ha), (sx_val b Hb). rewrite !norm_mod. change (Z.of_nat 33) with 33.
  assert (HM : 2 ^ 33 <> 0) by (rewrite p33; lia).
  repeat rewrite Z.mod_mod by exact HM.
  rewrite <- Zminus_mod. repeat rewrite Z.mod_mod by exact HM.
  pose proof (sv_def a Ha) as Da. pose proof (sv_def b Hb) as Db.
  rewrite ?p31, ?p32 in *. rewrite Da, Db.
  destruct (a =? b) eqn:E.
  - apply Z.eqb_eq in E. subst b. replace (_ - _) with 0 by lia. rewrite Z.mod_0_l by exact HM. reflexivity.
  - apply Z.eqb_neq in E.
    destruct (Z.eq_dec ((if 2147483648 <=? a then a - 4294967296 else a) - (if 2147483648 <=? b then b - 4294967296 else b)) 0) as [Z|NZ].
    + exfalso. destruct (2147483648 <=? a) eqn:C1; destruct (2147483648 <=? b) eqn:C2; lia.
    + destruct (0 =? _ mod 2 ^ 33) eqn:Q; [|reflexivity]. exfalso. apply Z.eqb_eq in Q.
      symmetry in Q. apply Z.mod_divide in Q; [|exact HM]. destruct Q as [c Hc]. rewrite p33 in Hc.
      destruct (2147483648 <=? a) eqn:C1; destruct (2147483648 <=? b) eqn:C2; apply Z.leb_le in C1 || apply Z.leb_gt in C1; apply Z.leb_le in C2 || apply Z.leb_gt in C2; lia.
Qed.
End CPUSubSign33.
Print Assumptions CPUSubSign33.slt_signbit.
Print Assumptions CPUSubSign33.sltu_signbit.
Print Assumptions CPUSubSign33.sub33_zero.
