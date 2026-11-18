(** Expression-level instance of the carry-isolated adder (design independent; CPUCarryIsolatedAdder is the Z-level fact).
    The RTL builds two 36-bit words ra, rb (gap-bit layout of CPUCarryIsolatedAdder.ci_in), adds their sign extensions to
    37 bits and reads four byte lanes at bits 1, 10, 19, 28.  [eval_ci_result] : if ra, rb hold ci_in 1 1 1 1 a and
    ci_in cin 0 0 0 b, the concatenated lanes evaluate to (a+b+cin) mod 2^32.
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import ZArith Lia Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVBankAlignment Ex.External.CPUCarryIsolatedAdder.
Import ExtendedSV ExtendedSVWordInvariant ExtendedSVBankAlignment CPUCarryIsolatedAdder.
Local Open Scope Z_scope.
Module CPUCarryIsolatedExpr.

Definition ci_sum_expr (ra rb:signal) : Expr := EBinary 37 BAdd (EExtend 37 true (EVar 36 ra)) (EExtend 37 true (EVar 36 rb)).
Definition ci_result_expr (ra rb:signal) : Expr :=
 EConcat 32 (ESel 8 (ci_sum_expr ra rb) (EConst 6 28)) (EConcat 24 (ESel 8 (ci_sum_expr ra rb) (EConst 6 19))
  (EConcat 16 (ESel 8 (ci_sum_expr ra rb) (EConst 6 10)) (ESel 8 (ci_sum_expr ra rb) (EConst 6 1)))).

Lemma lor_add_disjoint x y k : 0 <= k -> 0 <= x < 2^k -> Z.lor x (Z.shiftl y k) = x + y * 2^k.
Proof.
 intros Hk Hx. rewrite Z.shiftl_mul_pow2 by lia.
 assert (E1 : Z.land x (Z.ones k) = x) by (rewrite Z.land_ones by lia; apply Z.mod_small; lia).
 assert (E2 : Z.land (y*2^k) (Z.ones k) = 0) by (rewrite Z.land_ones by lia; apply Z.mod_mul; apply Z.pow_nonzero; lia).
 assert (Hl : Z.land x (y*2^k) = 0).
 { rewrite <- E1 at 1. rewrite <- Z.land_assoc. rewrite (Z.land_comm (Z.ones k)). rewrite E2. apply Z.land_0_r. }
 pose proof (Z.add_lor_land x (y*2^k)) as H. rewrite Hl in H. lia.
Qed.

Lemma lane_shift k T m q : 0 <= k <= 28 -> ((T - 2^36*m + 2^37*q) / 2^k) mod 256 = (T / 2^k) mod 256.
Proof.
 intros Hk.
 assert (Hp : 2^36 = 2^k * (256 * 2^(28-k))).
 { replace 256 with (2^8) by reflexivity. rewrite <- Z.pow_add_r by lia. rewrite <- Z.pow_add_r by lia. f_equal. lia. }
 assert (Hq : 2^37 = 2 * 2^36) by reflexivity.
 assert (Hpos : 0 < 2^k) by (apply Z.pow_pos_nonneg; lia).
 replace (T - 2^36*m + 2^37*q) with (T + ((2^(28-k) * (2*q - m)) * 256) * 2^k) by (rewrite Hq, Hp; ring).
 rewrite Z.div_add by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma ci_in_bound g0 g1 g2 g3 x : 0 <= x < 4294967296 -> 0 <= g0 <= 1 -> 0 <= g1 <= 1 -> 0 <= g2 <= 1 -> 0 <= g3 <= 1 ->
 0 <= ci_in g0 g1 g2 g3 x < 2^36.
Proof.
 intros Hx H0 H1 H2 H3. unfold ci_in.
 pose proof (Z.mod_pos_bound x 256 ltac:(lia)). pose proof (Z.mod_pos_bound (x/256) 256 ltac:(lia)).
 pose proof (Z.mod_pos_bound (x/65536) 256 ltac:(lia)). pose proof (Z.mod_pos_bound (x/16777216) 256 ltac:(lia)).
 change (2^36) with 68719476736. lia.
Qed.

Lemma sext_ci X : 0 <= X < 2^36 -> exists m, 0 <= m <= 1 /\ norm 37 (signed_value 36 X) = (X - 2^36*m) mod 2^37.
Proof.
 intros H. unfold signed_value. cbn [Nat.eqb Nat.pred]. rewrite (norm_mod 36 X). change (2 ^ Z.of_nat 36) with (2^36).
 rewrite Z.mod_small by lia. rewrite norm_mod. change (2 ^ Z.of_nat 37) with (2^37).
 change (2 ^ Z.of_nat 36) with (2^36). destruct (Z.testbit X (Z.of_nat 35)).
- exists 1. split; [lia|]. f_equal.
 - exists 0. split; [lia|]. f_equal. try lia.
Qed.

Theorem eval_ci_result s ra rb a b cin : 0 <= a < 4294967296 -> 0 <= b < 4294967296 -> (cin = 0 \/ cin = 1) ->
 norm 36 (read_signal s ra) = ci_in 1 1 1 1 a -> norm 36 (read_signal s rb) = ci_in cin 0 0 0 b ->
 eval_expr s (ci_result_expr ra rb) = (a + b + cin) mod 4294967296.
Proof.
 intros Ha Hb Hc Hra Hrb.
 rewrite <- (carry_isolated_add a b cin Ha Hb Hc).
 assert (Hcb : 0 <= cin <= 1) by (destruct Hc; lia).
 pose proof (ci_in_bound 1 1 1 1 a Ha ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as BA.
 pose proof (ci_in_bound cin 0 0 0 b Hb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as BB.
 destruct (sext_ci _ BA) as [m1 [M1 E1]]. destruct (sext_ci _ BB) as [m2 [M2 E2]].
 set (T := ci_in 1 1 1 1 a + ci_in cin 0 0 0 b).
 assert (HS : exists q, eval_expr s (ci_sum_expr ra rb) = T - 2^36*(m1+m2) + 2^37*q).
 { unfold ci_sum_expr. cbn [eval_expr expr_width]. rewrite Hra, Hrb. rewrite E1, E2.
   rewrite norm_mod. change (2 ^ Z.of_nat 37) with (2^37).
   rewrite <- Z.add_mod by lia.
   replace (ci_in 1 1 1 1 a - 2 ^ 36 * m1 + (ci_in cin 0 0 0 b - 2 ^ 36 * m2)) with (T - 2^36*(m1+m2)) by (subst T; lia).
   rewrite Z.mod_eq by lia. exists (-((T - 2^36*(m1+m2)) / 2^37)). lia. }
 destruct HS as [q Hq].
 assert (Hlane : forall k, 0 <= k <= 28 -> eval_expr s (ESel 8 (ci_sum_expr ra rb) (EConst 6 k)) = (T / 2^k) mod 256).
 { intros k Hk. cbn [eval_expr]. rewrite Hq. rewrite (norm_mod 6 k). change (2 ^ Z.of_nat 6) with 64. rewrite Z.mod_small by lia.
   rewrite Z.shiftr_div_pow2 by lia. rewrite norm_mod. change (2 ^ Z.of_nat 8) with 256. rewrite (lane_shift k T (m1+m2) q Hk). reflexivity. }
 unfold ci_result_expr. cbn [eval_expr expr_width].
 assert (L1 := Hlane 1 ltac:(lia)). assert (L10 := Hlane 10 ltac:(lia)). assert (L19 := Hlane 19 ltac:(lia)). assert (L28 := Hlane 28 ltac:(lia)).
 cbn [eval_expr] in L1, L10, L19, L28.
 rewrite L1, L10, L19, L28. unfold ci_out.
 change (2^1) with 2 in *. change (2^10) with 1024 in *. change (2^19) with 524288 in *. change (2^28) with 268435456 in *.
 pose proof (Z.mod_pos_bound (T/2) 256 ltac:(lia)) as B0. pose proof (Z.mod_pos_bound (T/1024) 256 ltac:(lia)) as B1.
 pose proof (Z.mod_pos_bound (T/524288) 256 ltac:(lia)) as B2. pose proof (Z.mod_pos_bound (T/268435456) 256 ltac:(lia)) as B3.
 generalize ((T/2) mod 256) ((T/1024) mod 256) ((T/524288) mod 256) ((T/268435456) mod 256) B0 B1 B2 B3.
 intros l0 l1 l2 l3 B0' B1' B2' B3'.
 change (Z.of_nat 24) with 24. change (Z.of_nat 16) with 16. change (Z.of_nat 8) with 8.
 assert (S1 : norm 16 (Z.lor (Z.shiftl l1 8) l0) = l0 + l1*256).
 { rewrite Z.lor_comm, (lor_add_disjoint l0 l1 8 ltac:(lia) ltac:(change (2^8) with 256; lia)). rewrite norm_mod. change (2 ^ Z.of_nat 16) with 65536.
   apply Z.mod_small. change (2^8) with 256. lia. }
 rewrite S1.
 assert (S2 : norm 24 (Z.lor (Z.shiftl l2 16) (l0 + l1*256)) = l0 + l1*256 + l2*65536).
 { rewrite Z.lor_comm, (lor_add_disjoint (l0 + l1*256) l2 16 ltac:(lia) ltac:(change (2^16) with 65536; lia)). rewrite norm_mod. change (2 ^ Z.of_nat 24) with 16777216.
   apply Z.mod_small. change (2^16) with 65536. lia. }
 rewrite S2. rewrite Z.lor_comm, (lor_add_disjoint (l0 + l1*256 + l2*65536) l3 24 ltac:(lia) ltac:(change (2^24) with 16777216; lia)).
 rewrite norm_mod. change (2 ^ Z.of_nat 32) with 4294967296. rewrite Z.mod_small by (change (2^24) with 16777216; lia).
 change (2^24) with 16777216. lia.
Qed.
End CPUCarryIsolatedExpr.
Print Assumptions CPUCarryIsolatedExpr.eval_ci_result.
