(** Design independent: the "carry-isolation" wide adder used by byte-vector ALUs.
    Each 8-bit lane of the operands is placed in a 9-bit slot of a 36-bit word ({a[31:24],g,a[23:16],g,a[15:8],g,a[7:0],g0}),
    the gap bits of operand A are 1 and of operand B are 0, the carry-in is the bit-0 gap of B, and the sum lanes are read back
    from the gap-shifted positions.  In scalar (non-vector) mode this is the plain 32-bit addition [a + b + cin] mod 2^32.
    Z-level statement over any width-agnostic arithmetic; the expression-level instance is made by the design's generator.
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import ZArith Lia.
Local Open Scope Z_scope.
Module CPUCarryIsolatedAdder.

Definition ci_in (g0 g1 g2 g3 x : Z) : Z :=
 g0 + 2*(x mod 256) + 512*g1 + 1024*((x/256) mod 256) + 262144*g2 + 524288*((x/65536) mod 256)
 + 134217728*g3 + 268435456*((x/16777216) mod 256).
Definition ci_out (S : Z) : Z :=
 ((S/2) mod 256) + 256*((S/1024) mod 256) + 65536*((S/524288) mod 256) + 16777216*((S/268435456) mod 256).

Lemma carry_bound x : 0 <= x < 512 -> 0 <= x/256 <= 1.
Proof. intro H. split; [apply Z.div_pos; lia|]. assert (x/256 < 2) by (apply Z.div_lt_upper_bound; lia). lia. Qed.

Lemma lane D u r Q : 0 < D -> 0 <= u < D -> 0 <= r < 256 -> (u + D*(r + 256*Q)) / D mod 256 = r.
Proof.
 intros HD Hu Hr. rewrite (Z.mul_comm D (r + 256*Q)), Z.add_comm, Z.div_add_l by lia. rewrite (Z.div_small u D) by lia.
 rewrite Z.add_0_r. replace (r + 256*Q) with (r + Q*256) by lia. rewrite Z.mod_add by lia. apply Z.mod_small; lia.
Qed.

Lemma bytes x : 0 <= x < 4294967296 ->
 x = x mod 256 + 256*((x/256) mod 256) + 65536*((x/65536) mod 256) + 16777216*((x/16777216) mod 256)
 /\ (0 <= x mod 256 < 256 /\ 0 <= (x/256) mod 256 < 256 /\ 0 <= (x/65536) mod 256 < 256 /\ 0 <= (x/16777216) mod 256 < 256).
Proof.
 intro H.
 assert (E2 : x/65536 = (x/256)/256) by (rewrite Z.div_div by lia; reflexivity).
 assert (E3 : x/16777216 = (x/65536)/256) by (rewrite Z.div_div by lia; reflexivity).
 assert (B3 : 0 <= x/16777216 < 256) by (split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]).
 pose proof (Z.div_mod x 256 ltac:(lia)) as D1.
 pose proof (Z.div_mod (x/256) 256 ltac:(lia)) as D2.
 pose proof (Z.div_mod (x/65536) 256 ltac:(lia)) as D3.
 rewrite <- E2 in D2. rewrite <- E3 in D3.
 pose proof (Z.mod_pos_bound x 256 ltac:(lia)). pose proof (Z.mod_pos_bound (x/256) 256 ltac:(lia)).
 pose proof (Z.mod_pos_bound (x/65536) 256 ltac:(lia)). pose proof (Z.mod_pos_bound (x/16777216) 256 ltac:(lia)).
 rewrite (Z.mod_small (x/16777216) 256) by lia.
 split; [|lia]. lia.
Qed.

Theorem carry_isolated_add a b cin : 0 <= a < 4294967296 -> 0 <= b < 4294967296 -> (cin = 0 \/ cin = 1) ->
 ci_out (ci_in 1 1 1 1 a + ci_in cin 0 0 0 b) = (a + b + cin) mod 4294967296.
Proof.
 intros Ha Hb Hc. unfold ci_in, ci_out.
 assert (Hcb : 0 <= cin <= 1) by (destruct Hc; lia).
 destruct (bytes a Ha) as [Ea Ra]. destruct (bytes b Hb) as [Eb Rb].
 remember (a/16777216 mod 256) as a3. remember (a/65536 mod 256) as a2. remember (a/256 mod 256) as a1. remember (a mod 256) as a0.
 remember (b/16777216 mod 256) as b3. remember (b/65536 mod 256) as b2. remember (b/256 mod 256) as b1. remember (b mod 256) as b0.
 clear Heqa0 Heqa1 Heqa2 Heqa3 Heqb0 Heqb1 Heqb2 Heqb3.
 destruct Ra as [Ra0 [Ra1 [Ra2 Ra3]]]. destruct Rb as [Rb0 [Rb1 [Rb2 Rb3]]].
 pose proof (Z.div_mod (a0+b0+cin) 256 ltac:(lia)) as E0. pose proof (Z.mod_pos_bound (a0+b0+cin) 256 ltac:(lia)) as R0.
 remember ((a0+b0+cin)/256) as c1. remember ((a0+b0+cin) mod 256) as r0.
 assert (Hc1 : 0 <= c1 <= 1) by (subst c1; apply carry_bound; lia).
 pose proof (Z.div_mod (a1+b1+c1) 256 ltac:(lia)) as E1. pose proof (Z.mod_pos_bound (a1+b1+c1) 256 ltac:(lia)) as R1.
 remember ((a1+b1+c1)/256) as c2. remember ((a1+b1+c1) mod 256) as r1.
 assert (Hc2 : 0 <= c2 <= 1) by (subst c2; apply carry_bound; lia).
 pose proof (Z.div_mod (a2+b2+c2) 256 ltac:(lia)) as E2. pose proof (Z.mod_pos_bound (a2+b2+c2) 256 ltac:(lia)) as R2.
 remember ((a2+b2+c2)/256) as c3. remember ((a2+b2+c2) mod 256) as r2.
 assert (Hc3 : 0 <= c3 <= 1) by (subst c3; apply carry_bound; lia).
 pose proof (Z.div_mod (a3+b3+c3) 256 ltac:(lia)) as E3. pose proof (Z.mod_pos_bound (a3+b3+c3) 256 ltac:(lia)) as R3.
 remember ((a3+b3+c3)/256) as c4. remember ((a3+b3+c3) mod 256) as r3.
 assert (Hc4 : 0 <= c4 <= 1) by (subst c4; apply carry_bound; lia).
 match goal with |- context[(?e / 2) mod 256] => remember e as S eqn:HS end.
 assert (HS2 : S = (1-cin) + 2*r0 + 512*(1-c1) + 1024*r1 + 262144*(1-c2) + 524288*r2 + 134217728*(1-c3) + 268435456*r3 + 68719476736*c4) by lia.
 rewrite HS2. clear HS HS2 Heqc1 Heqc2 Heqc3 Heqc4 Heqr0 Heqr1 Heqr2 Heqr3.
 assert (L0 : ((1-cin) + 2*r0 + 512*(1-c1) + 1024*r1 + 262144*(1-c2) + 524288*r2 + 134217728*(1-c3) + 268435456*r3 + 68719476736*c4)/2 mod 256 = r0).
 { replace ((1-cin) + 2*r0 + 512*(1-c1) + 1024*r1 + 262144*(1-c2) + 524288*r2 + 134217728*(1-c3) + 268435456*r3 + 68719476736*c4) with ((1-cin) + 2*(r0 + 256*((1-c1) + 2*r1 + 512*(1-c2) + 1024*r2 + 262144*(1-c3) + 524288*r3 + 134217728*c4))) by lia. apply (lane 2); lia. }
 assert (L1 : ((1-cin) + 2*r0 + 512*(1-c1) + 1024*r1 + 262144*(1-c2) + 524288*r2 + 134217728*(1-c3) + 268435456*r3 + 68719476736*c4)/1024 mod 256 = r1).
 { replace ((1-cin) + 2*r0 + 512*(1-c1) + 1024*r1 + 262144*(1-c2) + 524288*r2 + 134217728*(1-c3) + 268435456*r3 + 68719476736*c4) with (((1-cin) + 2*r0 + 512*(1-c1)) + 1024*(r1 + 256*((1-c2) + 2*r2 + 512*(1-c3) + 1024*r3 + 262144*c4))) by lia. apply (lane 1024); lia. }
 assert (L2 : ((1-cin) + 2*r0 + 512*(1-c1) + 1024*r1 + 262144*(1-c2) + 524288*r2 + 134217728*(1-c3) + 268435456*r3 + 68719476736*c4)/524288 mod 256 = r2).
 { replace ((1-cin) + 2*r0 + 512*(1-c1) + 1024*r1 + 262144*(1-c2) + 524288*r2 + 134217728*(1-c3) + 268435456*r3 + 68719476736*c4) with (((1-cin) + 2*r0 + 512*(1-c1) + 1024*r1 + 262144*(1-c2)) + 524288*(r2 + 256*((1-c3) + 2*r3 + 512*c4))) by lia. apply (lane 524288); lia. }
 assert (L3 : ((1-cin) + 2*r0 + 512*(1-c1) + 1024*r1 + 262144*(1-c2) + 524288*r2 + 134217728*(1-c3) + 268435456*r3 + 68719476736*c4)/268435456 mod 256 = r3).
 { replace ((1-cin) + 2*r0 + 512*(1-c1) + 1024*r1 + 262144*(1-c2) + 524288*r2 + 134217728*(1-c3) + 268435456*r3 + 68719476736*c4) with (((1-cin) + 2*r0 + 512*(1-c1) + 1024*r1 + 262144*(1-c2) + 524288*r2 + 134217728*(1-c3)) + 268435456*(r3 + 256*c4)) by lia. apply (lane 268435456); lia. }
 rewrite L0, L1, L2, L3.
 assert (Eab : a + b + cin = r0 + 256*r1 + 65536*r2 + 16777216*r3 + 4294967296*c4) by lia.
 rewrite Eab. apply (Z.mod_unique_pos _ _ c4); lia.
Qed.

End CPUCarryIsolatedAdder.
Print Assumptions CPUCarryIsolatedAdder.carry_isolated_add.
