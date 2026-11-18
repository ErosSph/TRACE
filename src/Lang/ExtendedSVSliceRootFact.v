(** From two covering slice equations to a full-root fact (template route, Steel, 2026-11-04).

    Generic, design independent, additive.  proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.
    A root written by two disjoint covering slice processes (low [w1] bits, then [w2] bits above) obtains the fact
    [EVar (w1+w2) r = z1 + z2 << w1] when both slice right-hand sides are decided by the facts. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVSymExec Lang.ExtendedSVSliceBits.
Import ListNotations ExtendedSV ExtendedSVSymExec ExtendedSVSliceBits.
Local Open Scope Z_scope.
Module ExtendedSVSliceRootFact.

Lemma slice_root_fact s r (w1 w2:nat) e1 e2 z1 z2 z :
 SliceEq s r 0 w1 e1 -> SliceEq s r (Z.of_nat w1) w2 e2 ->
 eval_expr s e1 = z1 -> eval_expr s e2 = z2 ->
 Z.lor (norm w1 z1) (Z.shiftl (norm w2 z2) (Z.of_nat w1)) = z ->
 FactsHold s [(EVar (w1+w2) r, z)].
Proof.
 intros [_ H1] [_ H2] X1 X2 Hz e z' HI. destruct HI as [HI|[]]. inversion HI; subst e z'; clear HI.
 rewrite X1 in H1. rewrite X2 in H2.
 cbn [eval_expr]. rewrite Z.shiftr_0_r in H1. rewrite <- Hz.
 apply Z.bits_inj'. intros n Hn.
 rewrite (testbit_norm (w1+w2) (read_signal s r) n Hn), Z.lor_spec, Z.shiftl_spec by lia.
 assert (T1 := f_equal (fun v => Z.testbit v n) H1). cbv beta in T1.
 rewrite !testbit_norm in T1 by exact Hn.
 assert (T2 : 0 <= n - Z.of_nat w1 -> Z.testbit (read_signal s r) n && (n - Z.of_nat w1 <? Z.of_nat w2) = Z.testbit (norm w2 z2) (n - Z.of_nat w1)).
 { intro Hm. assert (T := f_equal (fun v => Z.testbit v (n - Z.of_nat w1)) H2). cbv beta in T.
   rewrite !testbit_norm in T by exact Hm. rewrite Z.shiftr_spec in T by lia. replace (n - Z.of_nat w1 + Z.of_nat w1) with n in T by lia.
   rewrite testbit_norm by exact Hm. exact T. }
 rewrite Nat2Z.inj_add.
 destruct (Z.ltb_spec n (Z.of_nat w1)).
 - rewrite (Z.testbit_neg_r (norm w2 z2) (n - Z.of_nat w1)) by lia.
   assert (Hl : (n <? Z.of_nat w1) = true) by (apply Z.ltb_lt; lia). rewrite !Bool.andb_true_r in T1.
   rewrite (testbit_norm w1 z1 n Hn), Hl, Bool.andb_true_r, Bool.orb_false_r, <- T1.
   assert (Hl2 : (n <? Z.of_nat w1 + Z.of_nat w2) = true) by (apply Z.ltb_lt; lia). rewrite Hl2. apply Bool.andb_true_r.
 - assert (Hl : (n <? Z.of_nat w1) = false) by (apply Z.ltb_nlt; lia).
   rewrite (testbit_norm w1 z1 n Hn), Hl, Bool.andb_false_r, Bool.orb_false_l.
   specialize (T2 ltac:(lia)).
   destruct (Z.ltb_spec (n - Z.of_nat w1) (Z.of_nat w2)).
   + assert (Hl2 : (n <? Z.of_nat w1 + Z.of_nat w2) = true) by (apply Z.ltb_lt; lia). rewrite Hl2, Bool.andb_true_r.
     rewrite Bool.andb_true_r in T2. exact T2.
   + assert (Hl2 : (n <? Z.of_nat w1 + Z.of_nat w2) = false) by (apply Z.ltb_nlt; lia). rewrite Hl2, Bool.andb_false_r.
     rewrite (testbit_norm w2 z2 (n - Z.of_nat w1) ltac:(lia)). assert (Hl3 : (n - Z.of_nat w1 <? Z.of_nat w2) = false) by (apply Z.ltb_nlt; lia). rewrite Hl3. symmetry. apply Bool.andb_false_r.
Qed.
End ExtendedSVSliceRootFact.
Print Assumptions ExtendedSVSliceRootFact.slice_root_fact.
