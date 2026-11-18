(** Additive algebraic rules for the condition-directed reducer (template route).
    Each rule rewrites a boolean-style operator that has one already-constant
    operand. Soundness is proved for all states; nothing here mentions an RTL.
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import List ZArith Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVConditionalReduction.
Import ListNotations ExtendedSV ExtendedSVConditionalReduction.
Local Open Scope Z_scope.
Module ExtendedSVConditionalReductionAlgebra.

Lemma norm_zero w : norm w 0 = 0.
Proof. unfold norm. apply Z.land_0_l. Qed.

Lemma norm_one_land v x : norm 1 v = 1 -> norm 1 (Z.land v x) = norm 1 x.
Proof.
 unfold norm, mask; cbn; intro H.
 apply Z.bits_inj'; intros n Hn.
 rewrite !Z.land_spec. 
 assert (Hv : Z.testbit v 0 = true).
 { assert (E : Z.testbit (Z.land v 1) 0 = true) by (rewrite H; reflexivity).
   rewrite Z.land_spec in E. cbn in E. rewrite andb_true_r in E. exact E. }
 destruct (Z.eq_dec n 0) as [->|Hne].
 - rewrite Hv. reflexivity.
 - assert (Z.testbit 1 n = false) by (destruct n; [contradiction| |lia]; reflexivity).
   rewrite H0. rewrite !andb_false_r. reflexivity.
Qed.

Lemma norm_one_lor v x : norm 1 v = 1 -> norm 1 (Z.lor v x) = 1.
Proof.
 unfold norm, mask; cbn; intro H.
 assert (Hv : Z.testbit v 0 = true).
 { assert (E : Z.testbit (Z.land v 1) 0 = true) by (rewrite H; reflexivity).
   rewrite Z.land_spec in E. cbn in E. rewrite andb_true_r in E. exact E. }
 apply Z.bits_inj'; intros n Hn.
 rewrite Z.land_spec, Z.lor_spec.
 destruct (Z.eq_dec n 0) as [->|Hne].
 - rewrite Hv. reflexivity.
 - assert (Z.testbit 1 n = false) by (destruct n; [contradiction| |lia]; reflexivity).
   rewrite H0. rewrite andb_false_r. reflexivity.
Qed.

Lemma and_zero_l facts w wa v b : norm wa v = 0 ->
 Reduction facts (EBinary w BAnd (EConst wa v) b) (EConst w 0).
Proof.
 intro H; constructor; [reflexivity|]. intros s _; cbn [eval_expr].
 rewrite H, Z.land_0_l; reflexivity.
Qed.

Lemma and_zero_r facts w wa v b : norm wa v = 0 ->
 Reduction facts (EBinary w BAnd b (EConst wa v)) (EConst w 0).
Proof.
 intro H; constructor; [reflexivity|]. intros s _; cbn [eval_expr].
 rewrite H, Z.land_0_r; reflexivity.
Qed.

Lemma or_zero_l facts w wa v b : norm wa v = 0 ->
 Reduction facts (EBinary w BOr (EConst wa v) b) (EExtend w false b).
Proof.
 intro H; constructor; [reflexivity|]. intros s _; cbn [eval_expr].
 rewrite H, Z.lor_0_l; reflexivity.
Qed.

Lemma or_zero_r facts w wa v b : norm wa v = 0 ->
 Reduction facts (EBinary w BOr b (EConst wa v)) (EExtend w false b).
Proof.
 intro H; constructor; [reflexivity|]. intros s _; cbn [eval_expr].
 rewrite H, Z.lor_0_r; reflexivity.
Qed.

Lemma or_one_l facts wa v b : norm 1 v = 1 -> wa = 1%nat ->
 Reduction facts (EBinary 1 BOr (EConst wa v) b) (EConst 1 1).
Proof.
 intros H ->; constructor; [reflexivity|]. intros s _; cbn [eval_expr].
 rewrite H. apply norm_one_lor. reflexivity.
Qed.

Lemma or_one_r facts wa v b : norm 1 v = 1 -> wa = 1%nat ->
 Reduction facts (EBinary 1 BOr b (EConst wa v)) (EConst 1 1).
Proof.
 intros H ->; constructor; [reflexivity|]. intros s _; cbn [eval_expr].
 rewrite H, Z.lor_comm. apply norm_one_lor. reflexivity.
Qed.

Lemma and_one_l facts v b : norm 1 v = 1 ->
 Reduction facts (EBinary 1 BAnd (EConst 1 v) b) (EExtend 1 false b).
Proof.
 intro H; constructor; [reflexivity|]. intros s _; cbn [eval_expr].
 rewrite H. apply norm_one_land. reflexivity.
Qed.

Lemma and_one_r facts v b : norm 1 v = 1 ->
 Reduction facts (EBinary 1 BAnd b (EConst 1 v)) (EExtend 1 false b).
Proof.
 intro H; constructor; [reflexivity|]. intros s _; cbn [eval_expr].
 rewrite H, Z.land_comm. apply norm_one_land. reflexivity.
Qed.
End ExtendedSVConditionalReductionAlgebra.
Print Assumptions ExtendedSVConditionalReductionAlgebra.and_one_r.
Print Assumptions ExtendedSVConditionalReductionAlgebra.or_one_r.
