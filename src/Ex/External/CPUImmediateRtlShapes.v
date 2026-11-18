(** Design independent: the Verilog idiom for RISC-V immediates with sign replication
    ({N{w[31]}} concatenated with the bit slices) evaluates to the riscv-coq decoder immediates.
    The five RTL assembly shapes [rimm_X W] over any 32-bit word expression W; the template route
    instantiates them with the elaborated assignment right-hand sides (checked by computation).
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import ZArith Lia Bool.
Require Import coqutil.Z.BitOps coqutil.Z.bitblast coqutil.Z.prove_Zeq_bitwise riscv.Utility.Utility Lang.ExtendedSV
 Ex.External.CPUImmediateShapes.
Import ExtendedSV CPUImmediateShapes.
Local Open Scope Z_scope.
Module CPUImmediateRtlShapes.

Definition rimm_I (W:Expr) : Expr := EConcat 32 (EReplicate 20 20 (sel 1 W 31)) (sel 12 W 20).
Definition rimm_S (W:Expr) : Expr := EConcat 32 (EReplicate 20 20 (sel 1 W 31)) (EConcat 12 (sel 7 W 25) (sel 5 W 7)).
Definition rimm_B (W:Expr) : Expr := EConcat 32 (EReplicate 19 19 (sel 1 W 31)) (EConcat 13 (sel 1 W 31) (EConcat 12 (sel 1 W 7)
  (EConcat 11 (sel 6 W 25) (EConcat 5 (sel 4 W 8) (EConst 1 0))))).
Definition rimm_J (W:Expr) : Expr := EConcat 32 (EReplicate 12 12 (sel 1 W 31)) (EConcat 20 (sel 8 W 12)
  (EConcat 12 (sel 1 W 20) (EConcat 11 (sel 10 W 21) (EConst 1 0)))).

Lemma replicate_ones n : replicate_bits n 1 1 = Z.ones (Z.of_nat n).
Proof.
 induction n; cbn [replicate_bits]; [reflexivity|].
 rewrite IHn. change (norm 1 1) with 1.
 apply Z.bits_inj'. intros k Hk. rewrite Z.lor_spec, Z.shiftl_spec by lia.
 change (Z.of_nat 1) with 1. rewrite Nat2Z.inj_succ.
 rewrite (Z.testbit_ones_nonneg (Z.succ (Z.of_nat n)) k) by lia.
 destruct (Z.eq_dec k 0) as [->|Hne].
 - cbn [Z.testbit]. destruct (0 <? Z.succ (Z.of_nat n)) eqn:E; [reflexivity|apply Z.ltb_ge in E; lia].
 - assert (Z.testbit 1 k = false) by (apply Z.bits_above_log2; [lia|cbn; lia]).
   rewrite H, Bool.orb_false_r.
   rewrite (Z.testbit_ones_nonneg (Z.of_nat n) (k-1)) by lia.
   destruct (Z.ltb_spec0 (k-1) (Z.of_nat n)); destruct (Z.ltb_spec0 k (Z.succ (Z.of_nat n))); try reflexivity; lia.
Qed.
Lemma replicate_zero n : replicate_bits n 1 0 = 0.
Proof. induction n; cbn [replicate_bits]; [reflexivity|]. rewrite IHn. reflexivity. Qed.

Lemma rep_sign n c : Z.land (replicate_bits n 1 (Z.land (Z.shiftr c 31) (Z.ones 1))) (Z.ones (Z.of_nat n))
 = if Z.testbit c 31 then Z.ones (Z.of_nat n) else 0.
Proof.
 rewrite (sign_val c (Z.testbit c 31) eq_refl). destruct (Z.testbit c 31).
 - rewrite replicate_ones. apply Z.land_diag.
 - rewrite replicate_zero. apply Z.land_0_l.
Qed.

Ltac close_rimm s W :=
 cbn [eval_expr expr_width sel];
 generalize (eval_expr s W); intro c;
 repeat change (norm 5 31) with 31; repeat change (norm 5 20) with 20; repeat change (norm 5 25) with 25;
 repeat change (norm 5 7) with 7; repeat change (norm 5 8) with 8; repeat change (norm 5 12) with 12;
 repeat change (norm 5 21) with 21; repeat change (norm 5 0) with 0;
 repeat rewrite norm_ones;
 repeat rewrite rep_sign;
 try (match goal with |- context [Z.testbit ?c 31] => destruct (Z.testbit c 31) eqn:Tsign end);
 repeat match goal with |- context [Z.of_nat ?n] => let m := eval cbv in (Z.of_nat n) in change (Z.of_nat n) with m end.

Theorem eval_rimm_I s W : eval_expr s (rimm_I W) = norm 32 (isa_imm_I (eval_expr s W)).
Proof. unfold rimm_I, isa_imm_I. close_rimm s W. all: finish_imm. Qed.
Theorem eval_rimm_S s W : eval_expr s (rimm_S W) = norm 32 (isa_imm_S (eval_expr s W)).
Proof. unfold rimm_S, isa_imm_S. close_rimm s W. all: finish_imm. Qed.
Theorem eval_rimm_B s W : eval_expr s (rimm_B W) = norm 32 (isa_imm_B (eval_expr s W)).
Proof. unfold rimm_B, isa_imm_B. close_rimm s W. all: finish_imm. Qed.
Theorem eval_rimm_J s W : eval_expr s (rimm_J W) = norm 32 (isa_imm_J (eval_expr s W)).
Proof. unfold rimm_J, isa_imm_J. close_rimm s W. all: finish_imm. all: (replace (i - 20 + 31) with 31 by lia; rewrite Tsign; reflexivity). Qed.
End CPUImmediateRtlShapes.
Print Assumptions CPUImmediateRtlShapes.eval_rimm_I.
Print Assumptions CPUImmediateRtlShapes.eval_rimm_S.
Print Assumptions CPUImmediateRtlShapes.eval_rimm_B.
Print Assumptions CPUImmediateRtlShapes.eval_rimm_J.
