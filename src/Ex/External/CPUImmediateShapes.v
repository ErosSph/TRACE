(** Design independent: the five RISC-V immediate assembly shapes as ExtendedSV expressions over any 32-bit word
    expression W, and their value equal to the riscv-coq decoder immediates (signExtend of the bit slices of [Decode.decode]).
    A design reuses them by showing that (the reduced arm of) its immediate expression is [imm_X W] by computation.
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import ZArith Lia Bool.
Require Import coqutil.Z.BitOps coqutil.Z.bitblast coqutil.Z.prove_Zeq_bitwise riscv.Utility.Utility Lang.ExtendedSV.
Import ExtendedSV.
Local Open Scope Z_scope.
Module CPUImmediateShapes.

Definition sel w W lsb := ESel w W (EConst 5 lsb).
Definition sign_fill n W := ECond n (sel 1 W 31) (EConst n (2^(Z.of_nat n) - 1)) (EConst n 0).

Definition imm_I (W : Expr) : Expr := EConcat 32 (sign_fill 20 W) (sel 12 W 20).
Definition imm_S (W : Expr) : Expr := EConcat 32 (sign_fill 20 W) (EConcat 12 (sel 7 W 25) (sel 5 W 7)).
Definition imm_B (W : Expr) : Expr := EConcat 32 (sign_fill 19 W) (EConcat 13 (sel 1 W 31) (EConcat 12 (sel 1 W 7)
  (EConcat 11 (sel 6 W 25) (EConcat 5 (sel 4 W 8) (EConst 1 0))))).
Definition imm_J (W : Expr) : Expr := EConcat 32 (sign_fill 11 W) (EConcat 21 (sel 1 W 31) (EConcat 20 (sel 8 W 12)
  (EConcat 12 (sel 1 W 20) (EConcat 11 (sel 10 W 21) (EConst 1 0))))).
Definition imm_U (W : Expr) : Expr := EConcat 32 (sel 20 W 12) (EConst 12 0).

(* ISA immediates exactly as in riscv.Spec.Decode.decode *)
Definition isa_imm_I (w : Z) := signExtend 12 (bitSlice w 20 32).
Definition isa_imm_S (w : Z) := signExtend 12 (Z.lor (Z.shiftl (bitSlice w 25 32) 5) (bitSlice w 7 12)).
Definition isa_imm_B (w : Z) := signExtend 13 (Z.lor (Z.lor (Z.lor (Z.shiftl (bitSlice w 31 32) 12) (Z.shiftl (bitSlice w 25 31) 5))
  (Z.shiftl (bitSlice w 8 12) 1)) (Z.shiftl (bitSlice w 7 8) 11)).
Definition isa_imm_J (w : Z) := signExtend 21 (Z.lor (Z.lor (Z.lor (Z.shiftl (bitSlice w 31 32) 20) (Z.shiftl (bitSlice w 21 31) 1))
  (Z.shiftl (bitSlice w 20 21) 11)) (Z.shiftl (bitSlice w 12 20) 12)).
Definition isa_imm_U (w : Z) := signExtend 32 (Z.shiftl (bitSlice w 12 32) 12).

Lemma norm_ones w v : norm w v = Z.land v (Z.ones (Z.of_nat w)).
Proof. unfold norm, mask. rewrite Z.ones_equiv. reflexivity. Qed.

Lemma sign_val c b : Z.testbit c 31 = b -> Z.land (Z.shiftr c 31) (Z.ones 1) = if b then 1 else 0.
Proof. intro T. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.shiftr_spec by lia.
 rewrite Z.testbit_ones by lia.
 destruct (Z.eq_dec n 0) as [->|Hne].
 - rewrite Z.add_0_l, T. destruct b; reflexivity.
 - assert (Hf : (n <? 1) = false) by (apply Z.ltb_ge; lia). rewrite Hf. rewrite !andb_false_r.
   destruct b.
   + change 1 with (Z.ones 1). rewrite Z.testbit_ones by lia. rewrite Hf. rewrite !andb_false_r. reflexivity.
   + symmetry. apply Z.bits_0. Qed.
Lemma sign_guard c : Z.eqb (Z.land (Z.shiftr c 31) (Z.ones 1)) 0 = negb (Z.testbit c 31).
Proof. destruct (Z.testbit c 31) eqn:T; rewrite (sign_val c _ T); reflexivity. Qed.

Ltac close_imm s W :=
 cbn [eval_expr expr_width sel sign_fill];
 generalize (eval_expr s W); intro c;
 repeat change (norm 5 31) with 31; repeat change (norm 5 20) with 20; repeat change (norm 5 25) with 25;
 repeat change (norm 5 7) with 7; repeat change (norm 5 8) with 8; repeat change (norm 5 12) with 12;
 repeat change (norm 5 21) with 21; repeat change (norm 5 0) with 0;
 repeat rewrite norm_ones;
 repeat rewrite sign_guard;
 try (match goal with |- context [Z.testbit ?c 31] => destruct (Z.testbit c 31) eqn:Tsign end; cbn [negb]);
 repeat match goal with |- context [Z.of_nat ?n] => let m := eval cbv in (Z.of_nat n) in change (Z.of_nat n) with m end.

Lemma tb_ones n m : 0 <= n -> 0 <= m < n -> Z.testbit (2^n - 1) m = true.
Proof. intros. rewrite Z.sub_1_r, <- Z.ones_equiv by lia. rewrite Z.ones_spec_low by lia. reflexivity. Qed.
Lemma tb_ones_hi n m : 0 <= n -> n <= m -> Z.testbit (2^n - 1) m = false.
Proof. intros. rewrite Z.sub_1_r, <- Z.ones_equiv by lia. rewrite Z.ones_spec_high by lia. reflexivity. Qed.

Ltac finish_imm :=
 match goal with Ts : Z.testbit ?c0 31 = ?b |- _ =>
   assert (Tk : forall k, k = 31 -> Z.testbit c0 k = b) by (intros k ->; exact Ts);
   prove_Zeq_bitwise;
   repeat (first [ match goal with |- context [Z.testbit c0 ?k] => rewrite (Tk k eq_refl) end | rewrite tb_ones by lia | rewrite tb_ones_hi by lia ]);
   try reflexivity
 end.

Theorem eval_imm_I s W : eval_expr s (imm_I W) = norm 32 (isa_imm_I (eval_expr s W)).
Proof. unfold imm_I, isa_imm_I. close_imm s W. all: finish_imm. Qed.
Theorem eval_imm_S s W : eval_expr s (imm_S W) = norm 32 (isa_imm_S (eval_expr s W)).
Proof. unfold imm_S, isa_imm_S. close_imm s W. all: finish_imm. Qed.
Theorem eval_imm_B s W : eval_expr s (imm_B W) = norm 32 (isa_imm_B (eval_expr s W)).
Proof. unfold imm_B, isa_imm_B. close_imm s W. all: finish_imm. Qed.
Theorem eval_imm_J s W : eval_expr s (imm_J W) = norm 32 (isa_imm_J (eval_expr s W)).
Proof. unfold imm_J, isa_imm_J. close_imm s W. all: finish_imm. Qed.
Theorem eval_imm_U s W : eval_expr s (imm_U W) = norm 32 (isa_imm_U (eval_expr s W)).
Proof. unfold imm_U, isa_imm_U. close_imm s W. prove_Zeq_bitwise. Qed.
End CPUImmediateShapes.
Print Assumptions CPUImmediateShapes.eval_imm_I.
Print Assumptions CPUImmediateShapes.eval_imm_S.
Print Assumptions CPUImmediateShapes.eval_imm_B.
Print Assumptions CPUImmediateShapes.eval_imm_J.
Print Assumptions CPUImmediateShapes.eval_imm_U.
