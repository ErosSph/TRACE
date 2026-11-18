(** Design independent plumbing and Z-level lemmas for datapath facts of the template route (EX result, compare unit, target
    adders, immediate decoder).  Used by the generated Bzeeno modules BzTmplEx*.
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSVBankAlignment coqutil.Z.BitOps coqutil.Z.bitblast coqutil.Z.prove_Zeq_bitwise Lang.ExtendedSV Lang.ExtendedSVSymExec
 Lang.ExtendedSVWordInvariant Ex.External.CPUImmediateShapes Ex.External.CPUImmediateRtlShapes Ex.External.CPUISARegView.
Import ListNotations ExtendedSV ExtendedSVSymExec ExtendedSVWordInvariant CPUImmediateShapes CPUImmediateRtlShapes CPUISARegView.
Local Open Scope Z_scope.
Module CPUDatapathFacts.

(* ---- facts plumbing ---- *)
Definition outs_facts (l:list ((signal*nat)*Z)) : Facts := map (fun t => (EVar (snd (fst t)) (fst (fst t)), snd t)) l.
Lemma decout_facts s l : DecOut s l -> FactsHold s (outs_facts l).
Proof. intros H e z HI. unfold outs_facts in HI. apply in_map_iff in HI as [t [Ht Hin]]. inversion Ht; subst. cbn [eval_expr]. exact (H t Hin). Qed.
Lemma facts_app s a b : FactsHold s a -> FactsHold s b -> FactsHold s (a++b).
Proof. intros Ha Hb e z HI. apply in_app_or in HI as [HI|HI]; [apply Ha|apply Hb]; exact HI. Qed.
Lemma norm_self w v : norm w (norm w v) = norm w v.
Proof. apply norm_idempotent. Qed.
Lemma range_of_norm w (x v:Z) : norm w x = v -> norm w v = v.
Proof. intro H. rewrite <- H. apply norm_idempotent. Qed.

Lemma norm_lo w1 w2 x : (w1 <= w2)%nat -> norm w1 (norm w2 x) = norm w1 x.
Proof. intro H. rewrite !norm_ones. prove_Zeq_bitwise. Qed.
Lemma norm_wide w1 w2 x : (w1 <= w2)%nat -> norm w2 (norm w1 x) = norm w1 x.
Proof. intro H. rewrite !norm_ones. prove_Zeq_bitwise. Qed.

Lemma norm_add_r w a b : norm w (a + norm w b) = norm w (a + b).
Proof. rewrite !ExtendedSVBankAlignment.norm_mod. apply Zplus_mod_idemp_r. Qed.
Lemma norm_add_l w a b : norm w (norm w a + b) = norm w (a + b).
Proof. rewrite !ExtendedSVBankAlignment.norm_mod. apply Zplus_mod_idemp_l. Qed.
Lemma bit0_add_even a b : Z.testbit a 0 = false -> Z.testbit b 0 = false -> Z.testbit (a + b) 0 = false.
Proof. rewrite !Z.bit0_odd. intros Ha Hb. rewrite Z.odd_add, Ha, Hb. reflexivity. Qed.

(* ---- slices ---- *)
Lemma slice_val w s n : 0 <= s -> norm n (Z.shiftr w s) = bitSlice w s (s + Z.of_nat n).
Proof. intro Hs. rewrite (bs_norm w s (s + Z.of_nat n) Hs) by lia. replace (s + Z.of_nat n - s) with (Z.of_nat n) by lia. now rewrite Nat2Z.id. Qed.

Lemma shamt5 w : bitSlice w 25 26 = 0 -> norm 5 (Z.shiftr w 20) = bitSlice w 20 26.
Proof.
 intro H. pose proof (bit_from_bs w H) as T. rewrite (bs_norm w 20 26) by lia.
 change (Z.to_nat (26 - 20)) with 6%nat. rewrite !norm_ones. ofnat. prove_Zeq_bitwise.
 assert (i = 5) by lia. subst i. replace (5 + 20) with 25 by lia. exact (eq_sym T).
Qed.

(* ---- JALR / branch target: bit 0 cleared ---- *)
Lemma clear0_land x : norm 32 (Z.shiftl (Z.shiftr (norm 32 x) 1) 1) = norm 32 (Z.land x (Z.lnot 1)).
Proof.
 rewrite !norm_ones. ofnat. prove_Zeq_bitwise.
 - assert (i = 0) by lia. subst i. cbn. rewrite andb_false_r. reflexivity.
 - replace (i - 1 + 1) with i by lia. assert (Z.testbit 1 i = false) by (apply Z.bits_above_log2; [lia|cbn; lia]).
   rewrite H. cbn [negb]. rewrite andb_true_r. reflexivity.
Qed.

Lemma rtl_clear0 y : norm 32 (Z.lor (Z.shiftl (norm 31 (Z.shiftr y 1)) (Z.of_nat 1)) 0) = norm 32 (Z.shiftl (Z.shiftr y 1) 1).
Proof. rewrite Z.lor_0_r. rewrite !norm_ones. ofnat. prove_Zeq_bitwise. Qed.
Lemma clear0_land_even x : Z.testbit x 0 = false -> Z.land x (Z.lnot 1) = x.
Proof.
 intro H. prove_Zeq_bitwise.
 destruct (Z.eq_dec i 0) as [->|Hne].
 - rewrite H. reflexivity.
 - assert (Z.testbit 1 i = false) by (apply Z.bits_above_log2; [lia|cbn; lia]). rewrite H0. cbn. rewrite andb_true_r. reflexivity.
Qed.
Lemma clear0_even x : Z.testbit x 0 = false -> norm 32 (Z.shiftl (Z.shiftr (norm 32 x) 1) 1) = norm 32 x.
Proof. intro H. rewrite clear0_land, (clear0_land_even x H). reflexivity. Qed.
Lemma isa_imm_B_even w : Z.testbit (isa_imm_B w) 0 = false.
Proof.
 unfold isa_imm_B. rewrite signExtend_alt_bitwise by lia. unfold signExtend_bitwise.
 destruct (Z.testbit _ (13 - 1)); rewrite ?Z.lor_spec, ?Z.land_spec, ?Z.lor_spec; rewrite ?Z.shiftl_spec_low by lia; cbn; reflexivity.
Qed.
Lemma isa_imm_J_even w : Z.testbit (isa_imm_J w) 0 = false.
Proof.
 unfold isa_imm_J. rewrite signExtend_alt_bitwise by lia. unfold signExtend_bitwise.
 destruct (Z.testbit _ (21 - 1)); rewrite ?Z.lor_spec, ?Z.land_spec, ?Z.lor_spec; rewrite ?Z.shiftl_spec_low by lia; cbn; reflexivity.
Qed.

(* ---- sign replication gated by a control bit that is 1 (Bzeeno's signext) ---- *)
Definition rsx_I (W S:Expr) : Expr := EConcat 32 (EReplicate 20 20 (EBinary 1 BAnd (sel 1 W 31) S)) (sel 12 W 20).
Definition rsx_S (W S:Expr) : Expr := EConcat 32 (EReplicate 20 20 (EBinary 1 BAnd (sel 1 W 31) S)) (EConcat 12 (sel 7 W 25) (sel 5 W 7)).
Definition rsx_B (W S:Expr) : Expr := EConcat 32 (EReplicate 19 19 (EBinary 1 BAnd (sel 1 W 31) S)) (EConcat 13 (sel 1 W 31) (EConcat 12 (sel 1 W 7)
  (EConcat 11 (sel 6 W 25) (EConcat 5 (sel 4 W 8) (EConst 1 0))))).
Definition rsx_J (W S:Expr) : Expr := EConcat 32 (EReplicate 12 12 (EBinary 1 BAnd (sel 1 W 31) S)) (EConcat 20 (sel 8 W 12)
  (EConcat 12 (sel 1 W 20) (EConcat 11 (sel 10 W 21) (EConst 1 0)))).
(* Bzeeno's branch immediate: twenty sign bits, then w[7], w[30:25], w[11:8], 0 *)
Definition rimm_B2 (W:Expr) : Expr := EConcat 32 (EReplicate 20 20 (sel 1 W 31)) (EConcat 12 (sel 1 W 7)
  (EConcat 11 (sel 6 W 25) (EConcat 5 (sel 4 W 8) (EConst 1 0)))).
Definition rsx_B2 (W S:Expr) : Expr := EConcat 32 (EReplicate 20 20 (EBinary 1 BAnd (sel 1 W 31) S)) (EConcat 12 (sel 1 W 7)
  (EConcat 11 (sel 6 W 25) (EConcat 5 (sel 4 W 8) (EConst 1 0)))).
Theorem eval_rimm_B2 s W : eval_expr s (rimm_B2 W) = norm 32 (isa_imm_B (eval_expr s W)).
Proof. unfold rimm_B2, isa_imm_B. close_rimm s W. all: finish_imm. all: (replace (i - 12 + 31) with 31 by lia; rewrite Tsign; reflexivity). Qed.
Lemma and_sx s W S : eval_expr s S = 1 -> eval_expr s (EBinary 1 BAnd (sel 1 W 31) S) = eval_expr s (sel 1 W 31).
Proof.
 intro H. cbn [eval_expr]. rewrite H. unfold sel. cbn [eval_expr].
 generalize (Z.shiftr (eval_expr s W) (norm 5 31)). intro c.
 rewrite !norm_ones. ofnat. prove_Zeq_bitwise.
 assert (i = 0) by lia. subst i. cbn. rewrite andb_true_r. reflexivity.
Qed.
Lemma eval_rsx_I s W S : eval_expr s S = 1 -> eval_expr s (rsx_I W S) = eval_expr s (rimm_I W).
Proof. intro H. unfold rsx_I, rimm_I. cbn [eval_expr expr_width]. pose proof (and_sx s W S H) as A. cbn [eval_expr] in A. rewrite A. reflexivity. Qed.
Lemma eval_rsx_S s W S : eval_expr s S = 1 -> eval_expr s (rsx_S W S) = eval_expr s (rimm_S W).
Proof. intro H. unfold rsx_S, rimm_S. cbn [eval_expr expr_width]. pose proof (and_sx s W S H) as A. cbn [eval_expr] in A. rewrite A. reflexivity. Qed.
Lemma eval_rsx_B s W S : eval_expr s S = 1 -> eval_expr s (rsx_B W S) = eval_expr s (rimm_B W).
Proof. intro H. unfold rsx_B, rimm_B. cbn [eval_expr expr_width]. pose proof (and_sx s W S H) as A. cbn [eval_expr] in A. rewrite A. reflexivity. Qed.
Lemma eval_rsx_B2 s W S : eval_expr s S = 1 -> eval_expr s (rsx_B2 W S) = eval_expr s (rimm_B2 W).
Proof. intro H. unfold rsx_B2, rimm_B2. cbn [eval_expr expr_width]. pose proof (and_sx s W S H) as A. cbn [eval_expr] in A. rewrite A. reflexivity. Qed.
Lemma eval_rsx_J s W S : eval_expr s S = 1 -> eval_expr s (rsx_J W S) = eval_expr s (rimm_J W).
Proof. intro H. unfold rsx_J, rimm_J. cbn [eval_expr expr_width]. pose proof (and_sx s W S H) as A. cbn [eval_expr] in A. rewrite A. reflexivity. Qed.
End CPUDatapathFacts.
Print Assumptions CPUDatapathFacts.norm_add_r.
Print Assumptions CPUDatapathFacts.norm_add_l.
Print Assumptions CPUDatapathFacts.bit0_add_even.
Print Assumptions CPUDatapathFacts.eval_rimm_B2.
Print Assumptions CPUDatapathFacts.eval_rsx_B2.
Print Assumptions CPUDatapathFacts.rtl_clear0.
Print Assumptions CPUDatapathFacts.norm_lo.
Print Assumptions CPUDatapathFacts.norm_wide.
Print Assumptions CPUDatapathFacts.decout_facts.
Print Assumptions CPUDatapathFacts.facts_app.
Print Assumptions CPUDatapathFacts.slice_val.
Print Assumptions CPUDatapathFacts.shamt5.
Print Assumptions CPUDatapathFacts.clear0_land.
Print Assumptions CPUDatapathFacts.clear0_even.
Print Assumptions CPUDatapathFacts.clear0_land_even.
Print Assumptions CPUDatapathFacts.isa_imm_B_even.
Print Assumptions CPUDatapathFacts.isa_imm_J_even.
Print Assumptions CPUDatapathFacts.eval_rsx_I.
Print Assumptions CPUDatapathFacts.eval_rsx_S.
Print Assumptions CPUDatapathFacts.eval_rsx_B.
Print Assumptions CPUDatapathFacts.eval_rsx_J.

