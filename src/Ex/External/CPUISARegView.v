(** Design independent: the ISA register file seen as an abstract view Z -> Z (x0 reads 0), the effect of a register write on
    that view (the `setRegister` effect of [dataop_post] / [jump_post] / [branch_post]), and the bank relation [RFRel] after a write.
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSVBankAlignment coqutil.Z.BitOps coqutil.Z.bitblast coqutil.Z.prove_Zeq_bitwise Ex.External.CPUImmediateShapes Lang.ExtendedSV Lang.ExtendedSVBankOperand Ex.External.CV32E40PReq40StateRel Ex.RvCore.FormalSpec
 coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte.
Import CV32E40PReq40StateRel ExtendedSVBankOperand ExtendedSV CPUImmediateShapes.
Local Open Scope Z_scope.
Module CPUISARegView.
Lemma bs_norm w s e : 0 <= s -> s <= e -> bitSlice w s e = norm (Z.to_nat (e - s)) (Z.shiftr w s).
Proof. intros Hs He. unfold bitSlice, norm, mask. rewrite Z2Nat.id by lia.
 replace (Z.lnot (Z.shiftl (-1) (e - s))) with (2 ^ (e - s) - 1).
 - reflexivity.
 - rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.lnot_eq_pred_opp. lia.
Qed.

Lemma bit_from_bs w : bitSlice w 25 26 = 0 -> Z.testbit w 25 = false.
Proof. intro H. unfold bitSlice in H.
 assert (E : Z.testbit (Z.land (Z.shiftr w 25) (Z.lnot (Z.shiftl (-1) (26 - 25)))) 0 = false) by (rewrite H; reflexivity).
 rewrite Z.land_spec, Z.shiftr_spec in E by lia. cbn in E. rewrite andb_true_r in E. exact E. Qed.
Ltac ofnat := repeat match goal with |- context [Z.of_nat ?n] => let m := eval cbv in (Z.of_nat n) in change (Z.of_nat n) with m end.
(** RV32 shift immediates: with shamtHi = 0 the RTL's low five immediate bits are the ISA shift amount. *)
Lemma shamt_imm w : bitSlice w 25 26 = 0 -> norm 5 (norm 32 (isa_imm_I w)) = bitSlice w 20 26.
Proof. intro H. pose proof (bit_from_bs w H) as T. unfold isa_imm_I. rewrite !CPUImmediateShapes.norm_ones. ofnat.
 prove_Zeq_bitwise. assert (i = 5) by lia. subst i. exact (eq_sym T). Qed.
Lemma bs7_shift w : bitSlice w 25 26 = 0 -> norm 7 (Z.shiftr w 25) = Z.shiftl (bitSlice w 26 32) 1.
Proof. intro H2. pose proof (bit_from_bs w H2) as T. unfold bitSlice. rewrite CPUImmediateShapes.norm_ones. ofnat.
 prove_Zeq_bitwise. assert (i = 0) by lia. subst i. exact T. Qed.
Section ISA.
Context {word : Interface.word 32} {BW : Bitwidth 32}.
Context {Registers : map.map Z word} {Mem : map.map word byte}.
Context {word_ok : word.ok word} {registers_ok : map.ok Registers} {mem_ok : map.ok Mem}.

Definition regs_view (regs : Registers) (i : Z) : Z :=
 if Z.eqb i 0 then 0 else match map.get regs i with Some v => word.unsigned v | None => 0 end.
Definition isa_view (s : FormalSpec.State) (i : Z) : Z := regs_view (getRegs s) i.

Lemma uw_link (pc : word) : word.unsigned (word.add pc (word.of_Z 4 : word)) = norm 32 (word.unsigned pc + 4).
Proof. rewrite word.unsigned_add, word.unsigned_of_Z. unfold word.wrap. rewrite ExtendedSVBankAlignment.norm_mod. cbn.
 rewrite <- Zplus_mod_idemp_r. reflexivity. Qed.

Lemma view_zero s : isa_view s 0 = 0. Proof. reflexivity. Qed.

(** Universal initial-register view, independent of the instruction memory.
    proof_author: OpenAI Codex; narrow_llm_new_generic_proof: 1.
    Existing design-specific initial states specialize this theorem. *)
Lemma isa_view_initial_state (initial_imem : Mem) i :
 isa_view (FormalSpec.initial_state initial_imem) i = 0.
Proof.
 unfold isa_view, regs_view. destruct (Z.eqb i 0); [reflexivity|].
 cbn [getRegs FormalSpec.initial_state]. rewrite map.get_empty. reflexivity.
Qed.

Lemma view_formal s r : word.unsigned (formal_register_word s r) = isa_view s r.
Proof. unfold formal_register_word, isa_view, regs_view. destruct (Z.eq_dec r 0) as [->|N].
 - cbn. rewrite word.unsigned_of_Z. reflexivity.
 - assert (E : Z.eqb r 0 = false) by (apply Z.eqb_neq; exact N). rewrite E.
   destruct (map.get (getRegs s) r); [reflexivity|]. rewrite word.unsigned_of_Z. reflexivity. Qed.

Lemma view_put (regs : Registers) rd v i :
 regs_view (if Z.eq_dec rd 0 then regs else map.put regs rd v) i =
 if (Z.eqb i rd && negb (Z.eqb rd 0))%bool then word.unsigned v else regs_view regs i.
Proof. destruct (Z.eq_dec rd 0) as [->|N].
 - cbn. rewrite andb_false_r. reflexivity.
 - assert (E : Z.eqb rd 0 = false) by (apply Z.eqb_neq; exact N). rewrite E, andb_true_r.
   unfold regs_view. destruct (Z.eqb i rd) eqn:EI.
   + apply Z.eqb_eq in EI. subst i. rewrite E, map.get_put_same. reflexivity.
   + destruct (Z.eqb i 0); [reflexivity|]. rewrite map.get_put_diff; [reflexivity|].
     intro H. apply Z.eqb_neq in EI. congruence. Qed.

Lemma view_after_write (s post : FormalSpec.State) rd v :
 getRegs post = (if Z.eq_dec rd 0 then getRegs s else map.put (getRegs s) rd v) ->
 forall i, isa_view post i = if (Z.eqb i rd && negb (Z.eqb rd 0))%bool then word.unsigned v else isa_view s i.
Proof. intros H i. unfold isa_view. rewrite H. apply view_put. Qed.

Lemma view_after_keep (s post : FormalSpec.State) : getRegs post = getRegs s -> forall i, isa_view post i = isa_view s i.
Proof. intros H i. unfold isa_view. rewrite H. reflexivity. Qed.

(** The bank after an RTL write of lane [dptr] equals the ISA view after the ISA register write. *)
Theorem rfrel_after_write bank (s post : FormalSpec.State) rd v dptr V :
 RFRel bank (fun i => if Z.eqb i dptr then V else isa_view s i) ->
 dptr = rd -> V = (if Z.eqb 0 dptr then 0 else word.unsigned v) ->
 getRegs post = (if Z.eq_dec rd 0 then getRegs s else map.put (getRegs s) rd v) ->
 RFRel bank (isa_view post).
Proof. intros [HL H0] HD HV HP. split.
 - intros i Hi. rewrite (HL i Hi). rewrite (view_after_write s post rd v HP i). subst dptr.
   destruct (Z.eqb i rd) eqn:EI.
   + apply Z.eqb_eq in EI. subst i. rewrite HV. destruct (Z.eqb 0 rd) eqn:E0.
     * apply Z.eqb_eq in E0. subst rd. cbn. reflexivity.
     * rewrite Z.eqb_sym in E0. rewrite E0. cbn. reflexivity.
   + cbn. reflexivity.
 - reflexivity. Qed.

Theorem rfrel_after_keep bank (s post : FormalSpec.State) dptr V :
 RFRel bank (fun i => if Z.eqb i dptr then V else isa_view s i) -> V = isa_view s dptr ->
 getRegs post = getRegs s -> RFRel bank (isa_view post).
Proof. intros [HL H0] HV HP. split.
 - intros i Hi. rewrite (HL i Hi), (view_after_keep s post HP i). destruct (Z.eqb i dptr) eqn:EI.
   + apply Z.eqb_eq in EI. subst i. exact HV.
   + reflexivity.
 - reflexivity. Qed.
End ISA.
End CPUISARegView.
Print Assumptions CPUISARegView.rfrel_after_write.
Print Assumptions CPUISARegView.rfrel_after_keep.
Print Assumptions CPUISARegView.view_formal.
Print Assumptions CPUISARegView.bs_norm.
Print Assumptions CPUISARegView.shamt_imm.
Print Assumptions CPUISARegView.bs7_shift.
