(** Design-independent: register-bank read ports and the "bank lanes = ISA registers, lane 0 = 0" relation.
    - [bank_port_value] / [bank_port_value_x0]: under a combinational LFP, a read-port wire driven by
      [ESel 32 (EVar W bank) idx] (optionally under the x0 mux [ECond (0 == rs) 0 ...]) equals a lane of the bank.
    - [RFRel packed view]: the lanes of the packed bank equal the abstract register view, and view 0 = 0.
    - operand clauses [a = view rs] and preservation of [RFRel] under a lane write / full reset / frame.
    No CPU, ISA or design names.
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import List ZArith Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVCheckedAssignmentBinding
 Lang.ExtendedSVBitSlice Lang.ExtendedSVRegisterBank Lang.ExtendedSVBankAlignment Lang.ExtendedSVBankRead.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVCheckedAssignmentBinding
 ExtendedSVBitSlice ExtendedSVRegisterBank ExtendedSVBankAlignment ExtendedSVBankRead.
Local Open Scope Z_scope.
Module ExtendedSVBankOperand.

Lemma lane_read_norm : forall w packed i, norm w (lane_read w packed i) = lane_read w packed i.
Proof.
 intros. unfold lane_read, read_slice, norm, mask. rewrite <- Z.land_assoc, Z.land_diag. reflexivity.
Qed.

Lemma eval_cond_unfold : forall s g y n w, eval_expr s (ECond w g y n) =
 norm w (if Z.eqb (eval_expr s g) 0 then eval_expr s n else eval_expr s y).
Proof. reflexivity. Qed.

Lemma eval_zero_guard : forall s rs,
 eval_expr s (EBinary 1 BEq (EConst 5 0) (EVar 5 rs)) = norm 1 (boolz (Z.eqb 0 (norm 5 (read_signal s rs)))).
Proof. intros. cbn [eval_expr]. change (norm 5 0) with 0. reflexivity. Qed.

(** ---- read ports under the combinational LFP ---- *)
Theorem bank_port_value : forall p ps index proc nba dst bank total idx seed fixed,
 filter is_comb (processes p) = ps -> nth_error ps index = Some proc ->
 process_body proc = SAssign nba (ESel 32 (EVar total bank) idx) (LVar 32 dst) ->
 assignment_bindingb ps index = true -> (0 < statement_fuel p)%nat -> CombLFP p seed fixed ->
 (1024 <= total)%nat -> bounded32b idx = true ->
 norm 32 (read_signal fixed dst) = lane_read 32 (read_signal fixed bank) (eval_expr fixed idx / 32).
Proof.
 intros p ps index proc nba dst bank total idx seed fixed HP HN HB HC HF HL HT HI.
 rewrite (checked_assignment_binding p ps index proc nba _ 32 dst seed fixed HP HN HB HC HF HL).
 rewrite (eval_packed_lane bank total idx HT HI fixed). apply lane_read_norm.
Qed.

(** The same with the x0 mux in front of the lane read: register index 0 reads as 0. *)
Theorem bank_port_value_x0 : forall p ps index proc nba dst bank total idx rs seed fixed,
 filter is_comb (processes p) = ps -> nth_error ps index = Some proc ->
 process_body proc = SAssign nba
   (ECond 32 (EBinary 1 BEq (EConst 5 0) (EVar 5 rs)) (EConst 32 0) (ESel 32 (EVar total bank) idx)) (LVar 32 dst) ->
 assignment_bindingb ps index = true -> (0 < statement_fuel p)%nat -> CombLFP p seed fixed ->
 (1024 <= total)%nat -> bounded32b idx = true ->
 norm 32 (read_signal fixed dst) =
 if Z.eqb (norm 5 (read_signal fixed rs)) 0 then 0
 else lane_read 32 (read_signal fixed bank) (eval_expr fixed idx / 32).
Proof.
 intros p ps index proc nba dst bank total idx rs seed fixed HP HN HB HC HF HL HT HI.
 rewrite (checked_assignment_binding p ps index proc nba _ 32 dst seed fixed HP HN HB HC HF HL).
 rewrite (eval_cond_unfold fixed). rewrite (eval_packed_lane bank total idx HT HI fixed).
 rewrite (eval_zero_guard fixed rs).
 destruct (Z.eqb (norm 5 (read_signal fixed rs)) 0) eqn:E.
 - apply Z.eqb_eq in E. rewrite E. cbn. reflexivity.
 - apply Z.eqb_neq in E.
   assert (Hz : Z.eqb 0 (norm 5 (read_signal fixed rs)) = false) by (apply Z.eqb_neq; lia).
   rewrite Hz. cbn. rewrite lane_read_norm. apply lane_read_norm.
Qed.

(** ---- the relation bank lanes = abstract registers, lane 0 = 0 ---- *)
Definition RFRel (packed : Z) (view : Z -> Z) : Prop :=
 (forall i, 0 <= i < 32 -> lane_read 32 packed i = view i) /\ view 0 = 0.

(** Operand clause (plain port): the port value is the abstract register at the lane the index expression selects. *)
Theorem operand_clause : forall p ps index proc nba dst bank total idx seed fixed view,
 filter is_comb (processes p) = ps -> nth_error ps index = Some proc ->
 process_body proc = SAssign nba (ESel 32 (EVar total bank) idx) (LVar 32 dst) ->
 assignment_bindingb ps index = true -> (0 < statement_fuel p)%nat -> CombLFP p seed fixed ->
 (1024 <= total)%nat -> bounded32b idx = true -> RFRel (read_signal fixed bank) view ->
 norm 32 (read_signal fixed dst) = view (eval_expr fixed idx / 32).
Proof.
 intros p ps index proc nba dst bank total idx seed fixed view HP HN HB HC HF HL HT HI [HR _].
 rewrite (bank_port_value p ps index proc nba dst bank total idx seed fixed HP HN HB HC HF HL HT HI).
 apply HR. exact (proj1 (bounded32b_sound idx HI fixed)).
Qed.

(** Operand clause with the x0 mux: the port value is the abstract register at the index register, with x0 = 0. *)
Theorem operand_clause_x0 : forall p ps index proc nba dst bank total idx rs seed fixed view,
 filter is_comb (processes p) = ps -> nth_error ps index = Some proc ->
 process_body proc = SAssign nba
   (ECond 32 (EBinary 1 BEq (EConst 5 0) (EVar 5 rs)) (EConst 32 0) (ESel 32 (EVar total bank) idx)) (LVar 32 dst) ->
 assignment_bindingb ps index = true -> (0 < statement_fuel p)%nat -> CombLFP p seed fixed ->
 (1024 <= total)%nat -> bounded32b idx = true ->
 eval_expr fixed idx / 32 = norm 5 (read_signal fixed rs) ->
 RFRel (read_signal fixed bank) view ->
 norm 32 (read_signal fixed dst) = view (norm 5 (read_signal fixed rs)).
Proof.
 intros p ps index proc nba dst bank total idx rs seed fixed view HP HN HB HC HF HL HT HI Hidx [HR H0].
 rewrite (bank_port_value_x0 p ps index proc nba dst bank total idx rs seed fixed HP HN HB HC HF HL HT HI).
 destruct (Z.eqb (norm 5 (read_signal fixed rs)) 0) eqn:E.
 - apply Z.eqb_eq in E. rewrite E. symmetry. exact H0.
 - rewrite Hidx. apply HR. pose proof (norm_bounds 5 (read_signal fixed rs)) as HB5.
   change (0 <= norm 5 (read_signal fixed rs) < 32) in HB5. exact HB5.
Qed.

(** ---- preservation of RFRel ---- *)
Theorem RFRel_lane_write : forall packed packed' view j x,
 RFRel packed view -> 0 <= j < 32 -> (j = 0 -> x = 0) ->
 (forall i, 0 <= i -> lane_read 32 packed' i = if Z.eqb i j then x else lane_read 32 packed i) ->
 RFRel packed' (fun i => if Z.eqb i j then x else view i).
Proof.
 intros packed packed' view j x [HR H0] Hj Hx Hl. split.
 - intros i Hi. rewrite Hl by lia. destruct (Z.eqb i j); [reflexivity|]. apply HR; lia.
 - destruct (Z.eqb 0 j) eqn:E.
   + apply Z.eqb_eq in E. apply Hx. lia.
   + exact H0.
Qed.

(** A write whose value is forced to 0 at lane 0 (the design's own mux/guard) keeps lane 0 = 0. *)
Theorem RFRel_lane_write_guarded : forall packed packed' view j v,
 RFRel packed view -> 0 <= j < 32 -> (j = 0 -> norm 32 v = 0) ->
 (forall i, 0 <= i -> lane_read 32 packed' i = if Z.eqb i j then norm 32 v else lane_read 32 packed i) ->
 RFRel packed' (fun i => if Z.eqb i j then norm 32 v else view i).
Proof. intros. eapply RFRel_lane_write; eassumption. Qed.

Theorem RFRel_reset : forall packed',
 (forall i, 0 <= i < 32 -> lane_read 32 packed' i = 0) -> RFRel packed' (fun _ => 0).
Proof. intros packed' H. split; [exact H|reflexivity]. Qed.

Theorem RFRel_frame : forall packed packed' view, RFRel packed view -> packed' = packed -> RFRel packed' view.
Proof. intros; subst; assumption. Qed.

Lemma lane_read_zero_bank : forall w i, lane_read w 0 i = 0.
Proof.
 intros. unfold lane_read, read_slice. rewrite Z.shiftr_0_l. apply Z.land_0_l.
Qed.

(** ---- x0 handling derived from the design's own expressions (not assumed) ---- *)
Lemma idx0_test_true : forall s rs, norm 5 (read_signal s rs) = 0 ->
 eval_expr s (EBinary 1 BEq (EConst 5 0) (EVar 5 rs)) = 1.
Proof. intros s rs H. cbn [eval_expr]. change (norm 5 0) with 0. rewrite H. reflexivity. Qed.

Lemma idx0_test_false : forall s rs, norm 5 (read_signal s rs) <> 0 ->
 eval_expr s (EBinary 1 BNeq (EConst 5 0) (EVar 5 rs)) = 1.
Proof.
 intros s rs H. cbn [eval_expr]. change (norm 5 0) with 0.
 destruct (Z.eqb 0 (norm 5 (read_signal s rs))) eqn:E; [apply Z.eqb_eq in E; lia|reflexivity].
Qed.

Lemma bit_cases : forall s e, expr_width e = 1%nat -> eval_expr s e = 0 \/ eval_expr s e = 1.
Proof. intros s e H. pose proof (eval_bounds s e) as [H1 H2]. rewrite H in H2. change (2 ^ Z.of_nat 1) with 2 in H2. lia. Qed.

Lemma or_nonzero_r : forall s a b, expr_width a = 1%nat -> expr_width b = 1%nat ->
 eval_expr s b <> 0 -> eval_expr s (EBinary 1 BOr a b) <> 0.
Proof.
 intros s a b Ha Hb H. destruct (bit_cases s a Ha) as [E|E]; destruct (bit_cases s b Hb) as [F|F];
  try lia; cbn [eval_expr] in *; rewrite ?E, ?F; vm_compute; discriminate.
Qed.

Lemma or_nonzero_l : forall s a b, expr_width a = 1%nat -> expr_width b = 1%nat ->
 eval_expr s a <> 0 -> eval_expr s (EBinary 1 BOr a b) <> 0.
Proof.
 intros s a b Ha Hb H. destruct (bit_cases s a Ha) as [E|E]; destruct (bit_cases s b Hb) as [F|F];
  try lia; cbn [eval_expr] in *; rewrite ?E, ?F; vm_compute; discriminate.
Qed.

Lemma cond_true_value : forall s g y n w, eval_expr s g <> 0 ->
 eval_expr s (ECond w g y n) = norm w (eval_expr s y).
Proof. intros s g y n w H. rewrite eval_cond_unfold. destruct (Z.eqb (eval_expr s g) 0) eqn:E; [apply Z.eqb_eq in E; lia|reflexivity]. Qed.

(** A write enabled by [a && (0 != rd)] has rd <> 0. *)
Lemma and_neq0_nonzero : forall s a rd, expr_width a = 1%nat ->
 eval_expr s (EBinary 1 BAnd a (EBinary 1 BNeq (EConst 5 0) (EVar 5 rd))) <> 0 -> norm 5 (read_signal s rd) <> 0.
Proof.
 intros s a rd Ha H E. cbn [eval_expr] in H. change (norm 5 0) with 0 in H. rewrite E in H. cbn in H.
 destruct (bit_cases s a Ha) as [F|F]; cbn [eval_expr] in F; rewrite F in H; apply H; vm_compute; reflexivity.
Qed.

Lemma RFRel_zero : RFRel 0 (fun _ => 0).
Proof. split; [intros i _; apply lane_read_zero_bank|reflexivity]. Qed.
End ExtendedSVBankOperand.
Print Assumptions ExtendedSVBankOperand.operand_clause.
Print Assumptions ExtendedSVBankOperand.operand_clause_x0.
Print Assumptions ExtendedSVBankOperand.RFRel_lane_write.
