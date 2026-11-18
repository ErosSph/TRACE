(** Design-independent: lane-level effect of a clock phase on a packed register-bank root.
    A selected sequential process writes the bank by one non-blocking slice assignment
    [LSel w (LVar W bank) idx := e] (alone in an NBA block, or under conditionals); lane [i] of the bank
    afterwards equals the written value if [i] is the written lane and keeps its old value otherwise.
    Mirrors ExtendedSV [assign_lvalue] / [resolve_update] / [apply_update] / [write_slice] exactly.
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import List ZArith Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice
 Lang.ExtendedSVAssignment Lang.ExtendedSVEmptyPipeline Lang.ExtendedSVWordInvariant Lang.ExtendedSVSeqStep
 Lang.ExtendedSVBitSlice Lang.ExtendedSVRegisterBank Lang.ExtendedSVBankAlignment Lang.ExtendedSVBankIndex.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVProcessSlice ExtendedSVAssignment
 ExtendedSVWordInvariant ExtendedSVSeqStep ExtendedSVBitSlice ExtendedSVRegisterBank ExtendedSVBankAlignment
 ExtendedSVBankIndex.
Local Open Scope Z_scope.
Module ExtendedSVBankWriteStep.

(** ---- phase level: the bank after the phase is the old bank with the one update of the selected process ---- *)
Theorem bank_phase_step : forall p ev pre r P l1 u l2,
 comb_root_unwrittenb p r = true -> changed_signal ev <> r ->
 filter (process_matches_states pre (phase_driven_state p ev pre)) (filter (writes_rootb r) (processes p)) = [P] ->
 process_updates p (phase_driven_state p ev pre) P = l1 ++ u :: l2 ->
 updates_avoid r l1 -> updates_avoid r l2 ->
 read_signal (PhaseSemantics p ev pre) r = apply_update_root_value r (read_signal pre r) u.
Proof.
 intros p ev pre r P l1 u l2 HU HE HW HP H1 H2.
 rewrite phase_root_projection by assumption.
 unfold phase_update_chain, selected_on_transition.
 rewrite process_slice_sound.
 rewrite filter_swap, HW. cbn [flat_map]. rewrite app_nil_r.
 rewrite HP, apply_root_app.
 rewrite (apply_root_avoids r l1 _ H1).
 cbn [apply_updates_root_value].
 rewrite (apply_root_avoids r l2 _ H2). reflexivity.
Qed.

(** The selected process does not write the bank in this phase (guard off): the bank is unchanged. *)
Theorem bank_phase_frame : forall p ev pre r P,
 comb_root_unwrittenb p r = true -> changed_signal ev <> r ->
 filter (process_matches_states pre (phase_driven_state p ev pre)) (filter (writes_rootb r) (processes p)) = [P] ->
 updates_avoid r (process_updates p (phase_driven_state p ev pre) P) ->
 read_signal (PhaseSemantics p ev pre) r = read_signal pre r.
Proof.
 intros p ev pre r P HU HE HW HP.
 rewrite phase_root_projection by assumption.
 unfold phase_update_chain, selected_on_transition.
 rewrite process_slice_sound.
 rewrite filter_swap, HW. cbn [flat_map]. rewrite app_nil_r.
 apply apply_root_avoids. exact HP.
Qed.

(** ---- process shape A: a block of non-blocking assignments, the bank slice write at position k ---- *)
Theorem bank_nba_step : forall p ev pre r P sts k e lhs,
 comb_root_unwrittenb p r = true -> changed_signal ev <> r ->
 process_body P = SSeq [SSeq sts] -> nba_blockb sts = true -> (3 <= statement_fuel p)%nat ->
 filter (process_matches_states pre (phase_driven_state p ev pre)) (filter (writes_rootb r) (processes p)) = [P] ->
 nth_error sts k = Some (SAssign true e lhs) -> lvalue_root lhs = r ->
 existsb (writes_stmtb r) (firstn k sts) = false ->
 existsb (writes_stmtb r) (skipn (S k) sts) = false ->
 read_signal (PhaseSemantics p ev pre) r =
 apply_update_root_value r (read_signal pre r)
   (resolve_update (phase_driven_state p ev pre) lhs (eval_expr (phase_driven_state p ev pre) e)).
Proof.
 intros p ev pre r P sts k e lhs HU HE HB HN HF HW HK HR HP HQ.
 set (driven := phase_driven_state p ev pre) in *.
 pose proof (nth_error_split sts k HK) as [l1 [l2 [Hsplit Hlen]]].
 assert (Hl1 : firstn k sts = l1).
 { rewrite Hsplit, firstn_app. rewrite firstn_all2 by lia. replace (k - length l1)%nat with 0%nat by lia. cbn. now rewrite app_nil_r. }
 assert (Hl2 : skipn (S k) sts = l2).
 { rewrite Hsplit, skipn_app. rewrite skipn_all2 by lia. replace (S k - length l1)%nat with 1%nat by lia. reflexivity. }
 rewrite Hl1 in HP. rewrite Hl2 in HQ.
 refine (bank_phase_step p ev pre r P (nba_updates driven l1) (resolve_update driven lhs (eval_expr driven e)) (nba_updates driven l2) HU HE HW _ _ _).
  - fold driven; rewrite (process_updates_nba p driven P sts HB HN HF).
   rewrite Hsplit at 1. rewrite nba_updates_app. cbn [nba_updates]. reflexivity.
 - exact (nba_updates_avoid driven r l1 HP).
 - exact (nba_updates_avoid driven r l2 HQ).
Qed.

(** ---- process shape B: [if c then (if g then bank-slice-write else skip) else other] in an NBA-style block ---- *)
Lemma exec_if_nba : forall f g y n es, exec_stmt (S f) (SIf g y n) es =
 exec_stmt f (if Z.eqb (eval_expr (blocking_state es) g) 0 then n else y) es.
Proof. reflexivity. Qed.

Lemma exec_skip : forall f es, exec_stmt (S f) SSkip es = es.
Proof. reflexivity. Qed.

Lemma process_updates_guard_write : forall p s proc c g e lhs other,
 process_body proc = SSeq [SSeq [SIf c (SIf g (SAssign true e lhs) SSkip) other]] ->
 (5 <= statement_fuel p)%nat ->
 eval_expr s c <> 0 -> eval_expr s g <> 0 ->
 process_updates p s proc = [resolve_update s lhs (eval_expr s e)].
Proof.
 intros p s proc c g e lhs other HB HF Hc Hg. unfold process_updates. rewrite HB.
 destruct (statement_fuel p) as [|[|[|[|[|f]]]]]; try lia.
 rewrite exec_seq. cbn [fold_left]. rewrite exec_seq. cbn [fold_left].
 rewrite exec_if_nba. cbn [blocking_state]. destruct (Z.eqb (eval_expr s c) 0) eqn:E1; [apply Z.eqb_eq in E1; lia|].
 rewrite exec_if_nba. cbn [blocking_state]. destruct (Z.eqb (eval_expr s g) 0) eqn:E2; [apply Z.eqb_eq in E2; lia|].
 rewrite exec_assign_nba. cbn [blocking_state emitted_updates]. reflexivity.
Qed.

Lemma process_updates_guard_off : forall p s proc c g y other,
 process_body proc = SSeq [SSeq [SIf c (SIf g y SSkip) other]] ->
 (5 <= statement_fuel p)%nat ->
 eval_expr s c <> 0 -> eval_expr s g = 0 ->
 process_updates p s proc = [].
Proof.
 intros p s proc c g y other HB HF Hc Hg. unfold process_updates. rewrite HB.
 destruct (statement_fuel p) as [|[|[|[|[|f]]]]]; try lia.
 rewrite exec_seq. cbn [fold_left]. rewrite exec_seq. cbn [fold_left].
 rewrite exec_if_nba. cbn [blocking_state]. destruct (Z.eqb (eval_expr s c) 0) eqn:E1; [apply Z.eqb_eq in E1; lia|].
 rewrite exec_if_nba. cbn [blocking_state]. rewrite Hg. cbn [Z.eqb]. rewrite exec_skip. reflexivity.
Qed.

Lemma process_updates_guard_other : forall p s proc c yes e lhs,
 process_body proc = SSeq [SSeq [SIf c yes (SAssign true e lhs)]] ->
 (4 <= statement_fuel p)%nat ->
 eval_expr s c = 0 ->
 process_updates p s proc = [resolve_update s lhs (eval_expr s e)].
Proof.
 intros p s proc c yes e lhs HB HF Hc. unfold process_updates. rewrite HB.
 destruct (statement_fuel p) as [|[|[|[|f]]]]; try lia.
 rewrite exec_seq. cbn [fold_left]. rewrite exec_seq. cbn [fold_left].
 rewrite exec_if_nba. cbn [blocking_state]. rewrite Hc. cbn [Z.eqb].
 rewrite exec_assign_nba. cbn [blocking_state emitted_updates]. reflexivity.
Qed.

(** ---- lane level ---- *)
(** The slice update has the exact shape of a lane write once the index expression evaluates to [w*j]. *)
Lemma slice_update_is_bank_write : forall s w W r idx v j,
 eval_expr s idx = Z.of_nat w * j ->
 resolve_update s (LSel w (LVar W r) idx) v = bank_write r w j (norm w v).
Proof.
 intros s w W r idx v j H. unfold resolve_update, bank_write. cbn [resolve_lvalue].
 rewrite H. cbn [Z.add]. reflexivity.
Qed.

Theorem bank_lane_write : forall s w W r idx v j old i,
 eval_expr s idx = Z.of_nat w * j -> 0 <= j -> 0 <= i ->
 lane_read w (apply_update_root_value r old (resolve_update s (LSel w (LVar W r) idx) v)) i =
 if Z.eqb i j then norm w v else lane_read w old i.
Proof.
 intros s w W r idx v j old i H Hj Hi. rewrite (slice_update_is_bank_write s w W r idx v j H).
 rewrite bank_write_lane by assumption. rewrite norm_idempotent. reflexivity.
Qed.

(** A whole-bank assignment [bank := value] (e.g. reset) sets every lane inside the bank to the lane of the value. *)
Theorem bank_lane_reset : forall s W r e old i w,
 0 <= i -> (i + 1) * Z.of_nat w <= Z.of_nat W ->
 lane_read w (apply_update_root_value r old (resolve_update s (LVar W r) (eval_expr s e))) i =
 lane_read w (norm W (eval_expr s e)) i.
Proof.
 intros s W r e old i w Hi Hc. unfold resolve_update, apply_update_root_value. cbn [resolve_lvalue update_signal update_offset update_width update_value].
 rewrite Nat.eqb_refl. unfold lane_read. apply read_slice_write_cover_zero; nia.
Qed.

(** Phase-level lane statements. *)
Theorem bank_phase_lane_nba : forall p ev pre r P sts k e w W idx j i,
 comb_root_unwrittenb p r = true -> changed_signal ev <> r ->
 process_body P = SSeq [SSeq sts] -> nba_blockb sts = true -> (3 <= statement_fuel p)%nat ->
 filter (process_matches_states pre (phase_driven_state p ev pre)) (filter (writes_rootb r) (processes p)) = [P] ->
 nth_error sts k = Some (SAssign true e (LSel w (LVar W r) idx)) ->
 existsb (writes_stmtb r) (firstn k sts) = false ->
 existsb (writes_stmtb r) (skipn (S k) sts) = false ->
 eval_expr (phase_driven_state p ev pre) idx = Z.of_nat w * j -> 0 <= j -> 0 <= i ->
 lane_read w (read_signal (PhaseSemantics p ev pre) r) i =
 if Z.eqb i j then norm w (eval_expr (phase_driven_state p ev pre) e) else lane_read w (read_signal pre r) i.
Proof.
 intros p ev pre r P sts k e w W idx j i HU HE HB HN HF HW HK H1 H2 Hidx Hj Hi.
 rewrite (bank_nba_step p ev pre r P sts k e _ HU HE HB HN HF HW HK eq_refl H1 H2).
 apply bank_lane_write; assumption.
Qed.

Theorem bank_phase_lane_guarded : forall p ev pre r P c g e w W idx other j i,
 comb_root_unwrittenb p r = true -> changed_signal ev <> r ->
 process_body P = SSeq [SSeq [SIf c (SIf g (SAssign true e (LSel w (LVar W r) idx)) SSkip) other]] ->
 (5 <= statement_fuel p)%nat ->
 filter (process_matches_states pre (phase_driven_state p ev pre)) (filter (writes_rootb r) (processes p)) = [P] ->
 eval_expr (phase_driven_state p ev pre) c <> 0 -> eval_expr (phase_driven_state p ev pre) g <> 0 ->
 eval_expr (phase_driven_state p ev pre) idx = Z.of_nat w * j -> 0 <= j -> 0 <= i ->
 lane_read w (read_signal (PhaseSemantics p ev pre) r) i =
 if Z.eqb i j then norm w (eval_expr (phase_driven_state p ev pre) e) else lane_read w (read_signal pre r) i.
Proof.
 intros p ev pre r P c g e w W idx other j i HU HE HB HF HW Hc Hg Hidx Hj Hi.
 rewrite (bank_phase_step p ev pre r P [] (resolve_update (phase_driven_state p ev pre) (LSel w (LVar W r) idx) (eval_expr (phase_driven_state p ev pre) e)) [] HU HE HW).
 - apply bank_lane_write; assumption.
 - rewrite (process_updates_guard_write p _ P c g e _ other HB HF Hc Hg). reflexivity.
 - intros u [].
 - intros u [].
Qed.

Theorem bank_phase_lane_guard_off : forall p ev pre r P c g y other,
 comb_root_unwrittenb p r = true -> changed_signal ev <> r ->
 process_body P = SSeq [SSeq [SIf c (SIf g y SSkip) other]] ->
 (5 <= statement_fuel p)%nat ->
 filter (process_matches_states pre (phase_driven_state p ev pre)) (filter (writes_rootb r) (processes p)) = [P] ->
 eval_expr (phase_driven_state p ev pre) c <> 0 -> eval_expr (phase_driven_state p ev pre) g = 0 ->
 read_signal (PhaseSemantics p ev pre) r = read_signal pre r.
Proof.
 intros p ev pre r P c g y other HU HE HB HF HW Hc Hg.
 apply (bank_phase_frame p ev pre r P HU HE HW).
 rewrite (process_updates_guard_off p _ P c g y other HB HF Hc Hg). intros u [].
Qed.

Theorem bank_phase_lane_other : forall p ev pre r P c yes e W i w,
 comb_root_unwrittenb p r = true -> changed_signal ev <> r ->
 process_body P = SSeq [SSeq [SIf c yes (SAssign true e (LVar W r))]] ->
 (4 <= statement_fuel p)%nat ->
 filter (process_matches_states pre (phase_driven_state p ev pre)) (filter (writes_rootb r) (processes p)) = [P] ->
 eval_expr (phase_driven_state p ev pre) c = 0 -> 0 <= i -> (i + 1) * Z.of_nat w <= Z.of_nat W ->
 lane_read w (read_signal (PhaseSemantics p ev pre) r) i =
 lane_read w (norm W (eval_expr (phase_driven_state p ev pre) e)) i.
Proof.
 intros p ev pre r P c yes e W i w HU HE HB HF HW Hc Hi Hcov.
 rewrite (bank_phase_step p ev pre r P [] (resolve_update (phase_driven_state p ev pre) (LVar W r) (eval_expr (phase_driven_state p ev pre) e)) [] HU HE HW).
 - apply bank_lane_reset; assumption.
 - rewrite (process_updates_guard_other p _ P c yes e _ HB HF Hc). reflexivity.
 - intros u [].
 - intros u [].
Qed.

(** ---- index expressions: the exact lane number behind the address encodings used by RTL register files ---- *)
Lemma mul32_exact : forall s width index scale,
 (10 <= width)%nat -> (expr_width index <= 5)%nat -> literal_eqb scale 32 = true ->
 eval_expr s (EBinary width BMul index scale) = Z.of_nat 32 * eval_expr s index.
Proof.
 intros s width index scale HW HI HC. pose proof (small_operand_bound index s HI) as HB.
 cbn [eval_expr]. rewrite (literal_eqb_sound scale 32 HC s).
 rewrite norm_small_offset by lia. change (Z.of_nat 32) with 32. lia.
Qed.

Lemma shifted_exact : forall s root,
 eval_expr s (ESel 10 (EBinary 32 BShiftL (EExtend 32 false (EVar 5 root)) (EConst 32 5)) (EConst 32 0)) =
 Z.of_nat 32 * norm 5 (read_signal s root).
Proof.
 intros s root.
 pose proof (norm_bounds 5 (read_signal s root)) as HB.
 change (0 <= norm 5 (read_signal s root) < 32) in HB.
 cbn [eval_expr].
 change (norm 10 (Z.shiftr (norm 32 (Z.shiftl (norm 32 (norm 5 (read_signal s root))) 5)) 0) = Z.of_nat 32 * norm 5 (read_signal s root)).
 rewrite (norm_small_index 32 (norm 5 (read_signal s root)) ltac:(lia) HB).
 rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_0_r.
 change (norm 10 (norm 32 (norm 5 (read_signal s root) * 2 ^ 5)) = Z.of_nat 32 * norm 5 (read_signal s root)).
 rewrite (norm_small_offset 32 (norm 5 (read_signal s root) * 2 ^ 5) ltac:(lia) ltac:(lia)).
 rewrite norm_small_offset by lia. change (Z.of_nat 32) with 32. change (2^5) with 32. lia.
Qed.
End ExtendedSVBankWriteStep.
Print Assumptions ExtendedSVBankWriteStep.bank_phase_lane_nba.
Print Assumptions ExtendedSVBankWriteStep.bank_phase_lane_guarded.
