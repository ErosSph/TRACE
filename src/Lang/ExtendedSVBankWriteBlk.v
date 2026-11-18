(** Design-independent: bank slice write inside a one-statement NBA block under reset and guard conditionals:
    [if c then (if g then { bank[idx] <= e; } else skip) else other] (the block form `begin .. end` that front ends produce for a
    single assignment).  Same conclusion as ExtendedSVBankWriteStep.bank_phase_lane_guarded / _guard_off, which cover the unwrapped form.
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import List ZArith Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice
 Lang.ExtendedSVAssignment Lang.ExtendedSVEmptyPipeline Lang.ExtendedSVWordInvariant Lang.ExtendedSVSeqStep
 Lang.ExtendedSVBitSlice Lang.ExtendedSVRegisterBank Lang.ExtendedSVBankAlignment Lang.ExtendedSVBankIndex Lang.ExtendedSVBankWriteStep.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVProcessSlice ExtendedSVAssignment
 ExtendedSVWordInvariant ExtendedSVSeqStep ExtendedSVBitSlice ExtendedSVRegisterBank ExtendedSVBankAlignment
 ExtendedSVBankIndex ExtendedSVBankWriteStep.
Local Open Scope Z_scope.
Module ExtendedSVBankWriteBlk.

Lemma process_updates_guard_write_blk : forall p s proc c g e lhs other,
 process_body proc = SSeq [SSeq [SIf c (SIf g (SSeq [SAssign true e lhs]) SSkip) other]] ->
 (7 <= statement_fuel p)%nat ->
 eval_expr s c <> 0 -> eval_expr s g <> 0 ->
 process_updates p s proc = [resolve_update s lhs (eval_expr s e)].
Proof.
 intros p s proc c g e lhs other HB HF Hc Hg. unfold process_updates. rewrite HB.
 destruct (statement_fuel p) as [|[|[|[|[|[|[|f]]]]]]]; try lia.
 rewrite exec_seq. cbn [fold_left]. rewrite exec_seq. cbn [fold_left].
 rewrite exec_if_nba. cbn [blocking_state]. destruct (Z.eqb (eval_expr s c) 0) eqn:E1; [apply Z.eqb_eq in E1; lia|].
 rewrite exec_if_nba. cbn [blocking_state]. destruct (Z.eqb (eval_expr s g) 0) eqn:E2; [apply Z.eqb_eq in E2; lia|].
 rewrite exec_seq. cbn [fold_left]. rewrite exec_assign_nba. cbn [blocking_state emitted_updates]. reflexivity.
Qed.

Lemma process_updates_guard_off_blk : forall p s proc c g y other,
 process_body proc = SSeq [SSeq [SIf c (SIf g y SSkip) other]] ->
 (5 <= statement_fuel p)%nat ->
 eval_expr s c <> 0 -> eval_expr s g = 0 ->
 process_updates p s proc = [].
Proof. intros. eapply process_updates_guard_off; eauto. Qed.

Theorem bank_phase_lane_guarded_blk : forall p ev pre r P c g e w W idx other j i,
 comb_root_unwrittenb p r = true -> changed_signal ev <> r ->
 process_body P = SSeq [SSeq [SIf c (SIf g (SSeq [SAssign true e (LSel w (LVar W r) idx)]) SSkip) other]] ->
 (7 <= statement_fuel p)%nat ->
 filter (process_matches_states pre (phase_driven_state p ev pre)) (filter (writes_rootb r) (processes p)) = [P] ->
 eval_expr (phase_driven_state p ev pre) c <> 0 -> eval_expr (phase_driven_state p ev pre) g <> 0 ->
 eval_expr (phase_driven_state p ev pre) idx = Z.of_nat w * j -> 0 <= j -> 0 <= i ->
 lane_read w (read_signal (PhaseSemantics p ev pre) r) i =
 if Z.eqb i j then norm w (eval_expr (phase_driven_state p ev pre) e) else lane_read w (read_signal pre r) i.
Proof.
 intros p ev pre r P c g e w W idx other j i HU HE HB HF HW Hc Hg Hidx Hj Hi.
 rewrite (bank_phase_step p ev pre r P [] (resolve_update (phase_driven_state p ev pre) (LSel w (LVar W r) idx) (eval_expr (phase_driven_state p ev pre) e)) [] HU HE HW).
 - apply bank_lane_write; assumption.
 - rewrite (process_updates_guard_write_blk p _ P c g e _ other HB HF Hc Hg). reflexivity.
 - intros u [].
 - intros u [].
Qed.
End ExtendedSVBankWriteBlk.
Print Assumptions ExtendedSVBankWriteBlk.bank_phase_lane_guarded_blk.
