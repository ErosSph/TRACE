(** Rebased register bank, write process of the shape "reset arm first": [if cr then {constant lane writes} else if c then {bank[idx] <= e}].
    Additive to ExtendedSVBankRebase / ExtendedSVBankWriteStep (nothing there is changed).  Used by Steel (rvx_core process 8).
      * [rf3_phase_chain]   : the bank after a phase = the old bank with all updates of the selected process applied;
      * [rf3_reset_lanes]   : reset arm taken, the updates are [bank_write r 32 j 0] for j in [js]: those lanes are 0;
      * [rf3_lane_write]    : reset arm off, guard on: lane [i] = written value if [i = j], old otherwise;
      * [rf3_frame]         : reset arm off, guard off: bank unchanged;
      * [rebase_eval_zero]  : rs = 0 addresses the pad lane 31;  [RFRelR_pad_write] : a write to the pad lane keeps [RFRelR].
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. Nothing is assumed. *)
From Coq Require Import List ZArith Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice
 Lang.ExtendedSVAssignment Lang.ExtendedSVEmptyPipeline Lang.ExtendedSVWordInvariant Lang.ExtendedSVSeqStep
 Lang.ExtendedSVBitSlice Lang.ExtendedSVRegisterBank Lang.ExtendedSVBankAlignment Lang.ExtendedSVBankIndex
 Lang.ExtendedSVCheckedAssignmentBinding Lang.ExtendedSVBankWriteStep Lang.ExtendedSVBankOperand Lang.ExtendedSVBankRebase.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVProcessSlice ExtendedSVAssignment
 ExtendedSVWordInvariant ExtendedSVSeqStep ExtendedSVBitSlice ExtendedSVRegisterBank ExtendedSVBankAlignment
 ExtendedSVBankIndex ExtendedSVCheckedAssignmentBinding ExtendedSVBankWriteStep ExtendedSVBankOperand ExtendedSVBankRebase.
Local Open Scope Z_scope.
Module ExtendedSVBankRebaseRst.

Theorem rf3_phase_chain : forall p ev pre r P,
 comb_root_unwrittenb p r = true -> changed_signal ev <> r ->
 filter (process_matches_states pre (phase_driven_state p ev pre)) (filter (writes_rootb r) (processes p)) = [P] ->
 read_signal (PhaseSemantics p ev pre) r =
 apply_updates_root_value r (read_signal pre r) (process_updates p (phase_driven_state p ev pre) P).
Proof.
 intros p ev pre r P HU HE HW.
 rewrite phase_root_projection by assumption.
 unfold phase_update_chain, selected_on_transition.
 rewrite process_slice_sound.
 rewrite filter_swap, HW. cbn [flat_map]. rewrite app_nil_r. reflexivity.
Qed.

Lemma process_updates_rst_arm : forall p s proc cr sts1 other,
 process_body proc = SSeq [SSeq [SIf cr (SSeq sts1) other]] ->
 (5 <= statement_fuel p)%nat -> nba_blockb sts1 = true -> eval_expr s cr <> 0 ->
 process_updates p s proc = nba_updates s sts1.
Proof.
 intros p s proc cr sts1 other HB HF Hb Hc. unfold process_updates. rewrite HB.
 destruct (statement_fuel p) as [|[|[|[|[|f]]]]]; try lia.
 rewrite exec_seq. cbn [fold_left]. rewrite exec_seq. cbn [fold_left].
 rewrite exec_if_nba. cbn [blocking_state]. destruct (Z.eqb (eval_expr s cr) 0) eqn:E1; [apply Z.eqb_eq in E1; lia|].
 rewrite exec_seq. rewrite (exec_nba_fold sts1 (S f) s [] [] ltac:(lia) Hb). cbn [emitted_updates]. reflexivity.
Qed.

Lemma process_updates_rst_write : forall p s proc cr yes c e lhs,
 process_body proc = SSeq [SSeq [SIf cr yes (SIf c (SAssign true e lhs) SSkip)]] ->
 (5 <= statement_fuel p)%nat -> eval_expr s cr = 0 -> eval_expr s c <> 0 ->
 process_updates p s proc = [resolve_update s lhs (eval_expr s e)].
Proof.
 intros p s proc cr yes c e lhs HB HF Hr Hc. unfold process_updates. rewrite HB.
 destruct (statement_fuel p) as [|[|[|[|[|f]]]]]; try lia.
 rewrite exec_seq. cbn [fold_left]. rewrite exec_seq. cbn [fold_left].
 rewrite exec_if_nba. cbn [blocking_state]. rewrite Hr. cbn [Z.eqb].
 rewrite exec_if_nba. cbn [blocking_state]. destruct (Z.eqb (eval_expr s c) 0) eqn:E2; [apply Z.eqb_eq in E2; lia|].
 rewrite exec_assign_nba. cbn [blocking_state emitted_updates]. reflexivity.
Qed.

Lemma process_updates_rst_off : forall p s proc cr yes c y,
 process_body proc = SSeq [SSeq [SIf cr yes (SIf c y SSkip)]] ->
 (5 <= statement_fuel p)%nat -> eval_expr s cr = 0 -> eval_expr s c = 0 ->
 process_updates p s proc = [].
Proof.
 intros p s proc cr yes c y HB HF Hr Hc. unfold process_updates. rewrite HB.
 destruct (statement_fuel p) as [|[|[|[|[|f]]]]]; try lia.
 rewrite exec_seq. cbn [fold_left]. rewrite exec_seq. cbn [fold_left].
 rewrite exec_if_nba. cbn [blocking_state]. rewrite Hr. cbn [Z.eqb].
 rewrite exec_if_nba. cbn [blocking_state]. rewrite Hc. cbn [Z.eqb]. rewrite exec_skip. reflexivity.
Qed.

Lemma norm0 w : norm w 0 = 0.
Proof. rewrite norm_mod. apply Z.mod_0_l. apply Z.pow_nonzero; lia. Qed.

Lemma chain_zero_lanes : forall r w js cur i, 0 <= i -> Forall (fun j => 0 <= j) js ->
 lane_read w (apply_updates_root_value r cur (map (fun j => bank_write r w j 0) js)) i =
 if existsb (Z.eqb i) js then 0 else lane_read w cur i.
Proof.
 intros r w js. induction js as [|j rest IH]; intros cur i Hi HF.
 - reflexivity.
 - inversion HF as [|? ? Hj HF']; subst. cbn [map apply_updates_root_value existsb].
   rewrite IH by assumption. rewrite bank_write_lane by assumption.
   destruct (Z.eqb i j) eqn:E; cbn [orb]; destruct (existsb (Z.eqb i) rest); rewrite ?norm0; reflexivity.
Qed.

Theorem rf3_reset_lanes : forall p ev pre r P cr sts1 other w js,
 comb_root_unwrittenb p r = true -> changed_signal ev <> r ->
 process_body P = SSeq [SSeq [SIf cr (SSeq sts1) other]] -> (5 <= statement_fuel p)%nat -> nba_blockb sts1 = true ->
 filter (process_matches_states pre (phase_driven_state p ev pre)) (filter (writes_rootb r) (processes p)) = [P] ->
 eval_expr (phase_driven_state p ev pre) cr <> 0 ->
 nba_updates (phase_driven_state p ev pre) sts1 = map (fun j => bank_write r w j 0) js -> Forall (fun j => 0 <= j) js ->
 forall i, 0 <= i -> In i js -> lane_read w (read_signal (PhaseSemantics p ev pre) r) i = 0.
Proof.
 intros p ev pre r P cr sts1 other w js HU HE HB HF Hb HW Hc Hn Hj i Hi Hin.
 rewrite (rf3_phase_chain p ev pre r P HU HE HW).
 rewrite (process_updates_rst_arm p _ P cr sts1 other HB HF Hb Hc), Hn.
 rewrite chain_zero_lanes by assumption.
 assert (Hex : existsb (Z.eqb i) js = true) by (apply existsb_exists; exists i; split; [exact Hin|apply Z.eqb_refl]).
 rewrite Hex. reflexivity.
Qed.

Theorem rf3_lane_write : forall p ev pre r P cr yes c e w W idx j i,
 comb_root_unwrittenb p r = true -> changed_signal ev <> r ->
 process_body P = SSeq [SSeq [SIf cr yes (SIf c (SAssign true e (LSel w (LVar W r) idx)) SSkip)]] -> (5 <= statement_fuel p)%nat ->
 filter (process_matches_states pre (phase_driven_state p ev pre)) (filter (writes_rootb r) (processes p)) = [P] ->
 eval_expr (phase_driven_state p ev pre) cr = 0 -> eval_expr (phase_driven_state p ev pre) c <> 0 ->
 eval_expr (phase_driven_state p ev pre) idx = Z.of_nat w * j -> 0 <= j -> 0 <= i ->
 lane_read w (read_signal (PhaseSemantics p ev pre) r) i =
 if Z.eqb i j then norm w (eval_expr (phase_driven_state p ev pre) e) else lane_read w (read_signal pre r) i.
Proof.
 intros p ev pre r P cr yes c e w W idx j i HU HE HB HF HW Hr Hc Hidx Hj Hi.
 rewrite (rf3_phase_chain p ev pre r P HU HE HW).
 rewrite (process_updates_rst_write p _ P cr yes c e _ HB HF Hr Hc).
 cbn [apply_updates_root_value]. apply bank_lane_write; assumption.
Qed.

Theorem rf3_frame : forall p ev pre r P cr yes c y,
 comb_root_unwrittenb p r = true -> changed_signal ev <> r ->
 process_body P = SSeq [SSeq [SIf cr yes (SIf c y SSkip)]] -> (5 <= statement_fuel p)%nat ->
 filter (process_matches_states pre (phase_driven_state p ev pre)) (filter (writes_rootb r) (processes p)) = [P] ->
 eval_expr (phase_driven_state p ev pre) cr = 0 -> eval_expr (phase_driven_state p ev pre) c = 0 ->
 read_signal (PhaseSemantics p ev pre) r = read_signal pre r.
Proof.
 intros p ev pre r P cr yes c y HU HE HB HF HW Hr Hc.
 rewrite (rf3_phase_chain p ev pre r P HU HE HW).
 rewrite (process_updates_rst_off p _ P cr yes c y HB HF Hr Hc). reflexivity.
Qed.

(** A process [if c then y] (no else) whose guard is off emits no update: the written root is unchanged (RAM hold). *)
Lemma process_updates_if_off : forall p s proc c y,
 process_body proc = SSeq [SSeq [SIf c y SSkip]] -> (4 <= statement_fuel p)%nat -> eval_expr s c = 0 ->
 process_updates p s proc = [].
Proof.
 intros p s proc c y HB HF Hc. unfold process_updates. rewrite HB.
 destruct (statement_fuel p) as [|[|[|[|f]]]]; try lia.
 rewrite exec_seq. cbn [fold_left]. rewrite exec_seq. cbn [fold_left].
 rewrite exec_if_nba. cbn [blocking_state]. rewrite Hc. cbn [Z.eqb]. rewrite exec_skip. reflexivity.
Qed.

Theorem if_off_frame : forall p ev pre r P c y,
 comb_root_unwrittenb p r = true -> changed_signal ev <> r ->
 process_body P = SSeq [SSeq [SIf c y SSkip]] -> (4 <= statement_fuel p)%nat ->
 filter (process_matches_states pre (phase_driven_state p ev pre)) (filter (writes_rootb r) (processes p)) = [P] ->
 eval_expr (phase_driven_state p ev pre) c = 0 ->
 read_signal (PhaseSemantics p ev pre) r = read_signal pre r.
Proof.
 intros p ev pre r P c y HU HE HB HF HW Hc.
 rewrite (rf3_phase_chain p ev pre r P HU HE HW).
 rewrite (process_updates_if_off p _ P c y HB HF Hc). reflexivity.
Qed.

Lemma rebase_eval_zero s rs : norm 5 (read_signal s rs) = 0 ->
 eval_expr s (rebased_index rs) = 32 * 31.
Proof.
 intro Hz. unfold rebased_index. cbn [eval_expr].
 change (norm 5 1) with 1. change (norm 12 32) with 32. rewrite Hz.
 change (norm 5 (0 - 1)) with 31. change (norm 12 (31 * 32)) with 992. reflexivity.
Qed.

Theorem RFRelR_pad_write : forall packed packed' view,
 RFRelR packed view ->
 (forall i, 0 <= i -> lane_read 32 packed' i = if Z.eqb i 31 then lane_read 32 packed' 31 else lane_read 32 packed i) ->
 RFRelR packed' view.
Proof.
 intros packed packed' view [HR H0] Hl. split; [|exact H0].
 intros j Hj. rewrite Hl by lia. assert (Hne : (j =? 31) = false) by (apply Z.eqb_neq; lia). rewrite Hne. apply HR; lia.
Qed.
End ExtendedSVBankRebaseRst.
Print Assumptions ExtendedSVBankRebaseRst.rf3_reset_lanes.
Print Assumptions ExtendedSVBankRebaseRst.rf3_lane_write.
Print Assumptions ExtendedSVBankRebaseRst.rf3_frame.
Print Assumptions ExtendedSVBankRebaseRst.if_off_frame.
Print Assumptions ExtendedSVBankRebaseRst.rebase_eval_zero.
Print Assumptions ExtendedSVBankRebaseRst.RFRelR_pad_write.
