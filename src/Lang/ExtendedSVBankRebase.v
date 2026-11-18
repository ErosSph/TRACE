(** Rebased register banks: lane j holds architectural register x(j+1) (address index [(addr - 1) * 32], 5-bit wrap), lane 31 is a
    padding lane that is never read live (the read port muxes address 0 to 0) and never written (the write guard excludes rd = 0).
    Design independent, additive to ExtendedSVBankOperand / ExtendedSVBankWriteStep.  Covers
      * [RFRelR packed view]            : lanes 0..30 = view 1..31, view 0 = 0 (the pad lane 31 is unconstrained);
      * [operand_clause_rebased]        : zero-muxed read port  ECond (0 == rs) 0 (bank[(rs-1)*32 +: 32])  =  view (norm 5 rs);
      * [rf2_lane_write] / [rf2_frame]  : bank phase effect for the write process shape
            SSeq [SSeq [SIf c (SSeq [bank[(rd-1)*32 +: 32] <= e]) SSkip ; SIf c2 (SSeq other-NBAs) SSkip]]
        (the second if carries the registered read addresses of a synchronous read port);
      * [RFRelR_write], [RFRelR_frame], [RFRelR_reset].
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. Nothing is assumed. *)
From Coq Require Import List ZArith Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice
 Lang.ExtendedSVAssignment Lang.ExtendedSVEmptyPipeline Lang.ExtendedSVWordInvariant Lang.ExtendedSVSeqStep
 Lang.ExtendedSVBitSlice Lang.ExtendedSVRegisterBank Lang.ExtendedSVBankAlignment Lang.ExtendedSVBankIndex
 Lang.ExtendedSVCheckedAssignmentBinding Lang.ExtendedSVBankWriteStep Lang.ExtendedSVBankOperand.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVProcessSlice ExtendedSVAssignment
 ExtendedSVWordInvariant ExtendedSVSeqStep ExtendedSVBitSlice ExtendedSVRegisterBank ExtendedSVBankAlignment
 ExtendedSVBankIndex ExtendedSVCheckedAssignmentBinding ExtendedSVBankWriteStep ExtendedSVBankOperand.
Local Open Scope Z_scope.
Module ExtendedSVBankRebase.

Definition RFRelR (packed : Z) (view : Z -> Z) : Prop :=
 (forall j, 0 <= j < 31 -> lane_read 32 packed j = view (j + 1)) /\ view 0 = 0.

Definition rebased_index (rs : signal) : Expr :=
 EBinary 12 BMul (EBinary 5 BSub (EVar 5 rs) (EConst 5 1)) (EConst 12 32).

Lemma rebase_eval s rs : norm 5 (read_signal s rs) <> 0 ->
 eval_expr s (rebased_index rs) = 32 * (norm 5 (read_signal s rs) - 1).
Proof.
 intro Hz. pose proof (norm_bounds 5 (read_signal s rs)) as HB. change (0 <= norm 5 (read_signal s rs) < 32) in HB.
 unfold rebased_index. cbn [eval_expr].
 change (norm 5 1) with 1. change (norm 12 32) with 32.
 rewrite (norm_small_index 5 (norm 5 (read_signal s rs) - 1)) by lia.
 rewrite (norm_small_offset 12 ((norm 5 (read_signal s rs) - 1) * 32)) by lia. lia.
Qed.

Lemma rebased_bounded rs : bounded32b (rebased_index rs) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem operand_clause_rebased : forall p ps index proc nba dst bank total rs seed fixed view,
 filter is_comb (processes p) = ps -> nth_error ps index = Some proc ->
 process_body proc = SAssign nba
   (ECond 32 (EBinary 1 BEq (EConst 5 0) (EVar 5 rs)) (EConst 32 0) (ESel 32 (EVar total bank) (rebased_index rs))) (LVar 32 dst) ->
 assignment_bindingb ps index = true -> (0 < statement_fuel p)%nat -> CombLFP p seed fixed ->
 (1024 <= total)%nat -> RFRelR (read_signal fixed bank) view ->
 norm 32 (read_signal fixed dst) = view (norm 5 (read_signal fixed rs)).
Proof.
 intros p ps index proc nba dst bank total rs seed fixed view HP HN HB HC HF HL HT [HR H0].
 rewrite (bank_port_value_x0 p ps index proc nba dst bank total (rebased_index rs) rs seed fixed HP HN HB HC HF HL HT (rebased_bounded rs)).
 destruct (Z.eqb (norm 5 (read_signal fixed rs)) 0) eqn:E.
 - apply Z.eqb_eq in E. rewrite E. symmetry. exact H0.
 - apply Z.eqb_neq in E. rewrite (rebase_eval fixed rs E).
   pose proof (norm_bounds 5 (read_signal fixed rs)) as HB5. change (0 <= norm 5 (read_signal fixed rs) < 32) in HB5.
   replace (32 * (norm 5 (read_signal fixed rs) - 1) / 32) with (norm 5 (read_signal fixed rs) - 1) by (rewrite Z.mul_comm; rewrite Z.div_mul; lia).
   rewrite HR by lia. f_equal. lia.
Qed.

Theorem RFRelR_write : forall packed packed' view r x,
 RFRelR packed view -> 1 <= r < 32 ->
 (forall i, 0 <= i -> lane_read 32 packed' i = if Z.eqb i (r - 1) then x else lane_read 32 packed i) ->
 RFRelR packed' (fun i => if Z.eqb i r then x else view i).
Proof.
 intros packed packed' view r x [HR H0] Hr Hl. split.
 - intros j Hj. rewrite Hl by lia. destruct (Z.eqb j (r - 1)) eqn:E1.
   + apply Z.eqb_eq in E1. subst j. replace (r - 1 + 1) with r by lia. rewrite Z.eqb_refl. reflexivity.
   + apply Z.eqb_neq in E1. assert (Hne : (j + 1 =? r) = false) by (apply Z.eqb_neq; lia). rewrite Hne. apply HR; lia.
 - assert (Hne : (0 =? r) = false) by (apply Z.eqb_neq; lia). rewrite Hne. exact H0.
Qed.

Theorem RFRelR_frame : forall packed packed' view, RFRelR packed view -> packed' = packed -> RFRelR packed' view.
Proof. intros; subst; assumption. Qed.

Theorem RFRelR_reset : forall packed',
 (forall j, 0 <= j < 31 -> lane_read 32 packed' j = 0) -> RFRelR packed' (fun _ => 0).
Proof. intros packed' H. split; [exact H|reflexivity]. Qed.

(** ---- the write process: [if c then {bank slice write} ; if c2 then {other NBAs}] ---- *)
Lemma exec_if_nba_block : forall f c sts s pn em, (2 <= f)%nat -> nba_blockb sts = true ->
 exec_stmt (S f) (SIf c (SSeq sts) SSkip) {| blocking_state := s; pending_nba := pn; emitted_updates := em |} =
 if Z.eqb (eval_expr s c) 0 then {| blocking_state := s; pending_nba := pn; emitted_updates := em |}
 else {| blocking_state := s; pending_nba := pn ++ nba_updates s sts; emitted_updates := em ++ nba_updates s sts |}.
Proof.
 intros f c sts s pn em Hf Hb. rewrite exec_if_nba. cbn [blocking_state].
 destruct f as [|f]; [lia|]. destruct (Z.eqb (eval_expr s c) 0).
 - apply exec_skip.
 - rewrite exec_seq. apply exec_nba_fold; [lia|exact Hb].
Qed.

Lemma rf2_updates : forall p s proc c c2 sts1 sts2,
 process_body proc = SSeq [SSeq [SIf c (SSeq sts1) SSkip; SIf c2 (SSeq sts2) SSkip]] ->
 (6 <= statement_fuel p)%nat -> nba_blockb sts1 = true -> nba_blockb sts2 = true ->
 process_updates p s proc =
 (if Z.eqb (eval_expr s c) 0 then [] else nba_updates s sts1) ++ (if Z.eqb (eval_expr s c2) 0 then [] else nba_updates s sts2).
Proof.
 intros p s proc c c2 sts1 sts2 HB HF H1 H2. unfold process_updates. rewrite HB.
 destruct (statement_fuel p) as [|[|[|[|[|[|f]]]]]]; try lia.
 rewrite exec_seq. cbn [fold_left]. rewrite exec_seq. cbn [fold_left].
 rewrite (exec_if_nba_block (S (S (S f))) c sts1 s [] [] ltac:(lia) H1).
 destruct (Z.eqb (eval_expr s c) 0) eqn:E1.
 - rewrite (exec_if_nba_block (S (S (S f))) c2 sts2 s [] [] ltac:(lia) H2).
   destruct (Z.eqb (eval_expr s c2) 0); cbn [emitted_updates]; rewrite ?app_nil_l, ?app_nil_r; reflexivity.
 - rewrite (exec_if_nba_block (S (S (S f))) c2 sts2 s _ _ ltac:(lia) H2).
   destruct (Z.eqb (eval_expr s c2) 0); cbn [emitted_updates]; rewrite ?app_nil_l, ?app_nil_r; reflexivity.
Qed.

Theorem rf2_lane_write : forall p ev pre r P c c2 e w W idx sts2 j i,
 comb_root_unwrittenb p r = true -> changed_signal ev <> r ->
 process_body P = SSeq [SSeq [SIf c (SSeq [SAssign true e (LSel w (LVar W r) idx)]) SSkip; SIf c2 (SSeq sts2) SSkip]] ->
 (6 <= statement_fuel p)%nat -> nba_blockb sts2 = true -> existsb (writes_stmtb r) sts2 = false ->
 filter (process_matches_states pre (phase_driven_state p ev pre)) (filter (writes_rootb r) (processes p)) = [P] ->
 eval_expr (phase_driven_state p ev pre) c <> 0 ->
 eval_expr (phase_driven_state p ev pre) idx = Z.of_nat w * j -> 0 <= j -> 0 <= i ->
 lane_read w (read_signal (PhaseSemantics p ev pre) r) i =
 if Z.eqb i j then norm w (eval_expr (phase_driven_state p ev pre) e) else lane_read w (read_signal pre r) i.
Proof.
 intros p ev pre r P c c2 e w W idx sts2 j i HU HE HB HF H2 HW1 HFl Hc Hidx Hj Hi.
 set (d := phase_driven_state p ev pre) in *.
 assert (Hup := rf2_updates p d P c c2 [SAssign true e (LSel w (LVar W r) idx)] sts2 HB HF eq_refl H2).
 destruct (Z.eqb (eval_expr d c) 0) eqn:Ec; [apply Z.eqb_eq in Ec; lia|].
 cbn [nba_updates] in Hup.
 assert (Hav : updates_avoid r (if Z.eqb (eval_expr d c2) 0 then [] else nba_updates d sts2)).
 { destruct (Z.eqb (eval_expr d c2) 0); [intros u []|exact (nba_updates_avoid d r sts2 HW1)]. }
 rewrite (bank_phase_step p ev pre r P [] (resolve_update d (LSel w (LVar W r) idx) (eval_expr d e)) (if Z.eqb (eval_expr d c2) 0 then [] else nba_updates d sts2) HU HE HFl).
 - apply bank_lane_write; assumption.
 - exact Hup.
 - intros u [].
 - exact Hav.
Qed.

Theorem rf2_frame : forall p ev pre r P c c2 lhs e sts2,
 comb_root_unwrittenb p r = true -> changed_signal ev <> r ->
 process_body P = SSeq [SSeq [SIf c (SSeq [SAssign true e lhs]) SSkip; SIf c2 (SSeq sts2) SSkip]] ->
 (6 <= statement_fuel p)%nat -> nba_blockb sts2 = true -> existsb (writes_stmtb r) sts2 = false ->
 filter (process_matches_states pre (phase_driven_state p ev pre)) (filter (writes_rootb r) (processes p)) = [P] ->
 eval_expr (phase_driven_state p ev pre) c = 0 ->
 read_signal (PhaseSemantics p ev pre) r = read_signal pre r.
Proof.
 intros p ev pre r P c c2 lhs e sts2 HU HE HB HF H2 HW1 HFl Hc.
 set (d := phase_driven_state p ev pre) in *.
 assert (Hup := rf2_updates p d P c c2 [SAssign true e lhs] sts2 HB HF eq_refl H2).
 rewrite Hc in Hup. cbn [Z.eqb] in Hup.
 apply (bank_phase_frame p ev pre r P HU HE HFl). change (updates_avoid r (process_updates p d P)). rewrite Hup. cbn [app].
 destruct (Z.eqb (eval_expr d c2) 0); [intros u []|exact (nba_updates_avoid d r sts2 HW1)].
Qed.
End ExtendedSVBankRebase.
Print Assumptions ExtendedSVBankRebase.operand_clause_rebased.
Print Assumptions ExtendedSVBankRebase.rf2_lane_write.
Print Assumptions ExtendedSVBankRebase.rf2_frame.
Print Assumptions ExtendedSVBankRebase.RFRelR_write.
