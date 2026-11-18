(** One-level-shallower variant of ExtendedSVSeqTree2 / ExtendedSVSeqTree2Slice (template route, 2026-11-04; additive, nothing existing is
    changed).  The accepted lemmas require a process body of the shape [SSeq [SSeq [t]]] (one statement below the two sequence wrappers);
    sequential processes without a reset test are emitted as [SSeq [SSeq l]] with SEVERAL statements in [l] (angelo5fix processes 0 and 2:
    the wrapper memory read port and the register-file process).  Here the body is [SSeq [t]] with [t := SSeq l], i.e. the inner sequence
    itself is the converted statement ([conv2] maps [SSeq l] to [T2Cat]).  Same conclusions as [seq_tree2m_value] / [seq_tree2s_value].
    Generic, design independent.  proof_author: LLM-generated: Claude Code (claude-opus-5-5); external_llm_api_calls=0. *)
From Coq Require Import List ZArith Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice
 Lang.ExtendedSVAssignment Lang.ExtendedSVEmptyPipeline Lang.ExtendedSVWordInvariant Lang.ExtendedSVSeqStep Lang.ExtendedSVSeqTree
 Lang.ExtendedSVSeqTree2 Lang.ExtendedSVSeqTree2Slice.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVProcessSlice ExtendedSVAssignment ExtendedSVWordInvariant ExtendedSVSeqStep
 ExtendedSVSeqTree ExtendedSVSeqTree2 ExtendedSVSeqTree2Slice.
Local Open Scope Z_scope.
Module ExtendedSVSeqTree2One.

Lemma process_updates_tree2_one : forall p s proc k t T,
 process_body proc = SSeq [t] -> Rel2 k t T -> (k + 1 <= statement_fuel p)%nat ->
 process_updates p s proc = nba_updates s (tleaf2 s T).
Proof.
 intros p s proc k t T HB HR HF. unfold process_updates. rewrite HB.
 destruct (statement_fuel p) as [|f]; try lia.
 rewrite exec_seq. cbn [fold_left].
 rewrite (exec_rel2 k t T HR f _) by lia. cbn [emitted_updates blocking_state]. reflexivity.
Qed.

Theorem seq_tree2m_value_one : forall p ev pre r P t T kf w,
 comb_root_unwrittenb p r = true -> changed_signal ev <> r ->
 process_body P = SSeq [t] -> Rel2 kf t T -> (kf + 1 <= statement_fuel p)%nat ->
 filter (process_matches_states pre (phase_driven_state p ev pre)) (filter (writes_rootb r) (processes p)) = [P] ->
 twf2m w r T = true ->
 norm w (read_signal (PhaseSemantics p ev pre) r) = norm w (eval_expr (phase_driven_state p ev pre) (texpr2m w r T)).
Proof.
 intros p ev pre r P t T kf w HU HE HB HR HF HW HWF.
 destruct (texpr2m_lastw w r (phase_driven_state p ev pre) T HWF) as [H1 H2].
 rewrite H1.
 rewrite (seq_upd_valuem p ev pre r P _ w HU HE HW (process_updates_tree2_one p _ P kf t T HB HR HF) H2).
 apply lastw_cong. cbn [eval_expr]. rewrite norm_idempotent. reflexivity.
Qed.

Theorem seq_tree2s_value_one : forall p ev pre r P t T kf,
 comb_root_unwrittenb p r = true -> changed_signal ev <> r ->
 process_body P = SSeq [t] -> Rel2 kf t T -> (kf + 1 <= statement_fuel p)%nat ->
 filter (process_matches_states pre (phase_driven_state p ev pre)) (filter (writes_rootb r) (processes p)) = [P] ->
 read_signal (PhaseSemantics p ev pre) r =
 lastws (phase_driven_state p ev pre) r (tleaf2 (phase_driven_state p ev pre) T) (read_signal (phase_driven_state p ev pre) r).
Proof.
 intros p ev pre r P t T kf HU HE HB HR HF HW.
 rewrite phase_root_projection by assumption.
 unfold phase_update_chain, selected_on_transition.
 rewrite process_slice_sound.
 rewrite filter_swap, HW. cbn [flat_map]. rewrite app_nil_r.
 rewrite (process_updates_tree2_one p _ P kf t T HB HR HF).
 rewrite apply_lastws. rewrite (driven_unchanged p ev pre r HU HE). reflexivity.
Qed.

End ExtendedSVSeqTree2One.
