(** Carry real ID/EX sampling through the remaining scheduler phases. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection
 Lang.ExtendedSVProcessSlice Ex.Generated.CV32E40PExtendedAST
 Ex.External.CV32E40PAddiIDEXHold Ex.External.CV32E40PReq39Trace.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVProcessSlice
 CV32E40PExtendedAST CV32E40PAddiIDEXHold CV32E40PReq39Trace.
Module CV32E40PAddiIDEXCycle.
 #[local] Opaque PhaseSemantics phase_driven_state read_signal.
 Theorem unselected_idex_preserved ev pre root :
   In root idex_roots -> changed_signal ev <> root ->
   process_matches_states pre (phase_driven_state cv32e40p_program ev pre) process_23 = false ->
   read_signal (PhaseSemantics cv32e40p_program ev pre) root = read_signal pre root.
 Proof.
   intros Hr He Hfire.
   rewrite phase_root_projection by (auto using idex_comb_unwritten).
   unfold phase_update_chain, selected_on_transition.
   rewrite process_slice_sound, filter_swap, idex_unique_writers by exact Hr.
   cbn [filter]. rewrite Hfire. reflexivity.
 Qed.
 Definition FallingIDEXQuiet image s :=
   process_matches_states (rising_state_image image s)
     (phase_driven_state cv32e40p_program clk_fall (rising_state_image image s)) process_23 = false.
 Theorem cycle_idex_equals_rising image s root :
   In root idex_roots -> FallingIDEXQuiet image s ->
   read_signal (trace_rtl (full_cycle_image image s)) root =
   read_signal (rising_state_image image s) root.
 Proof.
   intros Hr Hquiet.
   change (read_signal (lfp_candidate cv32e40p_program (falling_state_image image s)) root =
     read_signal (rising_state_image image s) root).
   rewrite lfp_candidate_preserves_unwritten_root by (now apply idex_comb_unwritten).
   unfold falling_state_image. apply unselected_idex_preserved; [exact Hr| |exact Hquiet].
   cbn [idex_roots In] in Hr. change (7%nat <> root). intuition congruence.
 Qed.
 Print Assumptions cycle_idex_equals_rising.
End CV32E40PAddiIDEXCycle.
