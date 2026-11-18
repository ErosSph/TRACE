(** OBI adapter: an externally granted transfer cannot leave a held request. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVBlocking Lang.ExtendedSVRootProjection
 Lang.ExtendedSVProcessSlice Lang.ExtendedSVCombCut Lang.ExtendedSVNBAProjection
 Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PFetchFIFOCount
 Ex.External.CV32E40PAddiDecoder Ex.External.CV32E40PAddiForwardControl
 Ex.External.CV32E40PAddiOperands Ex.External.CV32E40PAddiIDEXAccept
 Ex.External.CV32E40PAddiOperandCone Ex.External.CV32E40PAddiDecoderPhase
 Ex.External.CV32E40PRequestWiring.
Import ListNotations ExtendedSV ExtendedSVBlocking ExtendedSVRootProjection
 ExtendedSVProcessSlice ExtendedSVCombCut ExtendedSVNBAProjection CV32E40PExtendedAST
 CV32E40PAddiDecoder CV32E40PAddiForwardControl CV32E40PAddiOperands
 CV32E40PAddiIDEXAccept CV32E40PAddiOperandCone CV32E40PAddiDecoderPhase
 CV32E40PFetchFIFOCount CV32E40PRequestWiring.
Local Open Scope Z_scope.
Module CV32E40POBIAdapter.
 #[local] Opaque norm read_signal write_signal write_slice.
 Lemma exec_block_assign fuel e lv es :
   exec_stmt (S fuel) (SAssign false e lv) es =
   let u := resolve_update (blocking_state es) lv (eval_expr (blocking_state es) e) in
   {| blocking_state := apply_update (blocking_state es) u;
      pending_nba := pending_nba es; emitted_updates := emitted_updates es ++ [u] |}.
 Proof. reflexivity. Qed.
 Lemma granted_next s : norm 1 (read_signal s 496%nat) = 1 ->
   norm 1 (read_signal (run_process cv32e40p_program s process_1575) 506%nat) = 0.
 Proof.
   intros Hg. rewrite blocking_run_process by reflexivity.
   change (statement_fuel cv32e40p_program) with 512%nat.
   cbn [process_1575 process_body].
   rewrite exec_sequence, fold_one, exec_sequence, fold_cons, fold_one, exec_case.
   rewrite exec_block_assign.
   cbv beta iota zeta delta [blocking_state eval_expr apply_update resolve_update resolve_lvalue
     update_signal update_offset update_width update_value Z.of_nat Pos.of_succ_nat].
   rewrite read_signal_write_other by discriminate.
   destruct (bit_cases (read_signal s 505%nat)) as [Hs|Hs]; rewrite Hs;
     cbn [select_case_stmt eval_expr]; change (norm 1 0) with 0; change (norm 1 1) with 1;
     cbn [Z.eqb Pos.eqb select_case_stmt].
   all: rewrite exec_sequence, fold_one, exec_if.
   all:
     cbn [blocking_state eval_expr];
     repeat rewrite read_signal_write_other by discriminate;
     rewrite Hg; change (norm 1 (Z.lnot 1)) with 0; rewrite ?Z.land_0_r;
     change (norm 1 0) with 0; change (norm 1 1) with 1;
     cbn [Z.eqb]; straight; rewrite ?Hs; reflexivity.
 Qed.
 #[local] Opaque before_process comb_round run_process.
 Lemma round_granted s : norm 1 (read_signal s 17%nat) = 1 ->
   norm 1 (read_signal (round s) 506%nat) = 0.
 Proof.
   intros Hg. unfold round.
   rewrite (comb_cut_root cv32e40p_program 1575 process_1575 s 506%nat
     eq_refl eq_refl ltac:(vm_compute; reflexivity)).
   apply granted_next.
   rewrite <- (cut_final_root cv32e40p_program 1575 s 496%nat ltac:(vm_compute; reflexivity)).
   rewrite grant_wiring. exact Hg.
 Qed.
 Lemma sequential_state s old :
   norm 1 (apply_updates_root_value 505%nat old (process_updates cv32e40p_program s process_21)) =
   if norm 1 (read_signal s 484%nat) =? 0 then 0 else norm 1 (read_signal s 506%nat).
 Proof.
   rewrite process_nba_pruned_projection by reflexivity.
   change (statement_fuel cv32e40p_program) with 512%nat.
   cbn [nba_root_pruned process_21 process_body stmt_writers lvalue_root flat_map fold_left existsb Nat.eqb app orb eval_expr].
   change (norm 1 (if norm 1 (read_signal s 484%nat) =? 0
     then write_slice old 0 1 (norm 1 (norm 1 0))
     else write_slice old 0 1 (norm 1 (norm 1 (read_signal s 506%nat)))) =
     if norm 1 (read_signal s 484%nat) =? 0 then 0 else norm 1 (read_signal s 506%nat)).
   destruct (norm 1 (read_signal s 484%nat) =? 0); rewrite norm_write_low, !norm_twice; reflexivity.
 Qed.
 Lemma state_unwritten : comb_root_unwrittenb cv32e40p_program 505%nat = true.
 Proof. vm_compute; reflexivity. Qed.
 Lemma state_writers : filter (writes_rootb 505%nat) (processes cv32e40p_program) = [process_21].
 Proof. vm_compute; reflexivity. Qed.
 #[local] Opaque PhaseSemantics phase_driven_state process_updates apply_updates_root_value.
 Theorem granted_phase_preserves_empty ev pre :
   changed_signal ev <> 505%nat -> changed_signal ev <> 17%nat ->
   norm 1 (read_signal pre 505%nat) = 0 -> norm 1 (read_signal pre 17%nat) = 1 ->
   norm 1 (read_signal (PhaseSemantics cv32e40p_program ev pre) 505%nat) = 0.
 Proof.
   intros Hstate Hgrant Hempty Hg.
   assert (Hnext : norm 1 (read_signal (phase_driven_state cv32e40p_program ev pre) 506%nat) = 0).
   { rewrite phase_driven_last_round. apply round_granted.
     rewrite comb_iter_preserves_unwritten_root by (vm_compute; reflexivity).
     rewrite read_signal_write_other by exact Hgrant. exact Hg. }
   rewrite phase_root_projection by auto using state_unwritten.
   unfold phase_update_chain, selected_on_transition.
   rewrite process_slice_sound, filter_swap, state_writers. cbn [filter].
   destruct (process_matches_states pre (phase_driven_state cv32e40p_program ev pre) process_21);
     cbn [flat_map]; rewrite ?app_nil_r; [|exact Hempty].
   rewrite sequential_state, Hnext.
   destruct (norm 1 (read_signal (phase_driven_state cv32e40p_program ev pre) 484%nat) =? 0); reflexivity.
 Qed.
 Print Assumptions granted_phase_preserves_empty.
End CV32E40POBIAdapter.
