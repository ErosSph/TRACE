(** Actual instruction rd -> ID mux -> ID/EX destination, no expected-rd premise.
    Decoder mode/acceptance controls remain explicit reachable-state obligations. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVCombCut
  Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiAdderInputs
  Ex.External.CV32E40PAddiAdderBits Ex.External.CV32E40PAddiOperandCone
  Ex.External.CV32E40PAddiDecoderPhase Ex.External.CV32E40PAddiIDEXAccept
  Ex.External.CV32E40PAddiTokenSampling Ex.External.CV32E40PAddiTokenOrigin
  Ex.External.CV32E40PAddiReachability Ex.External.CV32E40PReq39Trace.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVCombCut
  CV32E40PExtendedAST CV32E40PAddiAdderInputs CV32E40PAddiAdderBits
  CV32E40PAddiOperandCone CV32E40PAddiDecoderPhase CV32E40PAddiIDEXAccept
  CV32E40PAddiTokenSampling CV32E40PAddiTokenOrigin CV32E40PAddiReachability CV32E40PReq39Trace.
Local Open Scope Z_scope.
Module CV32E40PAddiDestination.
  Definition instruction_rd ins := norm 5 (Z.shiftr (norm 32 ins) 7).
  Lemma extend_rd x : norm 6 (norm 5 x) = norm 5 x.
  Proof. apply norm_small. pose proof (norm_range 5 x). change (0 <= norm 5 x < 64). change (0 <= norm 5 x < 32) in H. lia. Qed.
  Lemma actual_integer_rd s : norm 1 (read_signal s 771%nat) = 0 ->
    norm 6 (read_signal (run_process cv32e40p_program s process_1409) 772%nat) =
      instruction_rd (read_signal s 718%nat).
  Proof.
    intros H. rewrite (assign_value s process_1409 6 772%nat (rhs process_1409) eq_refl).
    unfold rhs, instruction_rd. cbn [process_1409 process_body eval_expr expr_width]. rewrite H.
    change (norm 5 7) with 7. rewrite Z.shiftl_0_l, Z.lor_0_l, norm_twice. apply extend_rd.
  Qed.
  Lemma actual_rd_mux s : norm 1 (read_signal s 811%nat) = 1 ->
    norm 6 (read_signal (run_process cv32e40p_program s process_1450) 773%nat) =
      norm 6 (read_signal s 772%nat).
  Proof.
    intros H. rewrite (assign_value s process_1450 6 773%nat (rhs process_1450) eq_refl).
    unfold rhs. cbn [process_1450 process_body eval_expr]. rewrite H. cbn [Z.eqb]. now rewrite !norm_twice.
  Qed.
  #[local] Opaque comb_round before_process run_process.
  Theorem round_destination s :
    norm 1 (read_signal (round s) 771%nat) = 0 ->
    norm 1 (read_signal (round s) 811%nat) = 1 ->
    norm 6 (read_signal (round s) 773%nat) = instruction_rd (read_signal (round s) 718%nat).
  Proof.
    intros Hfp Hmux. unfold round in *.
    rewrite (comb_cut_root cv32e40p_program 1450 process_1450 s 773%nat
      eq_refl eq_refl ltac:(vm_compute; reflexivity)).
    rewrite actual_rd_mux.
    2: { rewrite <- (cut_final_root cv32e40p_program 1450 s 811%nat ltac:(vm_compute; reflexivity)). exact Hmux. }
    rewrite <- (cut_final_root cv32e40p_program 1450 s 772%nat ltac:(vm_compute; reflexivity)).
    rewrite (comb_cut_root cv32e40p_program 1409 process_1409 s 772%nat
      eq_refl eq_refl ltac:(vm_compute; reflexivity)).
    rewrite actual_integer_rd.
    - rewrite <- (cut_final_root cv32e40p_program 1409 s 718%nat ltac:(vm_compute; reflexivity)). reflexivity.
    - rewrite <- (cut_final_root cv32e40p_program 1409 s 771%nat ltac:(vm_compute; reflexivity)). exact Hfp.
  Qed.
  Theorem phase_destination ev pre :
    norm 1 (read_signal (phase_driven_state cv32e40p_program ev pre) 771%nat) = 0 ->
    norm 1 (read_signal (phase_driven_state cv32e40p_program ev pre) 811%nat) = 1 ->
    norm 6 (read_signal (phase_driven_state cv32e40p_program ev pre) 773%nat) =
      instruction_rd (read_signal (phase_driven_state cv32e40p_program ev pre) 718%nat).
  Proof. rewrite phase_driven_last_round. apply round_destination. Qed.
  Theorem accepted_destination_from_actual_instruction ev pre :
    changed_signal ev <> 598%nat ->
    accept_add_inputs (phase_driven_state cv32e40p_program ev pre) ->
    norm 1 (read_signal (phase_driven_state cv32e40p_program ev pre) 774%nat) = 1 ->
    norm 1 (read_signal (phase_driven_state cv32e40p_program ev pre) 771%nat) = 0 ->
    norm 1 (read_signal (phase_driven_state cv32e40p_program ev pre) 811%nat) = 1 ->
    process_matches_states pre (phase_driven_state cv32e40p_program ev pre) process_23 = true ->
    norm 6 (read_signal (PhaseSemantics cv32e40p_program ev pre) 598%nat) =
      instruction_rd (read_signal (phase_driven_state cv32e40p_program ev pre) 718%nat).
  Proof.
    intros Hev Haccept Hwe Hfp Hmux Hfire.
    rewrite (fullcore_accepts_add_fields ev pre 598%nat
      ltac:(unfold CV32E40PAddiIDEXHold.CV32E40PAddiIDEXHold.idex_roots; cbn; auto) Hev Haccept Hfire).
    cbn [accepted_field]. rewrite Hwe. cbn [Z.eqb].
    rewrite CV32E40PAddiOperands.CV32E40PAddiOperands.norm_write_low, norm_twice.
    apply phase_destination; assumption.
  Qed.
  #[local] Opaque PhaseSemantics phase_driven_state environment_state_image.
  Theorem issued_token_destination image s token :
    issued image s = Some token ->
    accept_add_inputs (edge_input image s) ->
    norm 1 (read_signal (edge_input image s) 774%nat) = 1 ->
    norm 1 (read_signal (edge_input image s) 771%nat) = 0 ->
    norm 1 (read_signal (edge_input image s) 811%nat) = 1 ->
    process_matches_states (environment_state_image image (physical_state s))
      (edge_input image s) process_23 = true ->
    norm 6 (read_signal (rising_state_image image (physical_state s)) 598%nat) =
      instruction_rd (token_instruction token).
  Proof.
    intros Hissue Haccept Hwe Hfp Hmux Hfire.
    pose proof (accepted_destination_from_actual_instruction clk_rise
      (environment_state_image image (physical_state s)) ltac:(discriminate)
      Haccept Hwe Hfp Hmux Hfire) as Hdest.
    unfold rising_state_image. rewrite Hdest.
    pose proof (proj1 (issued_has_edge_sample image s token Hissue)) as Hword.
    unfold instruction_rd. unfold edge_input in Hword.
    exact (eq_sym (f_equal (fun w => norm 5 (Z.shiftr w 7)) Hword)).
  Qed.
  Print Assumptions issued_token_destination.
End CV32E40PAddiDestination.
