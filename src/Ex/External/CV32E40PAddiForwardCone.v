(** Real controller -> real wire -> real forwarding mux -> ID/EX.
    The three combinational rounds below are parts of the unchanged eight-round
    phase calculation, not three CPU cycles. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVCombCut.
Require Import Ex.Generated.CV32E40PExtendedAST
  Ex.External.CV32E40PAddiOperands Ex.External.CV32E40PAddiOperandCone
  Ex.External.CV32E40PAddiForwardControl Ex.External.CV32E40PAddiIDEXAccept
  Ex.External.CV32E40PAddiDecoderPhase.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVCombCut
  CV32E40PExtendedAST CV32E40PAddiOperands CV32E40PAddiOperandCone
  CV32E40PAddiForwardControl CV32E40PAddiIDEXAccept CV32E40PAddiDecoderPhase.
Local Open Scope Z_scope.
Module CV32E40PAddiForwardCone.
  Lemma controller_suffix : avoids_root 1108%nat
    (filter is_comb (skipn 1707 (processes cv32e40p_program))) = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma controller_wire_tail : avoids_root 1108%nat
    (filter is_comb (skipn 1742 (processes cv32e40p_program))) = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma selector_suffix : avoids_root 834%nat
    (filter is_comb (skipn 1743 (processes cv32e40p_program))) = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma selector_prefix : avoids_root 834%nat
    (filter is_comb (firstn 1629 (processes cv32e40p_program))) = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma actual_selector_wire s :
    norm 2 (read_signal (run_process cv32e40p_program s process_1742) 834%nat) =
    norm 2 (read_signal s 1108%nat).
  Proof.
    change (norm 2 (read_signal (write_signal s 834%nat
      (write_slice (read_signal s 834%nat) 0 2 (norm 2 (norm 2 (read_signal s 1108%nat))))) 834%nat) =
      norm 2 (read_signal s 1108%nat)).
    rewrite read_signal_write_same, norm_write_low, !norm_twice. reflexivity.
  Qed.
  #[local] Opaque before_process comb_round.
  Theorem round_selector s : norm 2 (read_signal (round s) 834%nat) =
    control_choice (cut 1706 s).
  Proof.
    unfold round.
    rewrite (comb_cut_root cv32e40p_program 1742 process_1742 s 834%nat eq_refl eq_refl selector_suffix).
    rewrite actual_selector_wire.
    rewrite <- (cut_final_root cv32e40p_program 1742 s 1108%nat controller_wire_tail).
    rewrite (comb_cut_root cv32e40p_program 1706 process_1706 s 1108%nat eq_refl eq_refl controller_suffix).
    apply actual_controller_run_priority.
  Qed.
  Definition selected_source choice s :=
    if choice =? 1 then norm 32 (read_signal s 695%nat)
    else if choice =? 2 then norm 32 (read_signal s 691%nat)
    else norm 32 (read_signal s 776%nat).
  Theorem next_round_forward s : forward_value (cut 1629 (round s)) =
    selected_source (control_choice (cut 1706 s)) (cut 1629 (round s)).
  Proof.
    unfold forward_value, selected_source.
    assert (H : norm 2 (read_signal (cut 1629 (round s)) 834%nat) = control_choice (cut 1706 s)).
    { unfold cut. rewrite before_process_keeps_root by exact selector_prefix. apply round_selector. }
    now rewrite H.
  Qed.
  Definition round5 ev pre := comb_iter cv32e40p_program 5
    (write_signal pre (changed_signal ev) (new_value ev)).
  Definition controlled_source ev pre := selected_source
    (control_choice (cut 1706 (round5 ev pre))) (cut 1629 (round6 ev pre)).
  Lemma round6_after_round5 ev pre : round6 ev pre = round (round5 ev pre).
  Proof. unfold round6, round, round5. apply comb_iter_last. Qed.
  Theorem actual_forward_input_is_controlled ev pre :
    actual_forward_input ev pre = controlled_source ev pre.
  Proof.
    unfold actual_forward_input, controlled_source. rewrite round6_after_round5.
    apply next_round_forward.
  Qed.
  Theorem fullcore_accepts_controller_selected_operands ev pre :
    OperandChoices ev pre ->
    accept_add_inputs (phase_driven_state cv32e40p_program ev pre) ->
    changed_signal ev <> 589%nat -> changed_signal ev <> 590%nat ->
    process_matches_states pre (phase_driven_state cv32e40p_program ev pre) process_23 = true ->
    norm 32 (read_signal (PhaseSemantics cv32e40p_program ev pre) 589%nat) = controlled_source ev pre /\
    norm 32 (read_signal (PhaseSemantics cv32e40p_program ev pre) 590%nat) = actual_immediate_input ev pre.
  Proof.
    intros Hchoices Haccept Hea Heb Hfire.
    rewrite <- actual_forward_input_is_controlled.
    exact (accepted_operands_are_actual_sources ev pre Hchoices Haccept Hea Heb Hfire).
  Qed.
  Print Assumptions fullcore_accepts_controller_selected_operands.
End CV32E40PAddiForwardCone.
