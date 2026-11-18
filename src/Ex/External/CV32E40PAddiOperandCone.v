(** From actual ordered FullCore rounds to actual ID/EX operand registers.
    No replacement transition, fixed-point assumption, or expected post-state
    is used.  Controller choices and architectural source validity remain
    separate obligations of the reset-reachable invariant. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVCombCut.
Require Import Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiOperands
  Ex.External.CV32E40PAddiDecoderPhase Ex.External.CV32E40PAddiIDEXAccept.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVCombCut
  CV32E40PExtendedAST CV32E40PAddiOperands CV32E40PAddiDecoderPhase
  CV32E40PAddiIDEXAccept CV32E40PAddiDecoder.CV32E40PAddiDecoder.
Local Open Scope Z_scope.
Module CV32E40PAddiOperandCone.
  Definition cut := before_process cv32e40p_program.
  Definition round := comb_round cv32e40p_program.
  Lemma cut_next n proc s : nth_error (processes cv32e40p_program) n = Some proc ->
    is_comb proc = true -> cut (S n) s = run_process cv32e40p_program (cut n s) proc.
  Proof. apply before_process_next. Qed.
  Lemma forward_suffix : avoids_root 837%nat
    (filter is_comb (skipn 1630 (processes cv32e40p_program))) = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma a_suffix : avoids_root 844%nat
    (filter is_comb (skipn 1629 (processes cv32e40p_program))) = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma b_suffix : avoids_root 845%nat
    (filter is_comb (skipn 1634 (processes cv32e40p_program))) = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma forward_prefix : avoids_root 837%nat
    (filter is_comb (firstn 1628 (processes cv32e40p_program))) = true.
  Proof. vm_compute. reflexivity. Qed.
  #[local] Opaque before_process comb_round.
  Theorem round_forward_value s : norm 32 (read_signal (round s) 837%nat) =
    forward_value (cut 1629 s).
  Proof.
    unfold round. rewrite (comb_cut_root cv32e40p_program 1629 process_1629 s 837%nat eq_refl eq_refl forward_suffix).
    apply actual_forward_mux.
  Qed.
  Theorem round_a_value s : norm 3 (read_signal (cut 1628 s) 781%nat) = 0 ->
    norm 32 (read_signal (round s) 844%nat) = norm 32 (read_signal s 837%nat).
  Proof.
    intros H. unfold round.
    rewrite (comb_cut_root cv32e40p_program 1628 process_1628 s 844%nat eq_refl eq_refl a_suffix).
    rewrite actual_a_mux by exact H.
    rewrite before_process_keeps_root by exact forward_prefix. reflexivity.
  Qed.
  Lemma keep root proc s : existsb (Nat.eqb root) (process_writers proc) = false ->
    read_signal (run_process cv32e40p_program s proc) root = read_signal s root.
  Proof. intros H. apply run_process_preserves_unwritten_root. now apply unwritten_checked. Qed.

  (** These checks are on the original process AST, not a handwritten cone. *)
  Lemma p1630_keeps_782 s : read_signal (run_process cv32e40p_program s process_1630) 782%nat = read_signal s 782%nat.
  Proof. apply keep. reflexivity. Qed.
  Lemma p1630_keeps_860 s : read_signal (run_process cv32e40p_program s process_1630) 860%nat = read_signal s 860%nat.
  Proof. apply keep. reflexivity. Qed.
  Lemma p1631_keeps_860 s : read_signal (run_process cv32e40p_program s process_1631) 860%nat = read_signal s 860%nat.
  Proof. apply keep. reflexivity. Qed.
  Lemma p1632_keeps_860 s : read_signal (run_process cv32e40p_program s process_1632) 860%nat = read_signal s 860%nat.
  Proof. apply keep. reflexivity. Qed.
  Lemma p1632_keeps_840 s : read_signal (run_process cv32e40p_program s process_1632) 840%nat = read_signal s 840%nat.
  Proof. apply keep. reflexivity. Qed.

  Theorem round_b_value s :
    norm 4 (read_signal (cut 1630 s) 786%nat) = 0 ->
    norm 3 (read_signal (cut 1630 s) 782%nat) = 2 ->
    norm 1 (read_signal (cut 1630 s) 860%nat) = 0 ->
    norm 32 (read_signal (round s) 845%nat) = norm 32 (read_signal (cut 1630 s) 742%nat).
  Proof.
    intros Hi Hb Hscalar.
    assert (H31 : cut 1631 s = run_process cv32e40p_program (cut 1630 s) process_1630).
    { apply cut_next; reflexivity. }
    assert (H32 : cut 1632 s = run_process cv32e40p_program (cut 1631 s) process_1631).
    { apply cut_next; reflexivity. }
    assert (H33 : cut 1633 s = run_process cv32e40p_program (cut 1632 s) process_1632).
    { apply cut_next; reflexivity. }
    assert (Hscalar' : norm 1 (read_signal (cut 1633 s) 860%nat) = 0).
    { rewrite H33, p1632_keeps_860, H32, p1631_keeps_860, H31, p1630_keeps_860. exact Hscalar. }
    assert (Hb' : norm 3 (read_signal (cut 1631 s) 782%nat) = 2).
    { rewrite H31, p1630_keeps_782. exact Hb. }
    unfold round. rewrite (comb_cut_root cv32e40p_program 1633 process_1633 s 845%nat eq_refl eq_refl b_suffix).
    change (norm 32 (read_signal (run_process cv32e40p_program (cut 1633 s) process_1633) 845%nat) =
      norm 32 (read_signal (cut 1630 s) 742%nat)).
    rewrite actual_scalar_mux by exact Hscalar'.
    rewrite H33, p1632_keeps_840, H32, actual_b_mux by exact Hb'.
    rewrite H31, actual_immediate_mux by exact Hi. reflexivity.
  Qed.

  Theorem two_round_operands s :
    norm 3 (read_signal (cut 1628 (round s)) 781%nat) = 0 ->
    norm 4 (read_signal (cut 1630 (round s)) 786%nat) = 0 ->
    norm 3 (read_signal (cut 1630 (round s)) 782%nat) = 2 ->
    norm 1 (read_signal (cut 1630 (round s)) 860%nat) = 0 ->
    norm 32 (read_signal (round (round s)) 844%nat) = forward_value (cut 1629 s) /\
    norm 32 (read_signal (round (round s)) 845%nat) = norm 32 (read_signal (cut 1630 (round s)) 742%nat).
  Proof.
    intros Ha Hi Hb Hscalar. split.
    - rewrite round_a_value by exact Ha. apply round_forward_value.
    - apply round_b_value; assumption.
  Qed.
  Definition round6 ev pre := comb_iter cv32e40p_program 6
    (write_signal pre (changed_signal ev) (new_value ev)).
  Definition OperandChoices ev pre :=
    let r7 := round (round6 ev pre) in
    norm 3 (read_signal (cut 1628 r7) 781%nat) = 0 /\
    norm 4 (read_signal (cut 1630 r7) 786%nat) = 0 /\
    norm 3 (read_signal (cut 1630 r7) 782%nat) = 2 /\
    norm 1 (read_signal (cut 1630 r7) 860%nat) = 0.
  Definition actual_forward_input ev pre := forward_value (cut 1629 (round6 ev pre)).
  Definition actual_immediate_input ev pre := norm 32
    (read_signal (cut 1630 (round (round6 ev pre))) 742%nat).
  Lemma driven_two_rounds ev pre : phase_driven_state cv32e40p_program ev pre =
    round (round (round6 ev pre)).
  Proof.
    rewrite phase_driven_last_round, (comb_iter_last _ 6). reflexivity.
  Qed.
  Theorem driven_operands ev pre : OperandChoices ev pre ->
    norm 32 (read_signal (phase_driven_state cv32e40p_program ev pre) 844%nat) = actual_forward_input ev pre /\
    norm 32 (read_signal (phase_driven_state cv32e40p_program ev pre) 845%nat) = actual_immediate_input ev pre.
  Proof.
    intros (Ha & Hi & Hb & Hscalar). rewrite driven_two_rounds.
    now apply two_round_operands.
  Qed.
  Theorem accepted_operands_are_actual_sources ev pre :
    OperandChoices ev pre ->
    accept_add_inputs (phase_driven_state cv32e40p_program ev pre) ->
    changed_signal ev <> 589%nat -> changed_signal ev <> 590%nat ->
    process_matches_states pre (phase_driven_state cv32e40p_program ev pre) process_23 = true ->
    norm 32 (read_signal (PhaseSemantics cv32e40p_program ev pre) 589%nat) = actual_forward_input ev pre /\
    norm 32 (read_signal (PhaseSemantics cv32e40p_program ev pre) 590%nat) = actual_immediate_input ev pre.
  Proof.
    intros Hchoices Haccept Hea Heb Hfire.
    destruct (driven_operands _ _ Hchoices) as [Ha Hb]. split.
    - rewrite (fullcore_accepts_add_fields ev pre 589%nat
        ltac:(unfold CV32E40PAddiIDEXHold.CV32E40PAddiIDEXHold.idex_roots; simpl; auto) Hea Haccept Hfire).
      change (norm 32 (write_slice (read_signal pre 589%nat) 0 32
        (norm 32 (read_signal (phase_driven_state cv32e40p_program ev pre) 844%nat))) = actual_forward_input ev pre).
      rewrite norm_write_low, norm_twice. exact Ha.
    - rewrite (fullcore_accepts_add_fields ev pre 590%nat
        ltac:(unfold CV32E40PAddiIDEXHold.CV32E40PAddiIDEXHold.idex_roots; simpl; auto) Heb Haccept Hfire).
      change (norm 32 (write_slice (read_signal pre 590%nat) 0 32
        (norm 32 (read_signal (phase_driven_state cv32e40p_program ev pre) 845%nat))) = actual_immediate_input ev pre).
      rewrite norm_write_low, norm_twice. exact Hb.
  Qed.
  Print Assumptions two_round_operands.
  Print Assumptions accepted_operands_are_actual_sources.
End CV32E40PAddiOperandCone.
