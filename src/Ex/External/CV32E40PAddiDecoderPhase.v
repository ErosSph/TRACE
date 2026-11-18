(** Actual combinational decoder cone -> driven ID operator -> ID/EX edge.
    Input validity and the remaining controller/operand invariants are explicit
    open premises, not consequences of reset reachability in this file. *)
From Coq Require Import ZArith List.
Require Import Lang.ExtendedSV.
Require Import Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiDecoder
  Ex.External.CV32E40PAddiIDEXHold Ex.External.CV32E40PAddiIDEXAccept.
Import ExtendedSV CV32E40PExtendedAST CV32E40PAddiDecoder
  CV32E40PAddiIDEXHold CV32E40PAddiIDEXAccept.
Local Open Scope Z_scope.
Module CV32E40PAddiDecoderPhase.
  Lemma comb_iter_last p n s :
    comb_iter p (S n) s = comb_round p (comb_iter p n s).
  Proof.
    induction n in s |- *; [reflexivity|].
    cbn [comb_iter]. apply IHn.
  Qed.
  Definition last_decoder_input ev pre := decoder_input_state
    (comb_iter cv32e40p_program 7 (write_signal pre (changed_signal ev) (new_value ev))).
  Definition ADDIAtDecoder ev pre :=
    eval_expr (last_decoder_input ev pre) opcode_expr = 19 /\
    eval_expr (last_decoder_input ev pre) funct_expr = 0.
  #[local] Opaque comb_round comb_iter decoder_input_state.
  Lemma phase_driven_last_round ev pre :
    phase_driven_state cv32e40p_program ev pre =
      comb_round cv32e40p_program
        (comb_iter cv32e40p_program 7 (write_signal pre (changed_signal ev) (new_value ev))).
  Proof.
    unfold phase_driven_state, lfp_candidate.
    change (lfp_fuel cv32e40p_program) with 8%nat.
    apply comb_iter_last.
  Qed.
  Theorem actual_phase_decodes_addi ev pre : ADDIAtDecoder ev pre ->
    norm 7 (read_signal (phase_driven_state cv32e40p_program ev pre) 780%nat) = 24.
  Proof.
    intros [Hop Hfunct]. rewrite phase_driven_last_round.
    apply fullcore_comb_addi_id_operator; assumption.
  Qed.
  Theorem fullcore_accepts_decoded_addi ev pre root :
    In root idex_roots -> changed_signal ev <> root -> ADDIAtDecoder ev pre ->
    (let driven := phase_driven_state cv32e40p_program ev pre in
      norm 1 (read_signal driven 561%nat) = 1 /\
      norm 1 (read_signal driven 662%nat) = 0 /\
      norm 1 (read_signal driven 696%nat) = 0 /\
      norm 1 (read_signal driven 586%nat) = 1 /\
      norm 1 (read_signal driven 779%nat) = 1) ->
    process_matches_states pre (phase_driven_state cv32e40p_program ev pre) process_23 = true ->
    read_signal (PhaseSemantics cv32e40p_program ev pre) root =
      accepted_field (phase_driven_state cv32e40p_program ev pre) root (read_signal pre root).
  Proof.
    intros Hroot Hevent Hdecode (Hr & Hmis & Hmult & Hid & Hen) Hfire.
    apply fullcore_accepts_add_fields; try assumption.
    unfold accept_add_inputs.
    split; [exact Hr|]. split; [exact Hmis|]. split; [exact Hmult|].
    split; [exact Hid|]. split; [exact Hen|]. now apply actual_phase_decodes_addi.
  Qed.
  Print Assumptions actual_phase_decodes_addi.
  Print Assumptions fullcore_accepts_decoded_addi.
End CV32E40PAddiDecoderPhase.
