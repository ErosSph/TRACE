(** Exact source-B forwarding and operand cone in the generated CV32E40P AST.
    The B operand mux precedes the B forwarding mux in one combinational round,
    so the selected value reaches the scalar operand on the following round. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection
  Lang.ExtendedSVCombCut Lang.ExtendedSVBlocking.
Require Import Ex.Generated.CV32E40PExtendedAST
  Ex.External.CV32E40PAddiOperands Ex.External.CV32E40PAddiOperandCone.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVCombCut
  ExtendedSVBlocking CV32E40PExtendedAST
  CV32E40PAddiOperands.CV32E40PAddiOperands CV32E40PAddiOperandCone
  CV32E40PAddiDecoder.CV32E40PAddiDecoder
  CV32E40PAddiIDEXAccept.CV32E40PAddiIDEXAccept.
Local Open Scope Z_scope.
Module CV32E40PForwardOperandB.
 Definition forward_value_b s :=
   if norm 2 (read_signal s 835%nat) =? 1 then norm 32 (read_signal s 695%nat)
   else if norm 2 (read_signal s 835%nat) =? 2 then norm 32 (read_signal s 691%nat)
   else norm 32 (read_signal s 777%nat).

 Lemma actual_forward_mux_b s :
   norm 32 (read_signal (run_process cv32e40p_program s process_1634) 838%nat) =
   forward_value_b s.
 Proof.
   unfold forward_value_b.
   rewrite blocking_run_process by reflexivity.
   change (statement_fuel cv32e40p_program) with 512%nat.
   cbn [process_1634 process_body].
   rewrite exec_sequence, fold_one, exec_sequence, fold_one, exec_case.
   cbn [eval_expr blocking_state].
   destruct (norm 2 (read_signal s 835%nat) =? 1) eqn:H1;
     [|destruct (norm 2 (read_signal s 835%nat) =? 2) eqn:H2];
     try destruct (norm 2 (read_signal s 835%nat) =? 0) eqn:H0;
     cbn [select_case_stmt eval_expr blocking_state];
     change (norm 2 1) with 1; change (norm 2 2) with 2;
     change (norm 2 0) with 0.
   all: rewrite ?H1, ?H2, ?H0.
   all: cbv beta iota zeta delta [exec_stmt resolve_update resolve_lvalue apply_update
     update_signal update_offset update_width update_value eval_expr blocking_state];
     rewrite read_signal_write_same, norm_write_low, !norm_twice; reflexivity.
 Qed.

 Lemma actual_b_register_mux s : norm 3 (read_signal s 782%nat) = 0 ->
   norm 32 (read_signal (run_process cv32e40p_program s process_1631) 840%nat) =
   norm 32 (read_signal s 838%nat).
 Proof.
   intros H. rewrite blocking_run_process by reflexivity.
   change (statement_fuel cv32e40p_program) with 512%nat.
   cbn [process_1631 process_body].
   rewrite exec_sequence, fold_one, exec_sequence, fold_one, exec_case.
   cbn [eval_expr blocking_state]. rewrite H.
   cbn [select_case_stmt eval_expr]. change (norm 3 0) with 0. cbn [Z.eqb].
   change (norm 32 (read_signal (blocking_state
     (exec_stmt 509 (SAssign false (EVar 32 838%nat) (LVar 32 840%nat))
       {| blocking_state := s; pending_nba := []; emitted_updates := [] |})) 840%nat) =
     norm 32 (read_signal s 838%nat)).
   cbv beta iota zeta delta [exec_stmt resolve_update resolve_lvalue apply_update
     update_signal update_offset update_width update_value eval_expr blocking_state].
   rewrite read_signal_write_same, norm_write_low, !norm_twice. reflexivity.
 Qed.

 Lemma forward_b_suffix : avoids_root 838%nat
   (filter is_comb (skipn 1635 (processes cv32e40p_program))) = true.
 Proof. vm_compute. reflexivity. Qed.
 Lemma forward_b_prefix : avoids_root 838%nat
   (filter is_comb (firstn 1634 (processes cv32e40p_program))) = true.
 Proof. vm_compute. reflexivity. Qed.
 Lemma b_mux_prefix : avoids_root 838%nat
   (filter is_comb (firstn 1631 (processes cv32e40p_program))) = true.
 Proof. vm_compute. reflexivity. Qed.
 #[local] Opaque before_process comb_round.
 Theorem round_forward_value_b s : norm 32 (read_signal (round s) 838%nat) =
   forward_value_b (cut 1634 s).
 Proof.
   unfold round. rewrite (comb_cut_root cv32e40p_program 1634 process_1634 s 838%nat
     eq_refl eq_refl forward_b_suffix). apply actual_forward_mux_b.
 Qed.

 Theorem round_b_register_value s :
   norm 3 (read_signal (cut 1631 s) 782%nat) = 0 ->
   norm 1 (read_signal (cut 1631 s) 860%nat) = 0 ->
   norm 32 (read_signal (round s) 845%nat) = norm 32 (read_signal s 838%nat).
 Proof.
   intros Hb Hscalar.
   assert (H32 : cut 1632 s = run_process cv32e40p_program (cut 1631 s) process_1631).
   { apply cut_next; reflexivity. }
   assert (H33 : cut 1633 s = run_process cv32e40p_program (cut 1632 s) process_1632).
   { apply cut_next; reflexivity. }
   assert (Hscalar' : norm 1 (read_signal (cut 1633 s) 860%nat) = 0).
   { rewrite H33, p1632_keeps_860, H32, p1631_keeps_860. exact Hscalar. }
   unfold round. rewrite (comb_cut_root cv32e40p_program 1633 process_1633 s 845%nat
     eq_refl eq_refl b_suffix).
   change (norm 32 (read_signal (run_process cv32e40p_program (cut 1633 s) process_1633)
     845%nat) = norm 32 (read_signal s 838%nat)).
   rewrite actual_scalar_mux by exact Hscalar'.
   rewrite H33, p1632_keeps_840, H32, actual_b_register_mux by exact Hb.
   unfold cut.
   rewrite before_process_keeps_root by exact b_mux_prefix. reflexivity.
 Qed.

 Definition RegisterBChoices s :=
   norm 3 (read_signal (cut 1631 (round s)) 782%nat) = 0 /\
   norm 1 (read_signal (cut 1631 (round s)) 860%nat) = 0.
 Theorem two_round_register_b s : RegisterBChoices s ->
   norm 32 (read_signal (round (round s)) 845%nat) =
   forward_value_b (cut 1634 s).
 Proof.
   intros [Hb Hscalar]. rewrite round_b_register_value by assumption.
   apply round_forward_value_b.
 Qed.

 Definition actual_forward_input_b ev pre :=
   forward_value_b (cut 1634 (round6 ev pre)).
 Definition RegisterBOperandChoices ev pre :=
   RegisterBChoices (round6 ev pre).
 Theorem driven_register_b ev pre : RegisterBOperandChoices ev pre ->
   norm 32 (read_signal (phase_driven_state cv32e40p_program ev pre) 845%nat) =
   actual_forward_input_b ev pre.
 Proof.
   intros H. rewrite driven_two_rounds. now apply two_round_register_b.
 Qed.
 Print Assumptions round_forward_value_b.
 Print Assumptions driven_register_b.
End CV32E40PForwardOperandB.
