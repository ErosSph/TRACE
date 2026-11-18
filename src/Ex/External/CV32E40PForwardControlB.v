(** Priority of the original blocking forwarding controller for RF source B.
    EX overrides WB; a misaligned access forces B back to the register file. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVBlocking
 Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiForwardControl.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVBlocking
 CV32E40PExtendedAST CV32E40PAddiForwardControl
 CV32E40PAddiOperands.CV32E40PAddiOperands
 CV32E40PAddiDecoder.CV32E40PAddiDecoder.
Local Open Scope Z_scope.
Module CV32E40PForwardControlB.
 Definition group_value_b es en b value :=
   if norm 1 (read_signal (blocking_state es) en) =? 0
   then norm 2 (read_signal (blocking_state es) 1109%nat)
   else if norm 1 (read_signal (blocking_state es) b) =? 0
   then norm 2 (read_signal (blocking_state es) 1109%nat) else norm 2 value.
 Lemma source_a_step_preserves es a root value : root <> 1108%nat ->
   read_signal (blocking_state (exec_stmt 508
     (SIf (EVar 1 a) (SAssign false (EConst 2 value) (LVar 2 1108%nat)) SSkip) es)) root =
   read_signal (blocking_state es) root.
 Proof.
   intros Hroot. rewrite exec_if. cbn [eval_expr].
   destruct (norm 1 (read_signal (blocking_state es) a) =? 0); [reflexivity|].
   change (read_signal (write_signal (blocking_state es) 1108%nat
     (write_slice (read_signal (blocking_state es) 1108%nat) 0 2
       (norm 2 (norm 2 value)))) root = read_signal (blocking_state es) root).
   now rewrite read_signal_write_other by congruence.
 Qed.
 Lemma source_b_step_projection es b value :
   norm 2 (read_signal (blocking_state (exec_stmt 508
     (SIf (EVar 1 b) (SAssign false (EConst 2 value) (LVar 2 1109%nat)) SSkip) es))
     1109%nat) =
   if norm 1 (read_signal (blocking_state es) b) =? 0
   then norm 2 (read_signal (blocking_state es) 1109%nat) else norm 2 value.
 Proof.
   rewrite exec_if. cbn [eval_expr].
   destruct (norm 1 (read_signal (blocking_state es) b) =? 0); [reflexivity|].
   change (norm 2 (read_signal (write_signal (blocking_state es) 1109%nat
     (write_slice (read_signal (blocking_state es) 1109%nat) 0 2
       (norm 2 (norm 2 value)))) 1109%nat) = norm 2 value).
   rewrite read_signal_write_same, norm_write_low.
   now rewrite !CV32E40PAddiIDEXAccept.CV32E40PAddiIDEXAccept.norm_twice.
 Qed.
 Lemma source_c_step_preserves_b es c value :
   read_signal (blocking_state (exec_stmt 508
     (SIf (EVar 1 c) (SAssign false (EConst 2 value) (LVar 2 1110%nat)) SSkip) es))
     1109%nat = read_signal (blocking_state es) 1109%nat.
 Proof.
   rewrite exec_if. cbn [eval_expr].
   destruct (norm 1 (read_signal (blocking_state es) c) =? 0); [reflexivity|].
   change (read_signal (write_signal (blocking_state es) 1110%nat
     (write_slice (read_signal (blocking_state es) 1110%nat) 0 2
       (norm 2 (norm 2 value)))) 1109%nat = read_signal (blocking_state es) 1109%nat).
   now rewrite read_signal_write_other by discriminate.
 Qed.
 Lemma group_projection_b es en a b c value :
   b <> 1108%nat ->
   norm 2 (read_signal (blocking_state
     (exec_stmt 510 (forward_group en a b c value) es)) 1109%nat) =
   group_value_b es en b value.
 Proof.
   intros Hba. unfold forward_group, group_value_b. rewrite exec_if. cbn [eval_expr].
   destruct (norm 1 (read_signal (blocking_state es) en) =? 0) eqn:Hen.
   - reflexivity.
   - rewrite exec_sequence, fold_cons, fold_two.
     rewrite source_c_step_preserves_b, source_b_step_projection.
     set (ea := exec_stmt 508
       (SIf (EVar 1 a) (SAssign false (EConst 2 value) (LVar 2 1108%nat)) SSkip) es).
     assert (Ht : read_signal (blocking_state ea) 1109%nat =
       read_signal (blocking_state es) 1109%nat).
     { unfold ea. apply source_a_step_preserves. discriminate. }
     assert (Hb' : read_signal (blocking_state ea) b = read_signal (blocking_state es) b).
     { unfold ea. now apply source_a_step_preserves. }
     now rewrite Hb', Ht.
 Qed.
 Lemma initial_zero_b es :
   norm 2 (read_signal (blocking_state (exec_stmt 511 initial es)) 1109%nat) = 0.
 Proof.
   change (norm 2 (read_signal
     (write_signal (write_signal (write_signal (blocking_state es) 1108%nat
       (write_slice (read_signal (blocking_state es) 1108%nat) 0 2 0))
       1109%nat (write_slice (read_signal (write_signal (blocking_state es) 1108%nat
         (write_slice (read_signal (blocking_state es) 1108%nat) 0 2 0)) 1109%nat) 0 2 0))
       1110%nat (write_slice (read_signal (write_signal (write_signal (blocking_state es) 1108%nat
         (write_slice (read_signal (blocking_state es) 1108%nat) 0 2 0)) 1109%nat
         (write_slice (read_signal (write_signal (blocking_state es) 1108%nat
           (write_slice (read_signal (blocking_state es) 1108%nat) 0 2 0)) 1109%nat) 0 2 0))
         1110%nat) 0 2 0)) 1109%nat) = 0).
   rewrite read_signal_write_other by discriminate.
   rewrite read_signal_write_same, norm_write_low. reflexivity.
 Qed.
 Definition guards_b : list signal := [1058%nat;1106%nat;1107%nat;1115%nat;1118%nat].
 Definition GuardsSameB es es' := forall root, In root guards_b ->
   read_signal (blocking_state es) root = read_signal (blocking_state es') root.
 Lemma component_preserves_guards_b fuel st es :
   forallb (fun root => negb (existsb (Nat.eqb root) (stmt_writers st))) guards_b = true ->
   GuardsSameB (exec_stmt fuel st es) es.
 Proof.
   intros H root Hin. apply forallb_forall with (x := root) in H; [|exact Hin].
   apply negb_true_iff in H.
   apply (proj1 (exec_stmt_preserves_unwritten_root fuel st root es
     (unwritten_checked root st H))).
 Qed.
 Lemma initial_guards_b es : GuardsSameB (exec_stmt 511 initial es) es.
 Proof. apply component_preserves_guards_b. reflexivity. Qed.
 Lemma wb_guards_b es : GuardsSameB (exec_stmt 510 wb es) es.
 Proof. apply component_preserves_guards_b. reflexivity. Qed.
 Lemma ex_guards_b es : GuardsSameB (exec_stmt 510 ex es) es.
 Proof. apply component_preserves_guards_b. reflexivity. Qed.
 Lemma override_projection_b es :
   norm 2 (read_signal (blocking_state (exec_stmt 510 override es)) 1109%nat) =
   if norm 1 (read_signal (blocking_state es) 1058%nat) =? 0
   then norm 2 (read_signal (blocking_state es) 1109%nat) else 0.
 Proof.
   change override with (SIf (EVar 1 1058%nat)
     (SSeq [SAssign false (EConst 2 1) (LVar 2 1108%nat);
            SAssign false (EConst 2 0) (LVar 2 1109%nat)])
     (SIf (EVar 1 1062%nat) (SSeq [SAssign false (EConst 2 1) (LVar 2 1110%nat)]) SSkip)).
   rewrite exec_if. cbn [eval_expr].
   destruct (norm 1 (read_signal (blocking_state es) 1058%nat) =? 0).
   - rewrite (proj1 (exec_stmt_preserves_unwritten_root 509
       (SIf (EVar 1 1062%nat) (SSeq [SAssign false (EConst 2 1) (LVar 2 1110%nat)]) SSkip)
       1109%nat es ltac:(cbn; intuition discriminate))). reflexivity.
   - rewrite exec_sequence, fold_two.
     change (norm 2 (read_signal (write_signal
       (write_signal (blocking_state es) 1108%nat
         (write_slice (read_signal (blocking_state es) 1108%nat) 0 2 1))
       1109%nat (write_slice (read_signal (write_signal (blocking_state es) 1108%nat
         (write_slice (read_signal (blocking_state es) 1108%nat) 0 2 1)) 1109%nat) 0 2 0))
       1109%nat) = 0).
     rewrite read_signal_write_same, norm_write_low. reflexivity.
 Qed.
 Definition wb_choice_b s := if norm 1 (read_signal s 1106%nat) =? 0 then 0
   else if norm 1 (read_signal s 1115%nat) =? 0 then 0 else 2.
 Definition ex_choice_b s := if norm 1 (read_signal s 1107%nat) =? 0 then wb_choice_b s
   else if norm 1 (read_signal s 1118%nat) =? 0 then wb_choice_b s else 1.
 Definition control_choice_b s := if norm 1 (read_signal s 1058%nat) =? 0
   then ex_choice_b s else 0.
 #[local] Opaque initial wb ex override.
 Theorem actual_controller_priority_b es :
   norm 2 (read_signal (blocking_state (exec_stmt 512 (process_body process_1706) es)) 1109%nat) =
   control_choice_b (blocking_state es).
 Proof.
   rewrite shape, exec_sequence, fold_one, exec_sequence, fold_left_app.
   change (norm 2 (read_signal (blocking_state
     (fold_left (fun es st => exec_stmt 510 st es) [wb;ex;override]
       (exec_stmt 511 initial es))) 1109%nat) = control_choice_b (blocking_state es)).
   rewrite fold_cons, fold_two, override_projection_b.
   pose proof (initial_guards_b es) as H0.
   pose proof (wb_guards_b (exec_stmt 511 initial es)) as Hw.
   pose proof (ex_guards_b (exec_stmt 510 wb (exec_stmt 511 initial es))) as He.
   unfold control_choice_b. rewrite (He 1058%nat ltac:(simpl; tauto)),
     (Hw 1058%nat ltac:(simpl; tauto)), (H0 1058%nat ltac:(simpl; tauto)).
   destruct (norm 1 (read_signal (blocking_state es) 1058%nat) =? 0); [|reflexivity].
   rewrite ex_shape, group_projection_b by discriminate. unfold group_value_b, ex_choice_b.
   rewrite (Hw 1107%nat ltac:(simpl; tauto)), (H0 1107%nat ltac:(simpl; tauto)),
     (Hw 1118%nat ltac:(simpl; tauto)), (H0 1118%nat ltac:(simpl; tauto)).
   assert (Hwb : norm 2 (read_signal (blocking_state
     (exec_stmt 510 wb (exec_stmt 511 initial es))) 1109%nat) = wb_choice_b (blocking_state es)).
   { rewrite wb_shape, group_projection_b by discriminate. unfold group_value_b, wb_choice_b.
     rewrite (H0 1106%nat ltac:(simpl; tauto)), (H0 1115%nat ltac:(simpl; tauto)), initial_zero_b.
     reflexivity. }
   rewrite Hwb. reflexivity.
 Qed.
 Theorem actual_controller_run_priority_b s :
   norm 2 (read_signal (run_process cv32e40p_program s process_1706) 1109%nat) =
   control_choice_b s.
 Proof.
   rewrite blocking_run_process by reflexivity. apply actual_controller_priority_b.
 Qed.
 Print Assumptions actual_controller_run_priority_b.
End CV32E40PForwardControlB.
