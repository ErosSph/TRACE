(** Priority of the real blocking forwarding controller: EX overrides WB;
    misaligned access overrides both.  Does not assume architectural equality
    of the forwarded data and does not claim reset-reachable validity. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVBlocking.
Require Import Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiOperands.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVBlocking
  CV32E40PExtendedAST CV32E40PAddiOperands
  CV32E40PAddiDecoder.CV32E40PAddiDecoder.
Local Open Scope Z_scope.
Module CV32E40PAddiForwardControl.
  Definition items := match process_body process_1706 with
    | SSeq [SSeq xs] => xs | _ => [] end.
  Definition initial := SSeq (firstn 3 items).
  Definition wb := nth 3 items SSkip.
  Definition ex := nth 4 items SSkip.
  Definition override := nth 5 items SSkip.
  Lemma shape : process_body process_1706 =
    SSeq [SSeq (firstn 3 items ++ [wb; ex; override])].
  Proof. reflexivity. Qed.
  Lemma exec_if fuel g yes no es :
    exec_stmt (S fuel) (SIf g yes no) es =
    if eval_expr (blocking_state es) g =? 0
    then exec_stmt fuel no es else exec_stmt fuel yes es.
  Proof. cbn [exec_stmt]. destruct (eval_expr (blocking_state es) g =? 0); reflexivity. Qed.
  Definition forward_group en a b c value := SIf (EVar 1 en)
    (SSeq [SIf (EVar 1 a) (SAssign false (EConst 2 value) (LVar 2 1108%nat)) SSkip;
           SIf (EVar 1 b) (SAssign false (EConst 2 value) (LVar 2 1109%nat)) SSkip;
           SIf (EVar 1 c) (SAssign false (EConst 2 value) (LVar 2 1110%nat)) SSkip]) SSkip.
  Lemma wb_shape : wb = forward_group 1106%nat 1114%nat 1115%nat 1116%nat 2.
  Proof. reflexivity. Qed.
  Lemma ex_shape : ex = forward_group 1107%nat 1117%nat 1118%nat 1119%nat 1.
  Proof. reflexivity. Qed.
  Definition group_value es en a value :=
    if norm 1 (read_signal (blocking_state es) en) =? 0
    then norm 2 (read_signal (blocking_state es) 1108%nat)
    else if norm 1 (read_signal (blocking_state es) a) =? 0
    then norm 2 (read_signal (blocking_state es) 1108%nat) else norm 2 value.
  Lemma group_projection es en a b c value :
    norm 2 (read_signal (blocking_state (exec_stmt 510 (forward_group en a b c value) es)) 1108%nat) =
    group_value es en a value.
  Proof.
    unfold forward_group, group_value. rewrite exec_if. cbn [eval_expr].
    destruct (norm 1 (read_signal (blocking_state es) en) =? 0) eqn:Hen.
    - reflexivity.
    - rewrite exec_sequence, fold_cons, fold_two.
      rewrite (proj1 (exec_stmt_preserves_unwritten_root 508
        (SIf (EVar 1 c) (SAssign false (EConst 2 value) (LVar 2 1110%nat)) SSkip)
        1108%nat _ ltac:(cbn; intuition discriminate))).
      rewrite (proj1 (exec_stmt_preserves_unwritten_root 508
        (SIf (EVar 1 b) (SAssign false (EConst 2 value) (LVar 2 1109%nat)) SSkip)
        1108%nat _ ltac:(cbn; intuition discriminate))).
      rewrite exec_if. cbn [eval_expr].
      destruct (norm 1 (read_signal (blocking_state es) a) =? 0) eqn:Ha.
      + reflexivity.
      + change (norm 2 (read_signal
          (write_signal (blocking_state es) 1108%nat
            (write_slice (read_signal (blocking_state es) 1108%nat) 0 2
              (norm 2 (norm 2 value)))) 1108%nat) = norm 2 value).
        rewrite read_signal_write_same, norm_write_low.
        now rewrite !CV32E40PAddiIDEXAccept.CV32E40PAddiIDEXAccept.norm_twice.
  Qed.
  Lemma initial_zero es :
    norm 2 (read_signal (blocking_state (exec_stmt 511 initial es)) 1108%nat) = 0.
  Proof.
    change (norm 2 (read_signal
      (write_signal (write_signal (write_signal (blocking_state es) 1108%nat
        (write_slice (read_signal (blocking_state es) 1108%nat) 0 2 0))
        1109%nat (write_slice (read_signal (write_signal (blocking_state es) 1108%nat
          (write_slice (read_signal (blocking_state es) 1108%nat) 0 2 0)) 1109%nat) 0 2 0))
        1110%nat (write_slice (read_signal (write_signal (write_signal (blocking_state es) 1108%nat
          (write_slice (read_signal (blocking_state es) 1108%nat) 0 2 0)) 1109%nat
          (write_slice (read_signal (write_signal (blocking_state es) 1108%nat
            (write_slice (read_signal (blocking_state es) 1108%nat) 0 2 0)) 1109%nat) 0 2 0)) 1110%nat) 0 2 0))
      1108%nat) = 0).
    rewrite !read_signal_write_other by discriminate.
    rewrite read_signal_write_same, norm_write_low. reflexivity.
  Qed.
  Definition guards : list signal := [1058%nat;1106%nat;1107%nat;1114%nat;1117%nat].
  Definition GuardsSame es es' := forall root, In root guards ->
    read_signal (blocking_state es) root = read_signal (blocking_state es') root.
  Lemma component_preserves_guards fuel st es :
    forallb (fun root => negb (existsb (Nat.eqb root) (stmt_writers st))) guards = true ->
    GuardsSame (exec_stmt fuel st es) es.
  Proof.
    intros H root Hin. apply forallb_forall with (x := root) in H; [|exact Hin].
    apply negb_true_iff in H.
    apply (proj1 (exec_stmt_preserves_unwritten_root fuel st root es
      (unwritten_checked root st H))).
  Qed.
  Lemma initial_guards es : GuardsSame (exec_stmt 511 initial es) es.
  Proof. apply component_preserves_guards. reflexivity. Qed.
  Lemma wb_guards es : GuardsSame (exec_stmt 510 wb es) es.
  Proof. apply component_preserves_guards. reflexivity. Qed.
  Lemma ex_guards es : GuardsSame (exec_stmt 510 ex es) es.
  Proof. apply component_preserves_guards. reflexivity. Qed.
  Lemma override_projection es :
    norm 2 (read_signal (blocking_state (exec_stmt 510 override es)) 1108%nat) =
    if norm 1 (read_signal (blocking_state es) 1058%nat) =? 0
    then norm 2 (read_signal (blocking_state es) 1108%nat) else 1.
  Proof.
    change override with (SIf (EVar 1 1058%nat)
      (SSeq [SAssign false (EConst 2 1) (LVar 2 1108%nat);
             SAssign false (EConst 2 0) (LVar 2 1109%nat)])
      (SIf (EVar 1 1062%nat) (SSeq [SAssign false (EConst 2 1) (LVar 2 1110%nat)]) SSkip)).
    rewrite exec_if. cbn [eval_expr].
    destruct (norm 1 (read_signal (blocking_state es) 1058%nat) =? 0).
    - rewrite (proj1 (exec_stmt_preserves_unwritten_root 509
        (SIf (EVar 1 1062%nat) (SSeq [SAssign false (EConst 2 1) (LVar 2 1110%nat)]) SSkip)
        1108%nat es ltac:(cbn; intuition discriminate))). reflexivity.
    - rewrite exec_sequence, fold_two.
      rewrite (proj1 (exec_stmt_preserves_unwritten_root 508
        (SAssign false (EConst 2 0) (LVar 2 1109%nat)) 1108%nat _ ltac:(cbn; intuition discriminate))).
      change (norm 2 (read_signal (write_signal (blocking_state es) 1108%nat
        (write_slice (read_signal (blocking_state es) 1108%nat) 0 2 1)) 1108%nat) = 1).
      rewrite read_signal_write_same, norm_write_low. reflexivity.
  Qed.
  Definition wb_choice s := if norm 1 (read_signal s 1106%nat) =? 0 then 0
    else if norm 1 (read_signal s 1114%nat) =? 0 then 0 else 2.
  Definition ex_choice s := if norm 1 (read_signal s 1107%nat) =? 0 then wb_choice s
    else if norm 1 (read_signal s 1117%nat) =? 0 then wb_choice s else 1.
  Definition control_choice s := if norm 1 (read_signal s 1058%nat) =? 0
    then ex_choice s else 1.
  #[local] Opaque initial wb ex override.
  Theorem actual_controller_priority es :
    norm 2 (read_signal (blocking_state (exec_stmt 512 (process_body process_1706) es)) 1108%nat) =
    control_choice (blocking_state es).
  Proof.
    rewrite shape, exec_sequence, fold_one, exec_sequence, fold_left_app.
    change (norm 2 (read_signal (blocking_state
      (fold_left (fun es st => exec_stmt 510 st es) [wb;ex;override]
        (exec_stmt 511 initial es))) 1108%nat) = control_choice (blocking_state es)).
    rewrite fold_cons, fold_two, override_projection.
    pose proof (initial_guards es) as H0.
    pose proof (wb_guards (exec_stmt 511 initial es)) as Hw.
    pose proof (ex_guards (exec_stmt 510 wb (exec_stmt 511 initial es))) as He.
    unfold control_choice. rewrite (He 1058%nat ltac:(simpl; tauto)),
      (Hw 1058%nat ltac:(simpl; tauto)), (H0 1058%nat ltac:(simpl; tauto)).
    destruct (norm 1 (read_signal (blocking_state es) 1058%nat) =? 0); [|reflexivity].
    rewrite ex_shape, group_projection. unfold group_value, ex_choice.
    rewrite (Hw 1107%nat ltac:(simpl; tauto)), (H0 1107%nat ltac:(simpl; tauto)),
      (Hw 1117%nat ltac:(simpl; tauto)), (H0 1117%nat ltac:(simpl; tauto)).
    assert (Hwb : norm 2 (read_signal (blocking_state
      (exec_stmt 510 wb (exec_stmt 511 initial es))) 1108%nat) = wb_choice (blocking_state es)).
    { rewrite wb_shape, group_projection. unfold group_value, wb_choice.
      rewrite (H0 1106%nat ltac:(simpl; tauto)), (H0 1114%nat ltac:(simpl; tauto)), initial_zero.
      reflexivity. }
    rewrite Hwb. reflexivity.
  Qed.
  Theorem actual_controller_run_priority s :
    norm 2 (read_signal (run_process cv32e40p_program s process_1706) 1108%nat) = control_choice s.
  Proof.
    rewrite blocking_run_process by reflexivity. apply actual_controller_priority.
  Qed.
  Print Assumptions actual_controller_run_priority.
End CV32E40PAddiForwardControl.
