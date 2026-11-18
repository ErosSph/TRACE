(** Actual two-entry fetch FIFO count logic. No replacement CPU transition. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVBlocking Lang.ExtendedSVRootProjection
  Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiOperands
  Ex.External.CV32E40PAddiAdderBits Ex.External.CV32E40PAddiIDEXAccept
  Ex.External.CV32E40PAddiForwardControl Ex.External.CV32E40PAddiDecoder.
Import ListNotations ExtendedSV ExtendedSVBlocking ExtendedSVRootProjection
  CV32E40PExtendedAST CV32E40PAddiOperands CV32E40PAddiAdderBits CV32E40PAddiIDEXAccept
  CV32E40PAddiForwardControl CV32E40PAddiDecoder.
Local Open Scope Z_scope.
Module CV32E40PFetchFIFOCount.
  Definition items := match process_body process_1570 with SSeq [SSeq xs] => xs | _ => [] end.
  Definition initial := SSeq (firstn 6 items).
  Definition push := nth 6 items SSkip.
  Definition pop := nth 7 items SSkip.
  Definition both := nth 8 items SSkip.
  Definition guard st := match st with SIf g _ _ => g | _ => EConst 1 0 end.
  Definition inputs : list signal := [469%nat;465%nat;471%nat;466%nat;479%nat].
  Definition SameInputs es es' := forall root, In root inputs ->
    read_signal (blocking_state es) root = read_signal (blocking_state es') root.
  Lemma keep_inputs fuel st es :
    forallb (fun root => negb (existsb (Nat.eqb root) (stmt_writers st))) inputs = true ->
    SameInputs (exec_stmt fuel st es) es.
  Proof.
    intros H root Hin. apply forallb_forall with (x:=root) in H; [|exact Hin].
    apply negb_true_iff in H. exact (proj1 (exec_stmt_preserves_unwritten_root fuel st root es (unwritten_checked root st H))).
  Qed.
  Lemma initial_inputs es : SameInputs (exec_stmt 511 initial es) es.
  Proof. apply keep_inputs. reflexivity. Qed.
  Lemma push_inputs es : SameInputs (exec_stmt 510 push es) es.
  Proof. apply keep_inputs. reflexivity. Qed.
  Lemma pop_inputs es : SameInputs (exec_stmt 510 pop es) es.
  Proof. apply keep_inputs. reflexivity. Qed.
  Lemma eval_guard_same es es' st : In st [push;pop;both] -> SameInputs es es' ->
    eval_expr (blocking_state es) (guard st) = eval_expr (blocking_state es') (guard st).
  Proof.
    intros [<-|[<-|[<-|[]]]] H; unfold guard, push, pop, both, items;
      cbn [process_1570 process_body nth eval_expr];
      rewrite ?(H 469%nat ltac:(cbn; tauto)), ?(H 465%nat ltac:(cbn; tauto)),
        ?(H 471%nat ltac:(cbn; tauto)), ?(H 466%nat ltac:(cbn; tauto)); reflexivity.
  Qed.
  #[local] Opaque read_signal write_signal norm write_slice.
  Ltac straight := cbv beta iota zeta delta [exec_stmt fold_left blocking_state
    pending_nba emitted_updates eval_expr apply_update resolve_update resolve_lvalue
    update_signal update_offset update_width update_value];
    repeat first [rewrite read_signal_write_same | rewrite read_signal_write_other by discriminate |
                  rewrite norm_write_low | rewrite norm_twice].
  Lemma initial_count es :
    norm 2 (read_signal (blocking_state (exec_stmt 511 initial es)) 478%nat) =
    norm 2 (read_signal (blocking_state es) 479%nat).
  Proof. unfold initial, items. cbn [process_1570 process_body firstn]. straight. reflexivity. Qed.
  Lemma push_count es :
    norm 2 (read_signal (blocking_state (exec_stmt 510 push es)) 478%nat) =
    if eval_expr (blocking_state es) (guard push) =? 0
    then norm 2 (read_signal (blocking_state es) 478%nat)
    else norm 2 (1 + norm 2 (read_signal (blocking_state es) 479%nat)).
  Proof.
    change push with (SIf (guard push) (SSeq (match push with SIf _ (SSeq xs) _ => xs | _ => [] end)) SSkip) at 1.
    rewrite exec_if. destruct (eval_expr (blocking_state es) (guard push) =? 0); [reflexivity|].
    unfold push, items. cbn [process_1570 process_body nth]. straight.
    change (norm 2 1) with 1. reflexivity.
  Qed.
  Lemma pop_count es :
    norm 2 (read_signal (blocking_state (exec_stmt 510 pop es)) 478%nat) =
    if eval_expr (blocking_state es) (guard pop) =? 0
    then norm 2 (read_signal (blocking_state es) 478%nat)
    else norm 2 (norm 2 (read_signal (blocking_state es) 479%nat) - 1).
  Proof.
    change pop with (SIf (guard pop) (SSeq (match pop with SIf _ (SSeq xs) _ => xs | _ => [] end)) SSkip) at 1.
    rewrite exec_if. destruct (eval_expr (blocking_state es) (guard pop) =? 0); [reflexivity|].
    unfold pop, items. cbn [process_1570 process_body nth]. straight.
    change (norm 2 1) with 1. reflexivity.
  Qed.
  Lemma both_count es :
    norm 2 (read_signal (blocking_state (exec_stmt 510 both es)) 478%nat) =
    if eval_expr (blocking_state es) (guard both) =? 0
    then norm 2 (read_signal (blocking_state es) 478%nat)
    else norm 2 (read_signal (blocking_state es) 479%nat).
  Proof.
    change both with (SIf (guard both) (SAssign false (EVar 2 479%nat) (LVar 2 478%nat)) SSkip) at 1.
    rewrite exec_if. destruct (eval_expr (blocking_state es) (guard both) =? 0); [reflexivity|].
    straight. reflexivity.
  Qed.
  #[local] Opaque initial push pop both.
  Lemma actual_shape : process_body process_1570 = SSeq [SSeq (firstn 6 items ++ [push;pop;both])].
  Proof. reflexivity. Qed.
  Definition count_step s :=
    if eval_expr s (guard both) =? 0 then
      if eval_expr s (guard pop) =? 0 then
        if eval_expr s (guard push) =? 0 then norm 2 (read_signal s 479%nat)
        else norm 2 (1 + norm 2 (read_signal s 479%nat))
      else norm 2 (norm 2 (read_signal s 479%nat) - 1)
    else norm 2 (read_signal s 479%nat).
  Theorem actual_count_projection es :
    norm 2 (read_signal (blocking_state (exec_stmt 512 (process_body process_1570) es)) 478%nat) =
      count_step (blocking_state es).
  Proof.
    rewrite actual_shape, exec_sequence, fold_one, exec_sequence, fold_left_app.
    change (norm 2 (read_signal (blocking_state
      (fold_left (fun es st => exec_stmt 510 st es) [push;pop;both]
        (exec_stmt 511 initial es))) 478%nat) = count_step (blocking_state es)).
    rewrite fold_cons, fold_two, both_count, pop_count, push_count, initial_count.
    pose proof (initial_inputs es) as Hi.
    pose proof (push_inputs (exec_stmt 511 initial es)) as Hp.
    pose proof (pop_inputs (exec_stmt 510 push (exec_stmt 511 initial es))) as Ho.
    unfold count_step.
    rewrite (eval_guard_same _ _ both ltac:(simpl; auto) Ho),
      (eval_guard_same _ _ both ltac:(simpl; auto) Hp),
      (eval_guard_same _ _ both ltac:(simpl; auto) Hi),
      (eval_guard_same _ _ pop ltac:(simpl; auto) Hp),
      (eval_guard_same _ _ pop ltac:(simpl; auto) Hi),
      (eval_guard_same _ _ push ltac:(simpl; auto) Hi).
    rewrite (Ho 479%nat ltac:(cbn; tauto)), (Hp 479%nat ltac:(cbn; tauto)),
      (Hi 479%nat ltac:(cbn; tauto)). reflexivity.
  Qed.
  Lemma bit_cases x : norm 1 x = 0 \/ norm 1 x = 1.
  Proof. pose proof (norm_range 1 x). change (0 <= norm 1 x < 2) in H. lia. Qed.
  Definition CountInputs s :=
    0 <= norm 2 (read_signal s 479%nat) <= 2 /\
    norm 1 (read_signal s 465%nat) = (if norm 2 (read_signal s 479%nat) =? 2 then 1 else 0) /\
    norm 1 (read_signal s 466%nat) = (if norm 2 (read_signal s 479%nat) =? 0 then 1 else 0).
  #[local] Transparent push pop both.
  Lemma count_step_bound s : CountInputs s -> 0 <= count_step s <= 2.
  Proof.
    intros [Hc [Hfull Hempty]].
    assert (Hcases : norm 2 (read_signal s 479%nat) = 0 \/
      norm 2 (read_signal s 479%nat) = 1 \/ norm 2 (read_signal s 479%nat) = 2) by lia.
    destruct (bit_cases (read_signal s 469%nat)) as [Hp|Hp];
      destruct (bit_cases (read_signal s 471%nat)) as [Ho|Ho];
      destruct Hcases as [Hn|[Hn|Hn]];
      unfold count_step, guard, push, pop, both, items;
      cbn [process_1570 process_body nth eval_expr];
      repeat first [rewrite Hp | rewrite Ho | rewrite Hfull | rewrite Hempty | rewrite Hn];
      vm_compute; intuition discriminate.
  Qed.
  Theorem actual_count_bounded s : CountInputs s ->
    0 <= norm 2 (read_signal (run_process cv32e40p_program s process_1570) 478%nat) <= 2.
  Proof.
    intros H. rewrite blocking_run_process by reflexivity.
    change (statement_fuel cv32e40p_program) with 512%nat.
    rewrite actual_count_projection. apply count_step_bound. exact H.
  Qed.
  Print Assumptions actual_count_bounded.
End CV32E40PFetchFIFOCount.
