(** The actual packed byte-comparison assignments in the complete ordered
    combinational round. Later writes to other bits are proved disjoint;
    no expected comparison result is supplied as an input assumption. *)
From Coq Require Import ZArith List Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVBlocking Lang.ExtendedSVCombCut
  Lang.ExtendedSVBitSlice Ex.Generated.CV32E40PExtendedAST
  Ex.External.CV32E40PCompareByteCone Ex.External.CV32E40PAddiOperandCone
  Ex.External.CV32E40PAddiFullCoreALU.
Import ListNotations ExtendedSV ExtendedSVBlocking ExtendedSVCombCut
  ExtendedSVBitSlice CV32E40PExtendedAST CV32E40PCompareByteCone
  CV32E40PAddiOperandCone.
Local Open Scope Z_scope.
Module CV32E40PCompareFullCoreBytes.

Lemma assign_bit_frame s proc root total offwidth off e query :
  process_body proc = SAssign false e (LSel 1 (LVar total root) (EConst offwidth off)) ->
  norm offwidth off = off -> 0 <= off -> 0 <= query ->
  (query + 1 <= off \/ off + 1 <= query) ->
  read_slice (read_signal (run_process cv32e40p_program s proc) root) query 1 =
    read_slice (read_signal s root) query 1.
Proof.
  intros HB HO HN HQ HD.
  rewrite blocking_run_process by (rewrite HB; reflexivity).
  change (statement_fuel cv32e40p_program) with 512%nat. rewrite HB.
  cbv beta iota zeta delta [exec_stmt blocking_state apply_update resolve_update
    resolve_lvalue update_signal update_offset update_width update_value].
  cbn [eval_expr]. rewrite HO, Z.add_0_l, read_signal_write_same.
  apply read_slice_write_disjoint; lia.
Qed.

Local Opaque before_process comb_round run_process.
Ltac project n p root := CV32E40PAddiFullCoreALU.project n p root.
Ltac final_inputs := CV32E40PAddiFullCoreALU.final_inputs.
Ltac discard_bit p root off q n :=
  rewrite (assign_bit_frame _ p root 4 2 off (assigned_expr p) q
    eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(lia));
  rewrite (before_process_next cv32e40p_program n _ _ eq_refl eq_refl).

Theorem fullcore_byte_equal s n : (n < 4)%nat ->
  read_slice (read_signal (round s) 1353%nat) (Z.of_nat n) 1 =
    norm 1 (eval_expr (round s) (assigned_expr (eq_process n))).
Proof.
  intros Hn. destruct n as [|[|[|[|n]]]]; try lia.
  all: project 566 process_566 1353%nat.
  - discard_bit process_566 1353%nat 3 0 565%nat.
    discard_bit process_565 1353%nat 2 0 564%nat.
    discard_bit process_564 1353%nat 1 0 563%nat.
    rewrite (actual_byte_equal _ 0 ltac:(lia)).
    cbn [eq_process assigned_expr process_563 process_body eval_expr]. final_inputs. reflexivity.
  - discard_bit process_566 1353%nat 3 1 565%nat.
    discard_bit process_565 1353%nat 2 1 564%nat.
    rewrite (actual_byte_equal _ 1 ltac:(lia)).
    cbn [eq_process assigned_expr process_564 process_body eval_expr]. final_inputs. reflexivity.
  - discard_bit process_566 1353%nat 3 2 565%nat.
    rewrite (actual_byte_equal _ 2 ltac:(lia)).
    cbn [eq_process assigned_expr process_565 process_body eval_expr]. final_inputs. reflexivity.
  - rewrite (actual_byte_equal _ 3 ltac:(lia)).
    cbn [eq_process assigned_expr process_566 process_body eval_expr]. final_inputs. reflexivity.
Qed.

Theorem fullcore_byte_greater s n : (n < 4)%nat ->
  read_slice (read_signal (round s) 1354%nat) (Z.of_nat n) 1 =
    norm 1 (eval_expr (round s) (assigned_expr (greater_process n))).
Proof.
  intros Hn. destruct n as [|[|[|[|n]]]]; try lia.
  all: project 590 process_590 1354%nat.
  - discard_bit process_590 1354%nat 3 0 589%nat.
    discard_bit process_589 1354%nat 2 0 588%nat.
    discard_bit process_588 1354%nat 1 0 587%nat.
    rewrite (actual_byte_greater _ 0 ltac:(lia)).
    cbn [greater_process assigned_expr process_587 process_body eval_expr expr_width].
    final_inputs. reflexivity.
  - discard_bit process_590 1354%nat 3 1 589%nat.
    discard_bit process_589 1354%nat 2 1 588%nat.
    rewrite (actual_byte_greater _ 1 ltac:(lia)).
    cbn [greater_process assigned_expr process_588 process_body eval_expr expr_width].
    final_inputs. reflexivity.
  - discard_bit process_590 1354%nat 3 2 589%nat.
    rewrite (actual_byte_greater _ 2 ltac:(lia)).
    cbn [greater_process assigned_expr process_589 process_body eval_expr expr_width].
    final_inputs. reflexivity.
  - rewrite (actual_byte_greater _ 3 ltac:(lia)).
    cbn [greater_process assigned_expr process_590 process_body eval_expr expr_width].
    final_inputs. reflexivity.
Qed.

Print Assumptions fullcore_byte_equal.
Print Assumptions fullcore_byte_greater.
End CV32E40PCompareFullCoreBytes.
