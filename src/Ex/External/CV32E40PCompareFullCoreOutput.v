(** Actual FullCore comparison-bit and final ALU-output connection. The
    boolean inputs are observed packed comparator bits, not ISA results. *)
From Coq Require Import ZArith Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVBitSlice Lang.ExtendedSVCombCut
  Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiOperandCone
  Ex.External.CV32E40PAddiFullCoreALU Ex.External.CV32E40PCompareControlCone
  Ex.External.CV32E40PCompareCombineCone Ex.External.CV32E40PCompareBooleanCombine
  Ex.External.CV32E40PCompareByteArithmetic Ex.External.CV32E40PScalarMuxSlt
  Ex.External.CV32E40PScalarMuxSltu Ex.External.CV32E40PAddiIDEXAccept.
Import ExtendedSV ExtendedSVBitSlice ExtendedSVCombCut CV32E40PExtendedAST
  CV32E40PAddiOperandCone CV32E40PCompareControlCone CV32E40PCompareCombineCone
  CV32E40PCompareBooleanCombine CV32E40PCompareByteArithmetic
  CV32E40PScalarMuxSlt CV32E40PScalarMuxSltu CV32E40PAddiIDEXAccept.
Local Open Scope Z_scope.
Module CV32E40PCompareFullCoreOutput.

Definition observed_bit s root off := Z.eqb (read_slice (read_signal s root) off 1) 1.
Lemma observed_bit_value s root off : 0 <= off ->
  read_slice (read_signal s root) off 1 = boolz (observed_bit s root off).
Proof.
  intros H. unfold observed_bit. pose proof (single_bit_range (read_signal s root) off H).
  destruct (Z.eqb (read_slice (read_signal s root) off 1) 1) eqn:HE;
    [apply Z.eqb_eq in HE|apply Z.eqb_neq in HE]; cbn [boolz]; lia.
Qed.
Definition observed_equal s := andb
  (andb (andb (observed_bit s 1353%nat 3) (observed_bit s 1353%nat 2))
    (observed_bit s 1353%nat 1)) (observed_bit s 1353%nat 0).
Definition observed_greater s := orb (observed_bit s 1354%nat 3)
  (andb (observed_bit s 1353%nat 3) (orb (observed_bit s 1354%nat 2)
    (andb (observed_bit s 1353%nat 2) (orb (observed_bit s 1354%nat 1)
      (andb (observed_bit s 1353%nat 1) (observed_bit s 1354%nat 0)))))).

Local Opaque before_process comb_round run_process.
Ltac project n p root := CV32E40PAddiFullCoreALU.project n p root.
Ltac final_inputs := CV32E40PAddiFullCoreALU.final_inputs.
Lemma fullcore_signed_mode s : norm 7 (read_signal (round s) 1303%nat) = 2 ->
  norm 2 (read_signal (round s) 1307%nat) = 0 ->
  norm 4 (read_signal (round s) 1352%nat) = 8.
Proof.
  intros HO HV. project 586 process_586 1352%nat.
  apply actual_signed_compare_mode; final_inputs; assumption.
Qed.
Lemma fullcore_unsigned_mode s : norm 7 (read_signal (round s) 1303%nat) = 3 ->
  norm 4 (read_signal (round s) 1352%nat) = 0.
Proof.
  intros HO. project 586 process_586 1352%nat.
  apply actual_unsigned_compare_mode. final_inputs. exact HO.
Qed.
Lemma fullcore_less_result s op : op = 2 \/ op = 3 ->
  norm 7 (read_signal (round s) 1303%nat) = op ->
  norm 4 (read_signal (round s) 1358%nat) =
    norm 4 (Z.lnot (Z.lor (norm 4 (read_signal (round s) 1351%nat))
      (norm 4 (read_signal (round s) 1350%nat)))).
Proof.
  intros HC HO. project 592 process_592 1358%nat.
  rewrite (actual_less_than_select (before_process cv32e40p_program 592 s)
    op HC ltac:(final_inputs; exact HO)).
  final_inputs. reflexivity.
Qed.
Lemma fullcore_compare_bit s : norm 1 (read_signal (round s) 1315%nat) =
  read_slice (read_signal (round s) 1358%nat) 3 1.
Proof.
  project 593 process_593 1315%nat. rewrite actual_compare_bit.
  final_inputs. reflexivity.
Qed.
Lemma fullcore_compare_mux s op : op = 2 \/ op = 3 ->
  norm 7 (read_signal (round s) 1303%nat) = op ->
  norm 32 (read_signal (round s) 1314%nat) = norm 32 (norm 1 (read_signal (round s) 1315%nat)).
Proof.
  intros HC HO. project 1896 process_1896 1314%nat.
  destruct HC as [->| ->];
    [rewrite actual_mux_slt|rewrite actual_mux_sltu]; final_inputs; auto.
Qed.

Theorem fullcore_scalar_compare_boolean s op : op = 2 \/ op = 3 ->
  norm 7 (read_signal (round s) 1303%nat) = op ->
  norm 2 (read_signal (round s) 1307%nat) = 0 ->
  norm 32 (read_signal (round s) 1314%nat) =
    boolz (negb (orb (observed_greater (round s)) (observed_equal (round s)))).
Proof.
  intros HC HO HV. rewrite fullcore_compare_mux with (op:=op) by assumption.
  rewrite fullcore_compare_bit.
  rewrite <- (Ex.External.CV32E40PAddiAdderBits.CV32E40PAddiAdderBits.slice_norm
    (read_signal (round s) 1358%nat) 4 3 1 ltac:(lia) ltac:(lia) ltac:(lia)).
  rewrite fullcore_less_result with (op:=op) by assumption.
  destruct (fullcore_scalar_combine s HV) as [HE HG]. rewrite HE,HG.
  rewrite equal_expression_boolean with
    (e3:=observed_bit (round s) 1353%nat 3) (e2:=observed_bit (round s) 1353%nat 2)
    (e1:=observed_bit (round s) 1353%nat 1) (e0:=observed_bit (round s) 1353%nat 0)
    by (apply observed_bit_value; lia).
  rewrite greater_expression_boolean with
    (e3:=observed_bit (round s) 1353%nat 3) (e2:=observed_bit (round s) 1353%nat 2)
    (e1:=observed_bit (round s) 1353%nat 1)
    (g3:=observed_bit (round s) 1354%nat 3) (g2:=observed_bit (round s) 1354%nat 2)
    (g1:=observed_bit (round s) 1354%nat 1) (g0:=observed_bit (round s) 1354%nat 0)
    by (apply observed_bit_value; lia).
  change (norm 32 (read_slice (norm 4 (Z.lnot
    (Z.lor (repeated_bit (observed_greater (round s)))
      (repeated_bit (observed_equal (round s)))))) 3 1) =
    boolz (negb (orb (observed_greater (round s)) (observed_equal (round s))))).
  rewrite less_bit_boolean. destruct (negb (orb (observed_greater (round s))
    (observed_equal (round s)))); reflexivity.
Qed.
Print Assumptions fullcore_scalar_compare_boolean.
End CV32E40PCompareFullCoreOutput.
