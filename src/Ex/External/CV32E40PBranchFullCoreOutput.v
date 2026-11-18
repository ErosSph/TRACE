(** Real FullCore branch comparison output, through original processes
    586/591/592/593.  Inputs below are observed comparator bits, not ISA oracles. *)
From Coq Require Import ZArith Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVBitSlice Lang.ExtendedSVCombCut
  Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiOperandCone
  Ex.External.CV32E40PAddiFullCoreALU Ex.External.CV32E40PBranchCompareControl
  Ex.External.CV32E40PCompareFullCoreOutput Ex.External.CV32E40PCompareCombineCone
  Ex.External.CV32E40PCompareBooleanCombine Ex.External.CV32E40PCompareByteArithmetic
  Ex.External.CV32E40PAddiAdderBits Ex.External.CV32E40PAddiIDEXAccept.
Import ExtendedSV ExtendedSVBitSlice ExtendedSVCombCut CV32E40PExtendedAST
  CV32E40PAddiOperandCone CV32E40PBranchCompareControl CV32E40PCompareFullCoreOutput
  CV32E40PCompareCombineCone CV32E40PCompareBooleanCombine CV32E40PCompareByteArithmetic
  CV32E40PAddiAdderBits CV32E40PAddiIDEXAccept.
Local Open Scope Z_scope.
Module CV32E40PBranchFullCoreOutput.

Definition branch_boolean (op : Z) (e g : bool) : bool :=
  if op =? 12 then e else if op =? 13 then negb e else
  if (op =? 10) || (op =? 11) then orb g e else negb (orb g e).

Lemma branch_vector_boolean op e g : BranchALU op ->
  read_slice (branch_compare_vector op (repeated_bit e) (repeated_bit g)) 3 1 =
    boolz (branch_boolean op e g).
Proof.
  intros HC. destruct HC as [->| [->| [->| [->| [->| ->]]]]];
    destruct e,g; reflexivity.
Qed.

Local Opaque before_process comb_round run_process.
Ltac project n p root := CV32E40PAddiFullCoreALU.project n p root.
Ltac final_inputs := CV32E40PAddiFullCoreALU.final_inputs.

Lemma fullcore_branch_signed_mode s op : op = 0 \/ op = 10 ->
  norm 7 (read_signal (round s) 1303%nat) = op ->
  norm 2 (read_signal (round s) 1307%nat) = 0 ->
  norm 4 (read_signal (round s) 1352%nat) = 8.
Proof.
  intros HC HO HV. project 586 process_586 1352%nat.
  apply branch_signed_mode with (op:=op); try exact HC; final_inputs; assumption.
Qed.
Lemma fullcore_branch_unsigned_mode s op :
  op = 1 \/ op = 11 \/ op = 12 \/ op = 13 ->
  norm 7 (read_signal (round s) 1303%nat) = op ->
  norm 4 (read_signal (round s) 1352%nat) = 0.
Proof.
  intros HC HO. project 586 process_586 1352%nat.
  apply branch_unsigned_mode with (op:=op); try exact HC; final_inputs; exact HO.
Qed.
Lemma fullcore_branch_result s op : BranchALU op ->
  norm 7 (read_signal (round s) 1303%nat) = op ->
  norm 4 (read_signal (round s) 1358%nat) =
    branch_compare_vector op (norm 4 (read_signal (round s) 1350%nat))
      (norm 4 (read_signal (round s) 1351%nat)).
Proof.
  intros HC HO. project 592 process_592 1358%nat.
  rewrite (branch_result_select (before_process cv32e40p_program 592 s)
    op HC ltac:(final_inputs; exact HO)). final_inputs. reflexivity.
Qed.

Theorem fullcore_scalar_branch_boolean s op : BranchALU op ->
  norm 7 (read_signal (round s) 1303%nat) = op ->
  norm 2 (read_signal (round s) 1307%nat) = 0 ->
  norm 1 (read_signal (round s) 1315%nat) =
    boolz (branch_boolean op (observed_equal (round s)) (observed_greater (round s))).
Proof.
  intros HC HO HV. rewrite fullcore_compare_bit.
  rewrite <- (slice_norm (read_signal (round s) 1358%nat) 4 3 1
    ltac:(lia) ltac:(lia) ltac:(lia)).
  rewrite fullcore_branch_result with (op:=op) by assumption.
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
  apply branch_vector_boolean. exact HC.
Qed.
Print Assumptions fullcore_branch_signed_mode.
Print Assumptions fullcore_branch_unsigned_mode.
Print Assumptions fullcore_scalar_branch_boolean.
End CV32E40PBranchFullCoreOutput.
