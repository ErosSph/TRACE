(** FullCore's actual ADD datapath through the final ALU result port. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVCombCut Ex.Generated.CV32E40PExtendedAST
  Ex.External.CV32E40PAddiOperandCone Ex.External.CV32E40PAddiFullCoreAdder
  Ex.External.CV32E40PAddiALUOutput.
Import ListNotations ExtendedSV ExtendedSVCombCut CV32E40PExtendedAST
  CV32E40PAddiOperandCone CV32E40PAddiFullCoreAdder CV32E40PAddiALUOutput.
Local Open Scope Z_scope.
Module CV32E40PAddiFullCoreALU.
  Definition ScalarADD s :=
    norm 7 (read_signal (round s) 1303%nat) = 24 /\
    norm 2 (read_signal (round s) 1307%nat) = 0 /\
    norm 1 (read_signal (round s) 1312%nat) = 0 /\
    norm 1 (read_signal (round s) 1311%nat) = 0 /\
    norm 5 (read_signal (round s) 1309%nat) = 0.
  #[local] Opaque before_process comb_round run_process.
  Ltac project n p root :=
    let n := eval compute in (Z.to_nat n) in
    unfold round;
    rewrite (comb_cut_root cv32e40p_program n p _ root eq_refl eq_refl ltac:(vm_compute; reflexivity));
    fold round.
  Ltac final_inputs := repeat match goal with
    | |- context [read_signal (before_process cv32e40p_program ?n ?s) ?root] =>
      rewrite <- (cut_final_root cv32e40p_program n s root ltac:(vm_compute; reflexivity)); fold round
    end.
  Lemma round_left s : norm 7 (read_signal (round s) 1303%nat) = 24 ->
    norm 1 (read_signal (round s) 1336%nat) = 0.
  Proof. intros H. project 411 process_411 1336%nat. apply left_disabled. final_inputs. exact H. Qed.
  Lemma round_use s : norm 7 (read_signal (round s) 1303%nat) = 24 ->
    norm 1 (read_signal (round s) 1337%nat) = 1.
  Proof. intros H. project 412 process_412 1337%nat. apply round_selected. final_inputs. exact H. Qed.
  Lemma round_rounding s : norm 7 (read_signal (round s) 1303%nat) = 24 ->
    norm 32 (read_signal (round s) 1334%nat) = 0.
  Proof. intros H. project 578 process_578 1334%nat. apply rounding_zero. final_inputs. exact H. Qed.
  Lemma round_rounded s : norm 7 (read_signal (round s) 1303%nat) = 24 ->
    norm 32 (read_signal (round s) 1335%nat) = norm 32 (read_signal (round s) 1332%nat).
  Proof.
    intros H. project 627 process_627 1335%nat. rewrite round_add_identity; final_inputs.
    - reflexivity.
    - apply round_rounding. exact H.
  Qed.
  Lemma round_shift_operand s : norm 7 (read_signal (round s) 1303%nat) = 24 ->
    norm 32 (read_signal (round s) 1343%nat) = norm 32 (read_signal (round s) 1332%nat).
  Proof.
    intros H. project 628 process_628 1343%nat. rewrite shift_operand; final_inputs.
    - apply round_rounded. exact H.
    - apply round_left. exact H.
    - apply round_use. exact H.
  Qed.
  Lemma round_extended s : norm 7 (read_signal (round s) 1303%nat) = 24 ->
    norm 32 (read_signal (round s) 1348%nat) = norm 32 (read_signal (round s) 1332%nat).
  Proof.
    intros H. project 629 process_629 1348%nat. rewrite extended_low; final_inputs.
    - apply round_shift_operand. exact H.
    - exact H.
  Qed.
  Lemma round_amount_norm s : norm 1 (read_signal (round s) 1311%nat) = 0 ->
    norm 5 (read_signal (round s) 1309%nat) = 0 -> norm 32 (read_signal (round s) 1342%nat) = 0.
  Proof. intros Hc Hb. project 639 process_639 1342%nat. apply shift_amount_zero; final_inputs; assumption. Qed.
  Lemma round_amount s : ScalarADD s -> norm 32 (read_signal (round s) 1341%nat) = 0.
  Proof.
    intros (Ho&Hv&Hs&Hc&Hb). project 1794 process_1794 1341%nat. rewrite shift_amount_select; final_inputs.
    - apply round_amount_norm; assumption.
    - apply round_use. exact Ho.
  Qed.
  Lemma round_right s : ScalarADD s ->
    norm 32 (read_signal (round s) 1345%nat) = norm 32 (read_signal (round s) 1332%nat).
  Proof.
    intros H. destruct H as (Ho&Hv&Hs&Hc&Hb).
    project 1795 process_1795 1345%nat. rewrite shift_identity; final_inputs.
    - apply round_extended. exact Ho.
    - exact Hv.
    - apply round_amount. repeat split; assumption.
  Qed.
  Lemma round_shift_result s : ScalarADD s ->
    norm 32 (read_signal (round s) 1344%nat) = norm 32 (read_signal (round s) 1332%nat).
  Proof.
    intros H. project 1828 process_1828 1344%nat. rewrite result_not_reversed; final_inputs.
    - apply round_right. exact H.
    - apply round_left. exact (proj1 H).
  Qed.
  Theorem fullcore_alu_equals_adder s : ScalarADD s ->
    norm 32 (read_signal (round s) 1314%nat) = norm 32 (read_signal (round s) 1332%nat).
  Proof.
    intros H. project 1896 process_1896 1314%nat. rewrite actual_alu_add_output; final_inputs.
    - apply round_shift_result. exact H.
    - exact (proj1 H).
  Qed.
  Theorem fullcore_alu_scalar_add s : ScalarADD s ->
    norm 32 (read_signal (round s) 1314%nat) =
      norm 32 (read_signal (cut 621 s) 1304%nat + read_signal (cut 621 s) 1305%nat).
  Proof.
    intros H. rewrite fullcore_alu_equals_adder by exact H.
    destruct H as (Ho&Hv&Hs&Hc&Hb). apply fullcore_scalar_adder;
      unfold cut; final_inputs; assumption.
  Qed.
  Print Assumptions fullcore_alu_scalar_add.
End CV32E40PAddiFullCoreALU.
