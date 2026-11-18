(** Exact ordered FullCore connection, not an alternative arithmetic DUT. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVCombCut
  Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiAdder
  Ex.External.CV32E40PAddiAdderResult Ex.External.CV32E40PAddiAdderInputs
  Ex.External.CV32E40PAddiCarryCone Ex.External.CV32E40PAddiOperandCone.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVCombCut CV32E40PExtendedAST
  CV32E40PAddiAdder CV32E40PAddiAdderResult CV32E40PAddiAdderInputs
  CV32E40PAddiCarryCone CV32E40PAddiOperandCone.
Local Open Scope Z_scope.
Module CV32E40PAddiFullCoreAdder.
  Definition inputs s := run_process cv32e40p_program
    (run_process cv32e40p_program (run_process cv32e40p_program s process_621) process_622) process_623.
  Definition adder_cone s := carry_cone (inputs s).
  Ltac keep_inputs := repeat match goal with
    | |- context [read_signal (run_process cv32e40p_program ?s ?p) ?root] =>
      rewrite (keep root p s ltac:(reflexivity))
    end.
  Lemma input_controls s :
    norm 7 (read_signal s 1303%nat) = 24 -> norm 1 (read_signal s 1312%nat) = 0 ->
    norm 2 (read_signal s 1307%nat) = 0 ->
    norm 1 (read_signal (inputs s) 1327%nat) = 0 /\
    norm 7 (read_signal (inputs s) 1303%nat) = 24 /\
    norm 2 (read_signal (inputs s) 1307%nat) = 0.
  Proof.
    intros Hop Hsub Hvec. unfold inputs.
    split; [|split]; keep_inputs; try assumption. apply actual_negate; assumption.
  Qed.
  Lemma input_data s :
    norm 7 (read_signal s 1303%nat) = 24 -> norm 1 (read_signal s 1312%nat) = 0 ->
    norm 32 (read_signal (inputs s) 1328%nat) = norm 32 (read_signal s 1304%nat) /\
    norm 32 (read_signal (inputs s) 1329%nat) = norm 32 (read_signal s 1305%nat).
  Proof.
    intros Hop Hsub. unfold inputs. split.
    - rewrite (keep 1328%nat process_623 _ eq_refl).
      rewrite actual_operand_a; keep_inputs; assumption || reflexivity.
    - rewrite actual_operand_b.
      + keep_inputs. reflexivity.
      + keep_inputs. apply actual_negate; assumption.
  Qed.
  Theorem actual_adder_cone s :
    norm 7 (read_signal s 1303%nat) = 24 -> norm 1 (read_signal s 1312%nat) = 0 ->
    norm 2 (read_signal s 1307%nat) = 0 ->
    norm 32 (read_signal (adder_cone s) 1332%nat) =
      norm 32 (read_signal s 1304%nat + read_signal s 1305%nat).
  Proof.
    intros Hop Hsub Hvec. destruct (input_controls s Hop Hsub Hvec) as (Hn&Ho&Hv).
    destruct (input_data s Hop Hsub) as [Ha Hb]. unfold adder_cone.
    rewrite actual_scalar_carry_cone by assumption.
    assert (Hsum : forall a b, norm 32 (a+b) = norm 32 (norm 32 a+norm 32 b)).
    { intros. rewrite !norm_mod. apply Z.add_mod. apply Z.pow_nonzero; lia. }
    rewrite Hsum, Ha, Hb. symmetry. apply Hsum.
  Qed.
  Lemma adder_suffix : avoids_root 1332%nat
    (filter is_comb (skipn 627 (processes cv32e40p_program))) = true.
  Proof. vm_compute. reflexivity. Qed.
  #[local] Opaque before_process comb_round run_process.
  Theorem fullcore_scalar_adder s :
    norm 7 (read_signal (cut 621 s) 1303%nat) = 24 ->
    norm 1 (read_signal (cut 621 s) 1312%nat) = 0 ->
    norm 2 (read_signal (cut 621 s) 1307%nat) = 0 ->
    norm 32 (read_signal (comb_round cv32e40p_program s) 1332%nat) =
      norm 32 (read_signal (cut 621 s) 1304%nat + read_signal (cut 621 s) 1305%nat).
  Proof.
    intros Hop Hsub Hvec.
    rewrite (comb_cut_root cv32e40p_program 626 process_626 s 1332%nat eq_refl eq_refl adder_suffix).
    change (norm 32 (read_signal (run_process cv32e40p_program (cut 626 s) process_626) 1332%nat) =
      norm 32 (read_signal (cut 621 s) 1304%nat + read_signal (cut 621 s) 1305%nat)).
    rewrite (cut_next 625 process_625 s eq_refl eq_refl),
      (cut_next 624 process_624 s eq_refl eq_refl),
      (cut_next 623 process_623 s eq_refl eq_refl),
      (cut_next 622 process_622 s eq_refl eq_refl),
      (cut_next 621 process_621 s eq_refl eq_refl).
    exact (actual_adder_cone (cut 621 s) Hop Hsub Hvec).
  Qed.
  Print Assumptions fullcore_scalar_adder.
End CV32E40PAddiFullCoreAdder.
