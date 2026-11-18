(** Real forwarding controller -> selector-B wire -> source-B forwarding mux. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVCombCut.
Require Import Ex.Generated.CV32E40PExtendedAST
  Ex.External.CV32E40PAddiOperandCone Ex.External.CV32E40PForwardControlB
  Ex.External.CV32E40PForwardOperandB Ex.External.CV32E40PAddiForwardCone.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVCombCut
  CV32E40PExtendedAST CV32E40PAddiOperandCone CV32E40PForwardControlB
  CV32E40PForwardOperandB CV32E40PAddiForwardCone
  CV32E40PAddiOperands.CV32E40PAddiOperands
  CV32E40PAddiIDEXAccept.CV32E40PAddiIDEXAccept.
Local Open Scope Z_scope.
Module CV32E40PForwardConeB.
 Lemma controller_b_suffix : avoids_root 1109%nat
   (filter is_comb (skipn 1707 (processes cv32e40p_program))) = true.
 Proof. vm_compute. reflexivity. Qed.
 Lemma controller_b_wire_tail : avoids_root 1109%nat
   (filter is_comb (skipn 1743 (processes cv32e40p_program))) = true.
 Proof. vm_compute. reflexivity. Qed.
 Lemma selector_b_suffix : avoids_root 835%nat
   (filter is_comb (skipn 1744 (processes cv32e40p_program))) = true.
 Proof. vm_compute. reflexivity. Qed.
 Lemma selector_b_prefix : avoids_root 835%nat
   (filter is_comb (firstn 1634 (processes cv32e40p_program))) = true.
 Proof. vm_compute. reflexivity. Qed.
 Lemma actual_selector_wire_b s :
   norm 2 (read_signal (run_process cv32e40p_program s process_1743) 835%nat) =
   norm 2 (read_signal s 1109%nat).
 Proof.
   change (norm 2 (read_signal (write_signal s 835%nat
     (write_slice (read_signal s 835%nat) 0 2
       (norm 2 (norm 2 (read_signal s 1109%nat))))) 835%nat) =
     norm 2 (read_signal s 1109%nat)).
   rewrite read_signal_write_same, norm_write_low, !norm_twice. reflexivity.
 Qed.
 #[local] Opaque before_process comb_round.
 Theorem round_selector_b s : norm 2 (read_signal (round s) 835%nat) =
   control_choice_b (cut 1706 s).
 Proof.
   unfold round.
   rewrite (comb_cut_root cv32e40p_program 1743 process_1743 s 835%nat
     eq_refl eq_refl selector_b_suffix), actual_selector_wire_b.
   rewrite <- (cut_final_root cv32e40p_program 1743 s 1109%nat controller_b_wire_tail).
   rewrite (comb_cut_root cv32e40p_program 1706 process_1706 s 1109%nat
     eq_refl eq_refl controller_b_suffix).
   apply actual_controller_run_priority_b.
 Qed.
 Definition selected_source_b choice s :=
   if choice =? 1 then norm 32 (read_signal s 695%nat)
   else if choice =? 2 then norm 32 (read_signal s 691%nat)
   else norm 32 (read_signal s 777%nat).
 Theorem next_round_forward_b s : forward_value_b (cut 1634 (round s)) =
   selected_source_b (control_choice_b (cut 1706 s)) (cut 1634 (round s)).
 Proof.
   unfold forward_value_b, selected_source_b.
   assert (H : norm 2 (read_signal (cut 1634 (round s)) 835%nat) =
     control_choice_b (cut 1706 s)).
   { unfold cut. rewrite before_process_keeps_root by exact selector_b_prefix.
     apply round_selector_b. }
   now rewrite H.
 Qed.
 Definition controlled_source_b ev pre := selected_source_b
   (control_choice_b (cut 1706 (round5 ev pre))) (cut 1634 (round6 ev pre)).
 Theorem actual_forward_input_b_is_controlled ev pre :
   actual_forward_input_b ev pre = controlled_source_b ev pre.
 Proof.
   unfold actual_forward_input_b, controlled_source_b.
   rewrite round6_after_round5. apply next_round_forward_b.
 Qed.
 Print Assumptions actual_forward_input_b_is_controlled.
End CV32E40PForwardConeB.
