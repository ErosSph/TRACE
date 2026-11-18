(** Actual request projection: no FullCore fixed-point assumption. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVCombCut
 Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiOperands
 Ex.External.CV32E40PAddiAdderInputs Ex.External.CV32E40PAddiOperandCone
 Ex.External.CV32E40PAddiDecoderPhase Ex.External.CV32E40PAddiIDEXAccept
 Ex.External.CV32E40PFetchFIFOCount Ex.External.CV32E40PRequestCount
 Ex.External.CV32E40PRequestOutput Ex.External.CV32E40PRequestCycleBalance
 Ex.External.CV32E40PReq39Trace Ex.External.CV32E40PAddiReachability.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVCombCut
 CV32E40PExtendedAST CV32E40PAddiOperands CV32E40PAddiAdderInputs
 CV32E40PAddiOperandCone CV32E40PAddiDecoderPhase CV32E40PAddiIDEXAccept
 CV32E40PFetchFIFOCount CV32E40PRequestCount CV32E40PRequestOutput
 CV32E40PRequestCycleBalance CV32E40PReq39Trace CV32E40PAddiReachability.
Local Open Scope Z_scope.
Module CV32E40PRequestCone.
 Definition request_value enable occupancy outstanding :=
   norm 1 (Z.land enable (norm 1 (boolz
     (Z.gtb (norm 32 2) (norm 32 (norm 32 occupancy + norm 32 outstanding)))))).
 #[local] Opaque norm read_signal write_signal write_slice run_process before_process comb_round.
 Theorem round_request_projection s :
   norm 1 (read_signal (round s) 426%nat) =
   request_value (norm 1 (read_signal s 420%nat))
     (norm 2 (read_signal s 450%nat)) (norm 2 (read_signal s 440%nat)).
 Proof.
   unfold round. rewrite (comb_cut_root cv32e40p_program 1549 process_1549 s 426%nat
     eq_refl eq_refl ltac:(vm_compute; reflexivity)),
     (assign_value _ process_1549 1 426%nat (rhs process_1549) eq_refl).
   unfold rhs. cbn [process_1549 process_body eval_expr]. rewrite !norm_twice.
   rewrite (before_process_keeps_root cv32e40p_program 1549 s 420%nat ltac:(vm_compute; reflexivity)),
     (before_process_keeps_root cv32e40p_program 1549 s 450%nat ltac:(vm_compute; reflexivity)),
     (before_process_keeps_root cv32e40p_program 1549 s 440%nat ltac:(vm_compute; reflexivity)).
   unfold request_value. reflexivity.
 Qed.
 Definition internal_boundary image s := comb_iter cv32e40p_program 7
   (write_signal (environment_state_image image (physical_state s)) 7%nat 1).
 Definition external_boundary image s := comb_iter cv32e40p_program 5
   (environment_input image (physical_state s)).
 #[local] Opaque comb_iter environment_state_image environment_input.
 Lemma internal_request_projection image s : InternalRequest image s =
   request_value (norm 1 (read_signal (internal_boundary image s) 420%nat))
     (norm 2 (read_signal (internal_boundary image s) 450%nat)) (Count s).
 Proof.
   unfold InternalRequest. rewrite phase_driven_last_round.
   fold (internal_boundary image s). fold round.
   rewrite round_request_projection. unfold internal_boundary.
   rewrite (comb_iter_preserves_unwritten_root cv32e40p_program 440%nat) by exact count_unwritten.
   rewrite (read_signal_write_other _ 7%nat 440%nat) by discriminate.
   rewrite environment_count. reflexivity.
 Qed.
 #[local] Transparent environment_input.
 Lemma external_request_projection image s : ExternalRequest image s =
   request_value (norm 1 (read_signal (external_boundary image s) 420%nat))
     (norm 2 (read_signal (external_boundary image s) 450%nat)) (Count s).
 Proof.
   unfold ExternalRequest, request_sample. rewrite (comb_iter_last _ 5).
   fold (external_boundary image s). fold round.
   rewrite round_request_projection. unfold external_boundary.
   rewrite (comb_iter_preserves_unwritten_root cv32e40p_program 440%nat) by exact count_unwritten.
   unfold environment_input, drive. cbn [fold_left fst snd].
   repeat rewrite read_signal_write_other by discriminate. reflexivity.
 Qed.
 Theorem request_alignment_from_two_fields image s :
   norm 1 (read_signal (internal_boundary image s) 420%nat) =
     norm 1 (read_signal (external_boundary image s) 420%nat) ->
   norm 2 (read_signal (internal_boundary image s) 450%nat) =
     norm 2 (read_signal (external_boundary image s) 450%nat) ->
   InternalRequest image s = ExternalRequest image s.
 Proof. intros He Ho. rewrite internal_request_projection, external_request_projection, He, Ho. reflexivity. Qed.
 Theorem enabled_accounting_from_two_fields image s :
   ResetReachable image s -> Count s = Pending s -> Gate image s = 1 ->
   norm 1 (read_signal (internal_boundary image s) 420%nat) =
     norm 1 (read_signal (external_boundary image s) 420%nat) ->
   norm 2 (read_signal (internal_boundary image s) 450%nat) =
     norm 2 (read_signal (external_boundary image s) 450%nat) ->
   Count (advance_retirement image s) = Pending (advance_retirement image s).
 Proof.
   intros Hr HC HG He Ho. apply (proj2 (enabled_count_preservation_iff image s Hr HC HG)).
   now apply request_alignment_from_two_fields.
 Qed.
 Theorem disabled_accounting_iff image s : ResetReachable image s -> Gate image s = 0 ->
   (Count (advance_retirement image s) = Pending (advance_retirement image s) <->
     Count s = ExternalRequest image s).
 Proof.
   intros Hr HG. rewrite (reachable_cycle_count image s Hr), (reachable_cycle_pending image s Hr), HG.
   reflexivity.
 Qed.
 Theorem round_request_ignores_top_clock s clock :
   norm 1 (read_signal (round (write_signal s 7%nat clock)) 426%nat) =
   norm 1 (read_signal (round s) 426%nat).
 Proof. rewrite !round_request_projection. repeat rewrite read_signal_write_other by discriminate. reflexivity. Qed.
 Example request_truth_table :
   map (fun x => request_value (fst x) (fst (snd x)) (snd (snd x)))
     [(0,(0,0));(1,(0,0));(1,(1,0));(1,(0,1));(1,(1,1));(1,(2,0))] =
     [0;1;1;1;0;0].
 Proof. vm_compute; reflexivity. Qed.
 Print Assumptions round_request_projection.
 Print Assumptions request_alignment_from_two_fields.
 Print Assumptions enabled_accounting_from_two_fields.
End CV32E40PRequestCone.
