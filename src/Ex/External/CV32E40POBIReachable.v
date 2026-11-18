(** The existing always-granted environment never accumulates an adapter-held
    request. This is an invariant of original reset reachability, not a new
    premise attached to reachability. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice
 Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PReq39Trace
 Ex.External.CV32E40PReq38Clock Ex.External.CV32E40PAddiReachability
 Ex.External.CV32E40PAddiResetReleaseInvariant Ex.External.CV32E40POBIAdapter.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVProcessSlice
 CV32E40PExtendedAST CV32E40PReq39Trace CV32E40PReq38Clock
 CV32E40PAddiReachability CV32E40PAddiResetReleaseInvariant CV32E40POBIAdapter.
Local Open Scope Z_scope.
Module CV32E40POBIReachable.
 Lemma released_empty : norm 1 (read_signal released 505%nat) = 0.
 Proof. vm_compute; reflexivity. Qed.
 #[local] Opaque lfp_candidate PhaseSemantics norm read_signal.
 Lemma environment_adapter image s :
   read_signal (environment_state_image image s) 505%nat = read_signal (trace_rtl s) 505%nat.
 Proof.
   unfold environment_state_image, obi_ports_image.
   rewrite lfp_candidate_preserves_unwritten_root by exact state_unwritten.
   unfold drive. cbn [fold_left fst snd].
   repeat rewrite read_signal_write_other by discriminate. reflexivity.
 Qed.
 Lemma environment_grant image s : norm 1 (read_signal (environment_state_image image s) 17%nat) = 1.
 Proof.
   unfold environment_state_image, obi_ports_image.
   rewrite lfp_candidate_preserves_unwritten_root by (vm_compute; reflexivity).
   unfold drive. cbn [fold_left fst snd].
   repeat rewrite read_signal_write_other by discriminate.
   rewrite read_signal_write_same. reflexivity.
 Qed.
 Lemma phase_keeps_grant ev pre : changed_signal ev <> 17%nat ->
   read_signal (PhaseSemantics cv32e40p_program ev pre) 17%nat = read_signal pre 17%nat.
 Proof.
   intros H. rewrite input_phase_frame by (vm_compute; reflexivity).
   apply read_signal_write_other. exact H.
 Qed.
 Lemma cycle_empty image s : norm 1 (read_signal (trace_rtl s) 505%nat) = 0 ->
   norm 1 (read_signal (trace_rtl (full_cycle_image image s)) 505%nat) = 0.
 Proof.
   intros H. change (norm 1 (read_signal (settled_state_image image s) 505%nat) = 0).
   unfold settled_state_image. rewrite lfp_candidate_preserves_unwritten_root by exact state_unwritten.
   unfold falling_state_image. apply granted_phase_preserves_empty; try discriminate.
   - unfold rising_state_image. apply granted_phase_preserves_empty; try discriminate.
     + rewrite environment_adapter. exact H.
     + apply environment_grant.
   - unfold rising_state_image. rewrite phase_keeps_grant by discriminate. apply environment_grant.
 Qed.
 Theorem reachable_adapter_empty image s : ResetReachable image s ->
   norm 1 (read_signal (trace_rtl (physical_state s)) 505%nat) = 0.
 Proof.
   intros Hr. induction Hr; [exact released_empty|].
   rewrite advance_physical. apply cycle_empty. exact IHHr.
 Qed.
 Print Assumptions reachable_adapter_empty.
End CV32E40POBIReachable.
