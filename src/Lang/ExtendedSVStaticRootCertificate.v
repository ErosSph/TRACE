(** Checked static writer metadata with an actual all-state phase consequence. *)
From Coq Require Import List.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice.
Import ExtendedSV ExtendedSVRootProjection ExtendedSVProcessSlice.
Module ExtendedSVStaticRootCertificate.
Record RootCertificate (p : Program) (root : signal) (writers : list Process) : Prop := {
 root_in_bounds : (root < signal_count p)%nat;
 root_comb_unwritten : comb_root_unwrittenb p root = true;
 root_exact_writers : filter (writes_rootb root) (processes p) = writers
}.
Theorem certified_phase_root p root writers :
 RootCertificate p root writers -> forall ev pre,
 changed_signal ev <> root ->
 read_signal (PhaseSemantics p ev pre) root =
 apply_updates_root_value root (read_signal pre root)
   (flat_map (process_updates p (phase_driven_state p ev pre))
     (filter (process_matches_states pre (phase_driven_state p ev pre)) writers)).
Proof.
 intros [HB HC HW] ev pre HE.
 rewrite phase_root_projection by assumption.
 unfold phase_update_chain. rewrite process_slice_sound.
 unfold selected_on_transition. rewrite filter_swap, HW. reflexivity.
Qed.
End ExtendedSVStaticRootCertificate.
Print Assumptions ExtendedSVStaticRootCertificate.certified_phase_root.
