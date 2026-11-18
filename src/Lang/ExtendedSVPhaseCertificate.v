(** Reusable certificate for the ORIGINAL physical phase: both complete-state
    LFPs and source-process priority, for arbitrary events and states. The
    concrete ordered producer certificate must be proved for the actual AST. *)
From Coq Require Import List.
Require Import Lang.ExtendedSV Lang.ExtendedSVCombIdempotence
 Lang.ExtendedSVStaticProcessGroups.
Import ExtendedSV ExtendedSVCombIdempotence ExtendedSVStaticProcessGroups.
Module ExtendedSVPhaseCertificate.
Theorem ordered_certificate_proves_original_phase p :
 lfp_fuel p=1%nat ->
 OrderedProducerCertificate p(filter is_comb(processes p)) ->
 sequential_writers_disjointb p=true -> forall ev pre,
 let driven:=phase_driven_state p ev pre in
 CombLFP p(write_signal pre(changed_signal ev)(new_value ev))driven /\
 CombLFP p(execute_process_order p driven(selected_on_transition p pre driven))
  (PhaseSemantics p ev pre) /\ PhaseIndependentAt p ev pre.
Proof.
 intros HF HC HS ev pre. cbn zeta. split.
 - unfold phase_driven_state.
   exact(certified_original_fuel1_candidate_is_LFP p HF HC _).
 - split.
   + unfold PhaseSemantics,phase_execute_order.
     exact(certified_original_fuel1_candidate_is_LFP p HF HC _).
   + exact(static_sequential_writers_imply_original_phase_independent p ev pre HS).
Qed.
End ExtendedSVPhaseCertificate.
Print Assumptions ExtendedSVPhaseCertificate.ordered_certificate_proves_original_phase.
