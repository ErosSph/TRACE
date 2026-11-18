(** Public original-program assembly. Residuals remain mandatory premises;
    concrete CPUs need not unfold the interpreter to apply these bridges. *)
From Coq Require Import List.
Require Import Lang.ExtendedSV Lang.ExtendedSVCombIdempotence
 Lang.ExtendedSVCombRuleRegistry Lang.ExtendedSVInferredProducerCertificate
 Lang.ExtendedSVForeignUpdateTransport Lang.ExtendedSVStaticProcessGroups
 Lang.ExtendedSVPhaseCertificate.
Import ListNotations ExtendedSV ExtendedSVCombIdempotence
 ExtendedSVCombRuleRegistry ExtendedSVInferredProducerCertificate
 ExtendedSVForeignUpdateTransport ExtendedSVStaticProcessGroups
 ExtendedSVPhaseCertificate.
Module ExtendedSVCombRuleAssembly.

Theorem complete_registry_from_residual producers p order :
 (0<statement_fuel p)%nat ->
 Forall(ProducerIdempotent p)(residual_order producers order)->
 Forall(ProducerIdempotent p)order.
Proof.
 intros HF HR.
 exact(complete_filtered_exception _ (ProducerIdempotent p)
  (producer_accepted producers)order
  (certified_order_sound producers p order HF)HR).
Qed.

Theorem ordered_registry_from_residual producers p order :
 (0<statement_fuel p)%nat ->
 Forall(ProducerIdempotent p)(residual_order producers order)->
 ordered_preservationb order=true -> OrderedProducerCertificate p order.
Proof.
 intros HF HR HP.
 apply idempotent_producers_with_preservation_complete.
 - exact(complete_registry_from_residual producers p order HF HR).
 - exact(ordered_preservationb_sound p order HP).
Qed.

Theorem original_phase_from_registry_residual producers p :
 (0<statement_fuel p)%nat ->
 Forall(ProducerIdempotent p)(residual_order producers(filter is_comb(processes p)))->
 ordered_preservationb(filter is_comb(processes p))=true ->
 lfp_fuel p=1%nat -> sequential_writers_disjointb p=true -> forall ev pre,
 let driven:=phase_driven_state p ev pre in
 CombLFP p(write_signal pre(changed_signal ev)(new_value ev))driven /\
 CombLFP p(execute_process_order p driven(selected_on_transition p pre driven))
  (PhaseSemantics p ev pre) /\ PhaseIndependentAt p ev pre.
Proof.
 intros HF HR HP HL HS ev pre.
 exact(ordered_certificate_proves_original_phase p HL
  (ordered_registry_from_residual producers p _ HF HR HP)HS ev pre).
Qed.
End ExtendedSVCombRuleAssembly.
Print Assumptions ExtendedSVCombRuleAssembly.complete_registry_from_residual.
Print Assumptions ExtendedSVCombRuleAssembly.ordered_registry_from_residual.
Print Assumptions ExtendedSVCombRuleAssembly.original_phase_from_registry_residual.
