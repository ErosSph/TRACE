(** Reusable checked syntactic backends. The constant-slice algebra lives in
    a historically Dark-named file, but imports no Dark RTL or CPU Program.
    Keeping that already-checked algebra avoids an unrelated refactoring. *)
From Coq Require Import List.
Require Import Lang.ExtendedSV Lang.ExtendedSVCombRuleRegistry
  Lang.ExtendedSVProducerAssignment Lang.ExtendedSVScalarProducerTransport
  Lang.ExtendedSVInferredProducerCertificate Lang.ExtendedSVForeignUpdateTransport
  Ex.External.DarkRISCV38SliceProducer.
Import ListNotations ExtendedSV ExtendedSVCombRuleRegistry
  ExtendedSVProducerAssignment ExtendedSVScalarProducerTransport
  ExtendedSVInferredProducerCertificate ExtendedSVForeignUpdateTransport
  DarkRISCV38SliceProducer.
Module CPUCombRuleCatalog.

Definition scalar_rule : ProducerRule :=
  {| producer_test := scalar_producerb; producer_rule_sound := scalar_producerb_sound |}.
Definition output_free_rule : ProducerRule :=
  {| producer_test := inferred_producerb;
     producer_rule_sound := fun p proc _ HC => inferred_actual_producer_idempotent p proc HC |}.
Definition constant_slice_rule : ProducerRule :=
  {| producer_test := slice_producerb; producer_rule_sound := slice_producerb_sound |}.
Definition scalar_transport_rule : TransportRule :=
  {| transport_test := scalar_transportb; transport_rule_sound := scalar_transportb_sound |}.
Definition foreign_transport_rule : TransportRule :=
  {| transport_test := later_preservesb;
     transport_rule_sound := fun p first later _ HC =>
       checked_original_later_preserves_fixed p first later HC |}.
Definition constant_slice_transport_rule : TransportRule :=
  {| transport_test := slice_transportb; transport_rule_sound := slice_transportb_sound |}.

Definition producer_rules := [scalar_rule; output_free_rule; constant_slice_rule].
Definition transport_rules :=
  [scalar_transport_rule; foreign_transport_rule; constant_slice_transport_rule].

End CPUCombRuleCatalog.
Print Assumptions CPUCombRuleCatalog.scalar_rule.
Print Assumptions CPUCombRuleCatalog.output_free_rule.
Print Assumptions CPUCombRuleCatalog.constant_slice_rule.
Print Assumptions CPUCombRuleCatalog.scalar_transport_rule.
Print Assumptions CPUCombRuleCatalog.foreign_transport_rule.
Print Assumptions CPUCombRuleCatalog.constant_slice_transport_rule.
