(** Optional extension: do not change any existing catalog consumer implicitly. *)
From Coq Require Import List.
Require Import Lang.ExtendedSVCombRuleRegistry Lang.ExtendedSVNBAOutputsFreeProducer
 Ex.External.CPUCombRuleCatalog.
Import ListNotations ExtendedSVCombRuleRegistry ExtendedSVNBAOutputsFreeProducer
 CPUCombRuleCatalog.
Module CPUCombNBAExtendedCatalog.
Definition output_independent_nba_rule : ProducerRule :=
 {| producer_test := inferred_nba_producerb;
    producer_rule_sound := fun p proc _ HC => inferred_nba_producerb_sound p proc HC |}.
Definition producer_rules_with_nba := producer_rules ++ [output_independent_nba_rule].
End CPUCombNBAExtendedCatalog.
Print Assumptions CPUCombNBAExtendedCatalog.output_independent_nba_rule.
