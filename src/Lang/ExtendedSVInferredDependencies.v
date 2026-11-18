(** Check external-only dependencies for actual definitely-assigned blocking
    producers. Failed checks are explicitly not certificates. *)
From Coq Require Import List Bool PeanoNat.
Require Import Lang.ExtendedSV Lang.ExtendedSVExprAgreement Lang.ExtendedSVKnownInputs
 Lang.ExtendedSVInferredProducerCertificate Lang.ExtendedSVBlocking.
Import ExtendedSV ExtendedSVExprAgreement ExtendedSVKnownInputs
 ExtendedSVInferredProducerCertificate ExtendedSVBlocking ListNotations.
Module ExtendedSVInferredDependencies.
Fixpoint statement_inputs st:=match st with
 |SSkip=>[]|SAssign _ e _=>expr_inputs e
 |SSeq xs=>flat_map statement_inputs xs
 |SIf g a b=>expr_inputs g++statement_inputs a++statement_inputs b
 |SCase e arms=>expr_inputs e++flat_map(fun arm=>
  (match fst arm with None=>[]|Some key=>expr_inputs key end)++statement_inputs(snd arm))arms end.
Definition external_inputs proc:=filter(fun wr=>negb(existsb(fun out=>Nat.eqb(snd wr)(snd out))
 (inferred_outputs(process_body proc))))(statement_inputs(process_body proc)).
Definition summaryb p proc:=blocking_onlyb(process_body proc)&&
 match infer_known(statement_fuel p)(external_inputs proc)(process_body proc)with
 |Some output=>containsb output(inferred_outputs(process_body proc))|None=>false end.
Theorem checked_external_dependency p proc : summaryb p proc=true->forall s t,
 InputsAgree s t(external_inputs proc)->
 InputsAgree(run_process p s proc)(run_process p t proc)(inferred_outputs(process_body proc)).
Proof.
 unfold summaryb. intro H. apply andb_true_iff in H as[HB HC].
 destruct(infer_known(statement_fuel p)(external_inputs proc)(process_body proc))as[output|]eqn:HE;[|discriminate].
 intros s t HA. eapply contains_agree;[exact HC|]. now apply actual_known_process with(known:=external_inputs proc).
Qed.
Print Assumptions checked_external_dependency.
End ExtendedSVInferredDependencies.
