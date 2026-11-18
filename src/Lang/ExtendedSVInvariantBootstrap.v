(** Lift a phase invariant using the checked full RTL settling certificate.
    Stable sampling is derived, not demanded at every step by the caller. *)
From Coq Require Import List Bool PeanoNat.
Require Import Lang.ExtendedSV Lang.ExtendedSVScalarHistory
 Lang.ExtendedSVDependencyCatalog Lang.ExtendedSVBoundedCatalogPhase Lang.ExtendedSVBootstrap.
Import ExtendedSV ExtendedSVScalarHistory ExtendedSVDependencyCatalog
 ExtendedSVBoundedCatalogPhase.
Module ExtendedSVInvariantBootstrap.
Theorem checked_history p catalog (certificate:BoundedCatalogCertificate p catalog)
 (Inv:State->Prop) (Boundary Allowed:Event->Prop)
 (inputs:forall ev,Allowed ev ->CatalogEvent p catalog ev /\Boundary ev)
 (step:forall seed ev pre,Boundary ev ->CombLFP p seed(phase_driven_state p ev pre) ->
   Inv pre ->Inv(PhaseSemantics p ev pre)) events :
 Forall Allowed events ->forall pre,
 CatalogShape p catalog pre ->Inv pre ->Inv(phase_run p events pre).
Proof.
 intro HE;induction HE as[|ev rest HE HT IH];intros pre HS HI;[exact HI|].
 cbn [phase_run].
 destruct(inputs ev HE)as[HC HB].
 destruct(ExtendedSVBootstrap.catalog_phase_evidence p catalog certificate ev pre HC HS)
   as[HL [HP HS']].
 apply IH;[exact HS'|].
 exact(step _ ev pre HB HL HI).
Qed.
End ExtendedSVInvariantBootstrap.
Print Assumptions ExtendedSVInvariantBootstrap.checked_history.
