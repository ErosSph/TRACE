(** Preserve a relation on the real phase run using explicit per-prefix inputs.
    The inputs are proof obligations, not part of the external event domain. *)
From Coq Require Import List.
Require Import Lang.ExtendedSV Lang.ExtendedSVScalarHistory Lang.ExtendedSVRuntimeHistory
 Lang.ExtendedSVBootstrap Lang.ExtendedSVBoundedCatalogPhase.
Import ListNotations ExtendedSV ExtendedSVScalarHistory ExtendedSVRuntimeHistory ExtendedSVBoundedCatalogPhase.
Module ExtendedSVRuntimeRelation.
Definition InputsAlong p Ghost (advance:Event->State->Ghost->unit->Ghost)
 (Input:Event->State->Ghost->Prop) events pre ghost:=forall left ev right,
 events=left++ev::right ->Input ev(phase_run p left pre)(replay p Ghost advance left pre ghost).

Theorem preserves p catalog(certificate:BoundedCatalogCertificate p catalog)
 Ghost advance (R:State->Ghost->Prop)(Input:Event->State->Ghost->Prop)(Allowed:Event->Prop)
 (input:forall ev,Allowed ev ->CatalogEvent p catalog ev)
 (step:forall seed ev pre ghost,Allowed ev ->CombLFP p seed(phase_driven_state p ev pre) ->
  R pre ghost ->Input ev pre ghost ->R(PhaseSemantics p ev pre)(advance ev pre ghost tt)) events:
 Forall Allowed events ->forall pre ghost,CatalogShape p catalog pre ->R pre ghost ->
 InputsAlong p Ghost advance Input events pre ghost ->
 R(phase_run p events pre)(replay p Ghost advance events pre ghost).
Proof.
 intro HE;induction HE as[|ev rest HE HRest IH];intros pre ghost HS HR HI;[exact HR|].
 destruct(ExtendedSVBootstrap.catalog_phase_evidence p catalog certificate ev pre(input ev HE)HS)as[HL[HX HSNext]].
 cbn[phase_run replay];apply IH;[exact HSNext| |].
 - exact(step _ ev pre ghost HE HL HR(HI [] ev rest eq_refl)).
 - intros left e right HP;exact(HI(ev::left)e right ltac:(cbn;now rewrite HP)).
Qed.
End ExtendedSVRuntimeRelation.
Print Assumptions ExtendedSVRuntimeRelation.preserves.
