(** Construct auxiliary histories along the actual RTL run. No supplied trace
    or supplied labels: the caller supplies only the environment condition. *)
From Coq Require Import List.
Require Import Lang.ExtendedSV Lang.ExtendedSVScalarHistory Lang.ExtendedSVHistoryChain
 Lang.ExtendedSVDependencyCatalog Lang.ExtendedSVBoundedCatalogPhase Lang.ExtendedSVBootstrap.
Import ListNotations ExtendedSV ExtendedSVScalarHistory ExtendedSVHistoryChain
 ExtendedSVDependencyCatalog ExtendedSVBoundedCatalogPhase.
Module ExtendedSVRuntimeHistory.
Lemma phase_run_append p left right pre:
 phase_run p (left ++ right) pre = phase_run p right (phase_run p left pre).
Proof. revert pre;induction left;intro pre;cbn;[reflexivity|apply IHleft]. Qed.
Fixpoint replay p (Ghost:Type)(advance:Event->State->Ghost->unit->Ghost)
 events pre ghost : Ghost := match events with
 | []=>ghost
 | ev::rest=>replay p Ghost advance rest(PhaseSemantics p ev pre)(advance ev pre ghost tt)
 end.

Theorem checked_execution p catalog(certificate:BoundedCatalogCertificate p catalog)
 Ghost advance Boundary(Allowed:Event->Prop)
 (input:forall ev,Allowed ev ->CatalogEvent p catalog ev)
 (connect:forall seed ev pre,Allowed ev ->CombLFP p seed(phase_driven_state p ev pre) ->Boundary ev pre tt)
 events :Forall Allowed events ->forall pre ghost,CatalogShape p catalog pre ->
 Execution p Ghost unit advance Boundary pre ghost events(phase_run p events pre)
   (replay p Ghost advance events pre ghost).
Proof.
 intro HE;induction HE as[|ev rest HE HT IH];intros pre ghost HS;[constructor|].
 destruct(ExtendedSVBootstrap.catalog_phase_evidence p catalog certificate ev pre(input ev HE)HS)
 as[HL [HP HS']]. cbn [phase_run replay].
 eapply More with(input:=tt);[exact(connect _ ev pre HE HL)|apply IH;exact HS'].
Qed.
End ExtendedSVRuntimeHistory.
Print Assumptions ExtendedSVRuntimeHistory.checked_execution.
