(** Public checked rows and original-budget agreement propagation.
    Catalog soundness is separate from coverage and actual convergence. *)
From Coq Require Import List Bool PeanoNat.
Require Import Lang.ExtendedSV Lang.ExtendedSVExprAgreement Lang.ExtendedSVKnownInputs
 Lang.ExtendedSVInferredDependencies Lang.ExtendedSVInferredProducerCertificate
 Lang.ExtendedSVSingleLeafDependency Lang.ExtendedSVOutputDependencySlice
 Lang.ExtendedSVDependencyPropagation Lang.ExtendedSVRootProjection.
Import ListNotations ExtendedSV ExtendedSVExprAgreement ExtendedSVKnownInputs
 ExtendedSVInferredDependencies ExtendedSVInferredProducerCertificate ExtendedSVSingleLeafDependency
 ExtendedSVOutputDependencySlice ExtendedSVDependencyPropagation ExtendedSVRootProjection.
Module ExtendedSVDependencyCatalog.
Inductive DependencyProposal :=
 | WholeSummary
 | ScalarLeaf(width:nat)(root:signal)
 | OutputSlice(proposal:OutputSliceProposal).
Definition dependency_proposal_check p proc proposal := match proposal with
 | WholeSummary=>summaryb p proc
 | ScalarLeaf width root=>single_leafb(statement_fuel p)width root(process_body proc)
 | OutputSlice candidate=>slice_dependencyb p proc candidate
 end.
Definition dependency_proposal_row p proc proposal : DependencyRow := match proposal with
 | WholeSummary=>{|dependency_inputs:=external_inputs proc;
     dependency_outputs:=inferred_outputs(process_body proc)|}
 | ScalarLeaf width root=>{|dependency_inputs:=statement_inputs(process_body proc);dependency_outputs:=[(width,root)]|}
 | OutputSlice candidate=>proposed_row p proc candidate
 end.
Theorem checked_dependency_proposal p proc proposal :
 dependency_proposal_check p proc proposal=true->RowSound p proc(dependency_proposal_row p proc proposal).
Proof.
 destruct proposal as [|width root|candidate];cbn.
 - exact(checked_external_dependency p proc).
 - intros HC s t HA w r HI. destruct HI as[HI|[]]. inversion HI;subst w r.
   exact(actual_single_leaf_process p proc width root HC s t HA).
 - exact(checked_output_slice_row p proc candidate).
Qed.
Definition checked_dependency_rows p proc proposals :=
 map(dependency_proposal_row p proc)(filter(dependency_proposal_check p proc)proposals).
Theorem checked_dependency_rows_sound p proc proposals :
 Forall(RowSound p proc)(checked_dependency_rows p proc proposals).
Proof.
 apply Forall_forall. intros row HI. apply in_map_iff in HI as[proposal[<- HI]].
 apply filter_In in HI as[_ HC]. exact(checked_dependency_proposal p proc proposal HC).
Qed.
Definition checked_dependency_catalog p entries : Catalog :=
 map(fun entry=>(fst entry,checked_dependency_rows p(fst entry)(snd entry)))entries.
Theorem checked_dependency_catalog_sound p entries : CatalogSound p(checked_dependency_catalog p entries).
Proof.
 apply Forall_forall. intros entry HI. apply in_map_iff in HI as[[proc proposals][<- HI]].
 exact(checked_dependency_rows_sound p proc proposals).
Qed.
Definition wire_eq_dec (a b:Wire) : {a=b}+{a<>b}.
Proof. decide equality;apply Nat.eq_dec. Defined.
Definition catalog_outputs(catalog:Catalog):list Wire :=
 nodup wire_eq_dec(flat_map(fun entry=>flat_map dependency_outputs(snd entry))catalog).
Definition catalog_initial_known p(catalog:Catalog):list Wire :=
 nodup wire_eq_dec(filter(fun wr=>comb_root_unwrittenb p(snd wr))
  (flat_map(fun entry=>flat_map dependency_inputs(snd entry))catalog)).
Lemma catalog_initial_inputs_stable p catalog s :
 InputsAgree s(comb_round p s)(catalog_initial_known p catalog).
Proof.
 intros w r HI. apply nodup_In in HI. apply filter_In in HI as[HI HC].
 rewrite(comb_round_preserves_unwritten_root p r HC s). reflexivity.
Qed.
Definition catalog_convergesb p catalog :=
 containsb(propagate_rounds(lfp_fuel p)catalog(catalog_initial_known p catalog))(catalog_outputs catalog).
Theorem original_budget_catalog_agreement p catalog :
 map fst catalog=filter is_comb(processes p)->CatalogSound p catalog->
 catalog_convergesb p catalog=true->forall s,
 InputsAgree(comb_iter p(lfp_fuel p)s)(comb_iter p(S(lfp_fuel p))s)(catalog_outputs catalog).
Proof.
 intros HO HC HD s. unfold catalog_convergesb in HD.
 pose proof(actual_rounds_agreement p catalog HO HC(lfp_fuel p)
  (catalog_initial_known p catalog)s(comb_round p s)(catalog_initial_inputs_stable p catalog s))as HA.
 exact(contains_agree _ _ _ _ HD HA).
Qed.
End ExtendedSVDependencyCatalog.
Print Assumptions ExtendedSVDependencyCatalog.checked_dependency_proposal.
Print Assumptions ExtendedSVDependencyCatalog.checked_dependency_catalog_sound.
Print Assumptions ExtendedSVDependencyCatalog.original_budget_catalog_agreement.
