(** Binary-run agreement propagation through the ORIGINAL process order.
    This consumes semantic producer proofs, not an unverified dependency graph. *)
From Coq Require Import List Bool PeanoNat.
Require Import Lang.ExtendedSV Lang.ExtendedSVExprAgreement Lang.ExtendedSVKnownInputs
 Lang.ExtendedSVRootProjection.
Import ExtendedSV ExtendedSVExprAgreement ExtendedSVKnownInputs ExtendedSVRootProjection ListNotations.
Module ExtendedSVDependencyPropagation.
Record DependencyRow:={dependency_inputs:list Wire;dependency_outputs:list Wire}.
Definition RowSound p proc row:=forall s t,InputsAgree s t(dependency_inputs row)->
 InputsAgree(run_process p s proc)(run_process p t proc)(dependency_outputs row).
Definition dependency_step proc rows known:=
 filter(fun wr=>negb(existsb(Nat.eqb(snd wr))(process_writers proc)))known++
 flat_map(fun row=>if containsb known(dependency_inputs row)then dependency_outputs row else[])rows.
Theorem actual_dependency_step p proc rows known s t :
 Forall(RowSound p proc)rows->InputsAgree s t known->
 InputsAgree(run_process p s proc)(run_process p t proc)(dependency_step proc rows known).
Proof.
 intros HS HA w r HI. apply in_app_or in HI as[HI|HI].
 - apply filter_In in HI as[HI HN]. apply negb_true_iff in HN.
   assert(Hfree:~In r(process_writers proc)).
   { intro HR. assert(existsb(Nat.eqb r)(process_writers proc)=true).
     { apply existsb_exists. exists r. split;[exact HR|apply Nat.eqb_refl]. } cbn in HN. congruence. }
   rewrite !run_process_preserves_unwritten_root by exact Hfree. now apply HA.
 - apply in_flat_map in HI as[row[HR HO]].
   destruct(containsb known(dependency_inputs row))eqn:HC;[|contradiction].
   apply Forall_forall with(x:=row)in HS;[|exact HR].
   exact(HS s t(contains_agree _ _ _ _ HC HA)w r HO).
Qed.
Definition Catalog:=list(Process*list DependencyRow).
Definition CatalogSound p(catalog:Catalog):=Forall(fun entry=>Forall(RowSound p(fst entry))(snd entry))catalog.
Definition propagate(catalog:Catalog)known:=fold_left(fun k entry=>dependency_step(fst entry)(snd entry)k)catalog known.
Theorem actual_catalog_agreement p catalog known s t : CatalogSound p catalog->InputsAgree s t known->
 InputsAgree(fold_left(run_process p)(map fst catalog)s)(fold_left(run_process p)(map fst catalog)t)(propagate catalog known).
Proof.
 induction catalog as[|[proc rows]rest IH]in known,s,t|-*;intros HC HA;[exact HA|].
 inversion HC as[|entry entries HH HT];subst. cbn[map fold_left propagate].
 apply IH;[exact HT|now apply actual_dependency_step].
Qed.
Fixpoint propagate_rounds n catalog known:=match n with O=>known|S k=>propagate_rounds k catalog(propagate catalog known)end.
Theorem actual_rounds_agreement p catalog : map fst catalog=filter is_comb(processes p)->CatalogSound p catalog->
 forall n known s t,InputsAgree s t known->
 InputsAgree(comb_iter p n s)(comb_iter p n t)(propagate_rounds n catalog known).
Proof.
 intros HO HC n. induction n;intros known s t HA;[exact HA|].
 cbn[comb_iter propagate_rounds]. apply IHn.
 unfold comb_round. rewrite <-HO. now apply actual_catalog_agreement.
Qed.
Print Assumptions actual_rounds_agreement.
End ExtendedSVDependencyPropagation.
