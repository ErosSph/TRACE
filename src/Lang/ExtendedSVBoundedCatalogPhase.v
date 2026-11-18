(** Original-budget full-state LFP/phase from checked dependency propagation.
    Raw equality additionally requires the explicit width/length shape; it is
    never inferred from normalized projection agreement alone. *)
From Coq Require Import List Bool PeanoNat ZArith Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVExprAgreement Lang.ExtendedSVDependencyPropagation
 Lang.ExtendedSVDependencyCatalog Lang.ExtendedSVRootProjection Lang.ExtendedSVWordInvariant
 Lang.ExtendedSVStateLength Lang.ExtendedSVStaticProcessGroups.
Import ListNotations ExtendedSV ExtendedSVExprAgreement ExtendedSVDependencyPropagation
 ExtendedSVDependencyCatalog ExtendedSVRootProjection ExtendedSVWordInvariant
 ExtendedSVStateLength ExtendedSVStaticProcessGroups.
Module ExtendedSVBoundedCatalogPhase.
Definition catalog_writers p:=flat_map process_writers(filter is_comb(processes p)).
Definition catalog_covers_writersb p catalog:=forallb(fun root=>
 existsb(fun wr=>Nat.eqb(snd wr)root)(catalog_outputs catalog))(catalog_writers p).
Definition catalog_word_checksb p catalog:=forallb(fun wr=>program_wordb p(fst wr)(snd wr))(catalog_outputs catalog).
Definition bounded_catalog_checksb p catalog:=catalog_convergesb p catalog&&catalog_word_checksb p catalog&&
 catalog_covers_writersb p catalog&&program_lengthb p(signal_count p)&&sequential_writers_disjointb p.
Record BoundedCatalogCertificate p catalog:Prop:={
 bounded_order:map fst catalog=filter is_comb(processes p);
 bounded_sound:CatalogSound p catalog;
 bounded_converges:catalog_convergesb p catalog=true;
 bounded_words:catalog_word_checksb p catalog=true;
 bounded_coverage:catalog_covers_writersb p catalog=true;
 bounded_length:program_lengthb p(signal_count p)=true;
 bounded_sequential:sequential_writers_disjointb p=true
}.
Theorem checked_bounded_catalog p catalog : map fst catalog=filter is_comb(processes p)->
 CatalogSound p catalog->bounded_catalog_checksb p catalog=true->BoundedCatalogCertificate p catalog.
Proof.
 intros HO HS HC. unfold bounded_catalog_checksb in HC.
 repeat rewrite andb_true_iff in HC. destruct HC as[[[[HA HW]HC]HL]HQ].
 constructor;assumption.
Qed.
Definition CatalogWords catalog s:=forall w r,In(w,r)(catalog_outputs catalog)->WordRoot w r s.
Definition CatalogShape p catalog s:=length s=signal_count p /\ CatalogWords catalog s.
Definition CatalogEvent p catalog ev:=
 (changed_signal ev<signal_count p)%nat /\
 forall w r,In(w,r)(catalog_outputs catalog)->r<>changed_signal ev.
Section Certified.
Variable p:Program.
Variable catalog:Catalog.
Variable certificate:BoundedCatalogCertificate p catalog.
Lemma output_word_checked w r : In(w,r)(catalog_outputs catalog)->program_wordb p w r=true.
Proof.
 intro HI. exact(proj1(forallb_forall _ _)(bounded_words _ _ certificate)(w,r)HI).
Qed.
Lemma iter_catalog_words n s : CatalogWords catalog s->CatalogWords catalog(comb_iter p n s).
Proof. intros HW w r HI. apply iter_word;[now apply output_word_checked|exact(HW w r HI)]. Qed.
Lemma outside_writer_checked r : ~In r(catalog_writers p)->comb_root_unwrittenb p r=true.
Proof.
 intro HN. unfold comb_root_unwrittenb. apply forallb_forall. intros proc HP.
 apply negb_true_iff. destruct(existsb(Nat.eqb r)(process_writers proc))eqn:HE;[|reflexivity].
 apply existsb_exists in HE as[x[HX HE]]. apply Nat.eqb_eq in HE. subst x.
 exfalso. apply HN. unfold catalog_writers. apply in_flat_map. exists proc. auto.
Qed.
Lemma original_budget_all_raw_roots s : CatalogWords catalog s->forall r,
 read_signal(comb_iter p(lfp_fuel p)s)r=read_signal(comb_iter p(S(lfp_fuel p))s)r.
Proof.
 intros HW r. destruct(in_dec Nat.eq_dec r(catalog_writers p))as[HR|HR].
 - pose proof(proj1(forallb_forall _ _)(bounded_coverage _ _ certificate)r HR)as HC.
   apply existsb_exists in HC as[[w root][HI HE]]. cbn in HE. apply Nat.eqb_eq in HE. subst root.
   pose proof(iter_catalog_words(lfp_fuel p)s HW w r HI)as Hn.
   pose proof(iter_catalog_words(S(lfp_fuel p))s HW w r HI)as Hnext.
   unfold WordRoot,Word in Hn,Hnext. rewrite Hn,Hnext.
   exact(original_budget_catalog_agreement p catalog(bounded_order _ _ certificate)
    (bounded_sound _ _ certificate)(bounded_converges _ _ certificate)s w r HI).
 - rewrite !comb_iter_preserves_unwritten_root by now apply outside_writer_checked. reflexivity.
Qed.
Lemma iter_after_round n s : comb_round p(comb_iter p n s)=comb_iter p(S n)s.
Proof. induction n in s|-*;[reflexivity|]. cbn[comb_iter]. exact(IHn(comb_round p s)). Qed.
Theorem original_catalog_candidate_lfp s : CatalogShape p catalog s->CombLFP p s(lfp_candidate p s).
Proof.
 intros[HL HW]. apply CombLFP_intro with(n:=lfp_fuel p);[reflexivity|].
 unfold lfp_candidate. rewrite iter_after_round. apply state_ext.
 - rewrite(iter_length p(signal_count p)(S(lfp_fuel p))s(bounded_length _ _ certificate)HL),
    (iter_length p(signal_count p)(lfp_fuel p)s(bounded_length _ _ certificate)HL). reflexivity.
 - intro r. symmetry. exact(original_budget_all_raw_roots s HW r).
Qed.
Lemma candidate_shape s : CatalogShape p catalog s->CatalogShape p catalog(lfp_candidate p s).
Proof.
 intros[HL HW]. split.
 - exact(iter_length p(signal_count p)(lfp_fuel p)s(bounded_length _ _ certificate)HL).
 - exact(iter_catalog_words(lfp_fuel p)s HW).
Qed.
Lemma input_shape ev s : CatalogEvent p catalog ev->CatalogShape p catalog s->
 CatalogShape p catalog(write_signal s(changed_signal ev)(new_value ev)).
Proof.
 intros[HB HE][HL HW]. split.
 - rewrite write_length;[exact HL|now rewrite HL].
 - intros w r HI. unfold WordRoot. rewrite read_signal_write_other;[exact(HW w r HI)|].
   pose proof(HE w r HI). congruence.
Qed.
Lemma captured_shape old s : CatalogShape p catalog s->
 CatalogShape p catalog(execute_process_order p s(selected_on_transition p old s)).
Proof.
 intros[HL HW]. split.
 - apply captured_length;[exact(bounded_length _ _ certificate)| |exact HL].
   intros proc HP. apply filter_In in HP. tauto.
 - intros w r HI. unfold execute_process_order. apply apply_updates_word;[|exact(HW w r HI)].
   apply Forall_forall. intros u HU. apply in_flat_map in HU as[proc[HP HU]].
   apply filter_In in HP as[HP _].
   pose proof(proj2(process_word p w r proc s
    (process_word_checked _ _ _ _ (output_word_checked w r HI)HP)(HW w r HI)))as HC.
   exact(proj1(Forall_forall _ _)HC u HU).
Qed.
Theorem original_catalog_phase ev pre : CatalogEvent p catalog ev->CatalogShape p catalog pre->
 let driven:=phase_driven_state p ev pre in
 CombLFP p(write_signal pre(changed_signal ev)(new_value ev))driven /\
 CombLFP p(execute_process_order p driven(selected_on_transition p pre driven))
  (PhaseSemantics p ev pre) /\ PhaseIndependentAt p ev pre.
Proof.
 intros HE HS. cbn zeta.
 assert(HD:CatalogShape p catalog(phase_driven_state p ev pre)).
 { apply candidate_shape. exact(input_shape ev pre HE HS). }
 split.
 - apply original_catalog_candidate_lfp. exact(input_shape ev pre HE HS).
 - split.
   + apply original_catalog_candidate_lfp. now apply captured_shape.
   + apply static_sequential_writers_imply_original_phase_independent. exact(bounded_sequential _ _ certificate).
Qed.
Theorem original_catalog_phase_shape ev pre : CatalogEvent p catalog ev->CatalogShape p catalog pre->
 CatalogShape p catalog(PhaseSemantics p ev pre).
Proof. intros HE HS. apply candidate_shape,captured_shape,candidate_shape. exact(input_shape ev pre HE HS). Qed.
End Certified.
End ExtendedSVBoundedCatalogPhase.
Print Assumptions ExtendedSVBoundedCatalogPhase.checked_bounded_catalog.
Print Assumptions ExtendedSVBoundedCatalogPhase.original_catalog_candidate_lfp.
Print Assumptions ExtendedSVBoundedCatalogPhase.original_catalog_phase.
Print Assumptions ExtendedSVBoundedCatalogPhase.original_catalog_phase_shape.
