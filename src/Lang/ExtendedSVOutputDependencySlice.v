(** Checked per-output dependency rows from original blocking-process slices.
    The proposed root sets are untrusted: actual slice and known-input checks
    must all succeed. This alone is not complete catalog coverage or an LFP. *)
From Coq Require Import List Bool PeanoNat.
Require Import Lang.ExtendedSV Lang.ExtendedSVExprAgreement Lang.ExtendedSVBlocking
 Lang.ExtendedSVKnownInputs Lang.ExtendedSVInferredDependencies
 Lang.ExtendedSVOutputSlice Lang.ExtendedSVDependencyPropagation.
Import ListNotations ExtendedSV ExtendedSVExprAgreement ExtendedSVBlocking
 ExtendedSVKnownInputs ExtendedSVInferredDependencies ExtendedSVOutputSlice
 ExtendedSVDependencyPropagation.
Module ExtendedSVOutputDependencySlice.
Record OutputSliceProposal := {
 kept_roots:list signal;
 observed_roots:list signal;
 wanted_outputs:list Wire
}.
Definition slice_inputs p proc proposal :=
 external_inputs(sliced_process p(kept_roots proposal)proc).
Definition proposed_row p proc proposal : DependencyRow :=
 {|dependency_inputs:=slice_inputs p proc proposal;dependency_outputs:=wanted_outputs proposal|}.
Definition outputs_observedb outputs roots:=
 forallb(fun wr:Wire=>existsb(Nat.eqb(snd wr))roots)outputs.
Lemma outputs_observed_sound outputs roots w r : outputs_observedb outputs roots=true->
 In(w,r)outputs->In r roots.
Proof.
 intros HC HI. apply forallb_forall with(x:=(w,r))in HC;[|exact HI].
 apply existsb_exists in HC as[r'[HR HE]]. cbn in HE. apply Nat.eqb_eq in HE. now subst r'.
Qed.
Definition slice_dependencyb p proc proposal :=
 let targets:=kept_roots proposal in let observed:=observed_roots proposal in
 let sliced:=sliced_process p targets proc in
 output_slice_safeb(statement_fuel p)targets observed(process_body proc) &&
 blocking_onlyb(process_body proc) && blocking_onlyb(process_body sliced) &&
 outputs_observedb(wanted_outputs proposal)observed &&
 match infer_known(statement_fuel p)(slice_inputs p proc proposal)(process_body sliced)with
 |Some known=>containsb known(wanted_outputs proposal)|None=>false end.

Theorem checked_output_slice_row p proc proposal : slice_dependencyb p proc proposal=true->
 RowSound p proc(proposed_row p proc proposal).
Proof.
 unfold slice_dependencyb. intro HC.
 apply andb_true_iff in HC as [HC HK]. apply andb_true_iff in HC as [HC HO].
 apply andb_true_iff in HC as [HC HS]. apply andb_true_iff in HC as [HF HB].
 destruct(infer_known(statement_fuel p)(slice_inputs p proc proposal)
  (process_body(sliced_process p(kept_roots proposal)proc)))as[known|]eqn:HE;[|discriminate].
 intros s t HA w r HI.
 assert(HR:In r(observed_roots proposal))by
  exact(outputs_observed_sound _ _ w r HO HI).
 rewrite(actual_output_slice_process p(kept_roots proposal)(observed_roots proposal)proc s HF HB HS r HR),
  (actual_output_slice_process p(kept_roots proposal)(observed_roots proposal)proc t HF HB HS r HR).
 pose proof(actual_known_process p(sliced_process p(kept_roots proposal)proc)
  (slice_inputs p proc proposal)known s t HE HS HA)as Hknown.
 exact(contains_agree _ _ _ _ HK Hknown w r HI).
Qed.
Definition checked_slice_rows p proc proposals :=
 map(proposed_row p proc)(filter(slice_dependencyb p proc)proposals).
Theorem checked_output_slice_rows p proc proposals :
 Forall(RowSound p proc)(checked_slice_rows p proc proposals).
Proof.
 apply Forall_forall. intros row HI. apply in_map_iff in HI as[proposal[<- HI]].
 apply filter_In in HI as [_ HC]. exact(checked_output_slice_row p proc proposal HC).
Qed.
Definition checked_slice_catalog p entries : Catalog :=
 map(fun entry=>(fst entry,checked_slice_rows p(fst entry)(snd entry)))entries.
Theorem checked_output_slice_catalog p entries : CatalogSound p(checked_slice_catalog p entries).
Proof.
 apply Forall_forall. intros entry HI. apply in_map_iff in HI as[[proc proposals][<- HI]].
 exact(checked_output_slice_rows p proc proposals).
Qed.
End ExtendedSVOutputDependencySlice.
Print Assumptions ExtendedSVOutputDependencySlice.outputs_observed_sound.
Print Assumptions ExtendedSVOutputDependencySlice.checked_output_slice_row.
Print Assumptions ExtendedSVOutputDependencySlice.checked_output_slice_rows.
Print Assumptions ExtendedSVOutputDependencySlice.checked_output_slice_catalog.
