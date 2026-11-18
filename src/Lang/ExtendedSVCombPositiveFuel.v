(** Preserve the original positive iteration budget, rather than replacing a
    multi-round Program by a fuel-1 Program. A full ordered certificate remains
    essential: positive fuel alone says nothing about convergence. *)
From Coq Require Import List PeanoNat.
Require Import Lang.ExtendedSV Lang.ExtendedSVCombIdempotence
 Lang.ExtendedSVStaticProcessGroups.
Import ListNotations ExtendedSV ExtendedSVCombIdempotence
 ExtendedSVStaticProcessGroups.
Module ExtendedSVCombPositiveFuel.
Lemma stable_state_all_iterations p fixed : comb_round p fixed=fixed ->
 forall n,comb_iter p n fixed=fixed.
Proof.
 intros HS n. induction n as[|n IH];[reflexivity|].
 cbn[comb_iter]. rewrite HS. exact IH.
Qed.
Theorem original_positive_candidate_equals_one_pass p :
 (0<lfp_fuel p)%nat ->
 OrderedProducerCertificate p(filter is_comb(processes p))->forall seed,
 lfp_candidate p seed=comb_round p seed.
Proof.
 intros HF HC seed. unfold lfp_candidate.
 destruct(lfp_fuel p)as[|n];[inversion HF|].
 cbn[comb_iter]. apply stable_state_all_iterations.
 exact(certified_original_comb_round_is_idempotent p HC seed).
Qed.
Theorem original_positive_candidate_is_LFP p :
 (0<lfp_fuel p)%nat ->
 OrderedProducerCertificate p(filter is_comb(processes p))->forall seed,
 CombLFP p seed(lfp_candidate p seed).
Proof.
 intros HF HC seed. apply CombLFP_intro with(n:=lfp_fuel p).
 - reflexivity.
 - rewrite(original_positive_candidate_equals_one_pass p HF HC seed).
   exact(certified_original_comb_round_is_idempotent p HC seed).
Qed.
Theorem original_positive_phase p :
 (0<lfp_fuel p)%nat ->
 OrderedProducerCertificate p(filter is_comb(processes p))->
 sequential_writers_disjointb p=true ->forall ev pre,
 let driven:=phase_driven_state p ev pre in
 CombLFP p(write_signal pre(changed_signal ev)(new_value ev))driven /\
 CombLFP p(execute_process_order p driven(selected_on_transition p pre driven))
  (PhaseSemantics p ev pre) /\ PhaseIndependentAt p ev pre.
Proof.
 intros HF HC HS ev pre. cbn zeta. split.
 - unfold phase_driven_state.
   exact(original_positive_candidate_is_LFP p HF HC _).
 - split.
   + unfold PhaseSemantics,phase_execute_order.
     exact(original_positive_candidate_is_LFP p HF HC _).
   + exact(static_sequential_writers_imply_original_phase_independent p ev pre HS).
Qed.
End ExtendedSVCombPositiveFuel.
Print Assumptions ExtendedSVCombPositiveFuel.original_positive_candidate_equals_one_pass.
Print Assumptions ExtendedSVCombPositiveFuel.original_positive_candidate_is_LFP.
Print Assumptions ExtendedSVCombPositiveFuel.original_positive_phase.
