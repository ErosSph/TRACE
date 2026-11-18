(** Exact idle physical-phase closure at the original combinational fixed point.
    No CPU-specific fields, fuel change, or alternative phase semantics. *)
From Coq Require Import List.
Require Import Lang.ExtendedSV.
Import ExtendedSV ListNotations.
Module ExtendedSVIdlePhase.
Lemma comb_iter_fixed p fixed n :comb_round p fixed=fixed ->comb_iter p n fixed=fixed.
Proof. intro H. induction n;[reflexivity|]. cbn[comb_iter]. now rewrite H. Qed.
Lemma candidate_at_fixed p fixed :comb_round p fixed=fixed ->lfp_candidate p fixed=fixed.
Proof. unfold lfp_candidate. apply comb_iter_fixed. Qed.
Lemma lfp_is_stable p seed fixed :CombLFP p seed fixed ->comb_round p fixed=fixed.
Proof. intros[n actual HI HS]. exact HS. Qed.
Theorem idle_phase_is_driven p ev pre :
 CombLFP p(write_signal pre(changed_signal ev)(new_value ev))(phase_driven_state p ev pre) ->
 selected_on_transition p pre(phase_driven_state p ev pre)=[] ->
 PhaseSemantics p ev pre=phase_driven_state p ev pre.
Proof.
 intros HL Hempty. unfold PhaseSemantics,phase_execute_order.
 rewrite Hempty. cbn[execute_process_order flat_map apply_updates].
 apply candidate_at_fixed. now apply(lfp_is_stable p _ _ HL).
Qed.
Theorem idle_phase_post_lfp p ev pre :
 CombLFP p(write_signal pre(changed_signal ev)(new_value ev))(phase_driven_state p ev pre) ->
 selected_on_transition p pre(phase_driven_state p ev pre)=[] ->
 CombLFP p
 (execute_process_order p(phase_driven_state p ev pre)
   (selected_on_transition p pre(phase_driven_state p ev pre)))
 (PhaseSemantics p ev pre).
Proof.
 intros HL Hempty. rewrite(idle_phase_is_driven p ev pre HL Hempty),Hempty.
 cbn[execute_process_order flat_map apply_updates].
 eapply CombLFP_intro with(n:=0%nat);[reflexivity|].
 exact(lfp_is_stable p _ _ HL).
Qed.
End ExtendedSVIdlePhase.
Print Assumptions ExtendedSVIdlePhase.idle_phase_post_lfp.
