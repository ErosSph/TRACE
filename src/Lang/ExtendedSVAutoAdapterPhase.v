(** Static, compiled-plan certificates for actual physical-phase root outputs.
    No processor-specific identifiers or assumed transition summaries. *)
From Coq Require Import List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection
 Lang.ExtendedSVProcessSlice Lang.ExtendedSVAutoAdapterPlan.
Import ExtendedSV ExtendedSVRootProjection ExtendedSVProcessSlice
 ExtendedSVAutoAdapterPlan ListNotations.
Module ExtendedSVAutoAdapterPhase.

Definition is_sequential (proc : Process) : bool :=
 match process_kind proc with Sequential => true | _ => false end.

Record PlanRootCertificate (p : Program) (root : signal)
    (entries : list (Process * NbPlan)) : Prop := {
 plan_root_in_bounds : (root < signal_count p)%nat;
 plan_root_comb_unwritten : comb_root_unwrittenb p root = true;
 plan_root_exact_writers :
   filter is_sequential (filter (writes_rootb root) (processes p)) =
   map fst entries;
 plan_root_compiled : Forall (fun entry =>
   compile_nb (statement_fuel p) (process_body (fst entry)) =
   Some (snd entry)) entries
}.

Definition plan_transition_updates (old new : State)
    (entries : list (Process * NbPlan)) : list Update :=
 flat_map (fun entry =>
   if process_matches_states old new (fst entry)
   then eval_plan new (snd entry) else []) entries.

Lemma selected_sequential_only old new ps :
 filter (process_matches_states old new) ps =
 filter (process_matches_states old new) (filter is_sequential ps).
Proof.
 induction ps as [|proc rest IH]; cbn; [reflexivity|].
 destruct proc as [kind events body line]; destruct kind;
   cbn [is_sequential process_matches_states process_kind process_events];
   rewrite ?IH; reflexivity.
Qed.

Lemma compiled_entries_updates p entries old new :
 Forall (fun entry => compile_nb (statement_fuel p)
   (process_body (fst entry)) = Some (snd entry)) entries ->
 flat_map (process_updates p new)
   (filter (process_matches_states old new) (map fst entries)) =
 plan_transition_updates old new entries.
Proof.
 intros HC. induction HC as [|[proc plan] rest Hhead Hrest IH];
   cbn [map filter flat_map plan_transition_updates fst snd] in *.
 - reflexivity.
 - destruct (process_matches_states old new proc); cbn.
   + rewrite (checked_process_plan p proc plan Hhead new), IH. reflexivity.
   + exact IH.
Qed.

Theorem planned_phase_root p root entries :
 PlanRootCertificate p root entries -> forall ev pre,
 changed_signal ev <> root ->
 read_signal (PhaseSemantics p ev pre) root =
 apply_updates_root_value root (read_signal pre root)
   (plan_transition_updates pre (phase_driven_state p ev pre) entries).
Proof.
 intros [HB HC HW HP] ev pre HE.
 rewrite phase_root_projection by assumption.
 unfold phase_update_chain.
 rewrite process_slice_sound.
 unfold selected_on_transition.
 rewrite filter_swap.
 rewrite selected_sequential_only, HW.
 rewrite (compiled_entries_updates p entries pre
   (phase_driven_state p ev pre) HP). reflexivity.
Qed.

Print Assumptions planned_phase_root.
End ExtendedSVAutoAdapterPhase.
