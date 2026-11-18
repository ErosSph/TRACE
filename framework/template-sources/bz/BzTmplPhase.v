(** Bzeeno cycle route, phase layer (hand-written core, tools/cpu_tmpl_bzgate.py).
    One clock cycle `events ++ [rise] ++ [fall]` of the reference environment: the hypotheses of the edge/stage/RF-fall layers at BOTH
    clock events, the state equations, and the clock boundary after the cycle.
    Reused low-level facts (same AST, program BzeenoLoadUseJalASTConfigured3122be4a95.bzeeno_load_use_jal_program, ConfiguredAST.v sha256 556b0d6b...):
      GeneratedBoundedPhase.Phase.{original_phase}, GeneratedSeedBoot.Bootstrap.boot_events_allowed (as in BzTmplEnv),
      GeneratedClockCycleJoint.CycleJoint.{ClockBoundary, post_clock_inputs, scheduled_event_allowed}.
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVScalarHistory Lang.ExtendedSVPackedROM
 Lang.ExtendedSVDependencyCatalog Lang.ExtendedSVBoundedCatalogPhase Lang.ExtendedSVEmptyPipeline Lang.ExtendedSVRuntimeHistory
 GeneratedRuntimeInput.ConfiguredAST
 GeneratedDependencyCatalog.Catalog GeneratedBoundedPhase.Phase
 GeneratedSeedBoot.FrozenEnvironment GeneratedSeedBoot.Bootstrap GeneratedWriteValidityBoot.WriteValidityBoot
 GeneratedClockCycleJoint.CycleJoint TmplBzEdge.BzTmplEdge TmplBzEnv.BzTmplEnv.
Import ListNotations ExtendedSV ExtendedSVScalarHistory ExtendedSVDependencyCatalog ExtendedSVBoundedCatalogPhase ExtendedSVRuntimeHistory.
Local Open Scope Z_scope.
Local Opaque PhaseSemantics BzeenoLoadUseJalASTConfigured3122be4a95.bzeeno_load_use_jal_program.
Module BzTmplPhase.
Module F := GeneratedSeedBoot.FrozenEnvironment.
Module B := GeneratedSeedBoot.Bootstrap.
Module Phi := GeneratedBoundedPhase.Phase.
Module E := TmplBzEnv.BzTmplEnv.BzTmplEnv.
Module Ed := TmplBzEdge.BzTmplEdge.BzTmplEdge.
Notation P := BzeenoLoadUseJalASTConfigured3122be4a95.bzeeno_load_use_jal_program (only parsing).
Notation Cat := GeneratedDependencyCatalog.Catalog.actual_catalog.
Notation rs := E.rs.

(** The state after the rising / falling event of the cycle. *)
Definition rise_state words events : State := rs words (events ++ [F.rise]).
Definition fall_state words events : State := rs words ((events ++ [F.rise]) ++ [F.fall]).

Lemma rs_snoc words events ev : rs words (events ++ [ev]) = PhaseSemantics P ev (rs words events).
Proof. unfold rs, E.rs. rewrite phase_run_append. reflexivity. Qed.

Lemma rise_state_eq words events : rise_state words events = PhaseSemantics P F.rise (rs words events).
Proof. unfold rise_state. apply rs_snoc. Qed.
Lemma fall_state_eq words events : fall_state words events = PhaseSemantics P F.fall (rise_state words events).
Proof. unfold fall_state, rise_state. apply rs_snoc. Qed.

Lemma fall_catalog : CatalogEvent P Cat F.fall.
Proof. pose proof B.boot_events_allowed as H. unfold F.boot_events in H. inversion H as [|a l H1 H2 Ea]; subst.
 inversion H2 as [|a' l' H3 H4 Eb]; subst. inversion H4 as [|a'' l'' H5 H6 Ec]; subst. exact H5. Qed.

Lemma catalog_rise_fall events : Forall (CatalogEvent P Cat) events -> Forall (CatalogEvent P Cat) ((events ++ [F.rise]) ++ [F.fall]).
Proof. intro H. apply Forall_app. split.
 - apply Forall_app. split; [exact H|]. constructor; [exact E.rise_catalog|constructor].
 - constructor; [exact fall_catalog|constructor]. Qed.

Lemma catalog_rise events : Forall (CatalogEvent P Cat) events -> Forall (CatalogEvent P Cat) (events ++ [F.rise]).
Proof. intro H. apply Forall_app. split; [exact H|]. constructor; [exact E.rise_catalog|constructor]. Qed.

(** Clock boundary: the clock is 0 and the reset is 1 between cycles. *)
Theorem boundary_after_rise words events :
 read_signal (rs words events) 1%nat = 1 -> read_signal (rise_state words events) 0%nat = 1 /\ read_signal (rise_state words events) 1%nat = 1.
Proof. intro H. rewrite rise_state_eq. exact (post_clock_inputs F.rise (rs words events) 1 eq_refl eq_refl H). Qed.

Theorem boundary_after_fall words events :
 read_signal (rise_state words events) 1%nat = 1 -> ClockBoundary (fall_state words events).
Proof. intro H. rewrite fall_state_eq. exact (post_clock_inputs F.fall (rise_state words events) 0 eq_refl eq_refl H). Qed.

(** Fall-event hypotheses at an arbitrary catalog history whose clock is 1 and reset is 1. *)
Theorem env_fall_hyps : forall words events, Forall (CatalogEvent P Cat) events ->
 read_signal (rs words events) 0%nat = 1 -> read_signal (rs words events) 1%nat = 1 ->
 exists seed, changed_signal F.fall = 0%nat /\ new_value F.fall = 0 /\ read_signal (rs words events) 0%nat = 1 /\ read_signal (rs words events) 1%nat = 1 /\
 Ed.NetWords (rs words events) /\ CombLFP P seed (rs words events) /\
 CombLFP P (write_signal (rs words events) (changed_signal F.fall) (new_value F.fall)) (phase_driven_state P F.fall (rs words events)).
Proof.
 intros words events HE HB0 HB1. destruct (E.env_state words events HE) as [[Hlen Hw] [seed HL]].
 exists seed. split; [reflexivity|]. split; [reflexivity|]. split; [exact HB0|]. split; [exact HB1|]. split.
 - unfold Ed.NetWords. repeat split.
   all: first [ (rewrite HB0; reflexivity) | (rewrite HB1; reflexivity) | (eapply Hw; apply E.net_in; unfold E.nets; cbn; tauto) ].
 - split; [exact HL|].
   pose proof (Phi.original_phase F.fall (rs words events) fall_catalog (conj Hlen Hw)) as HP. cbv zeta in HP. destruct HP as [H1 _]. exact H1.
Qed.

(** Everything one cycle needs, from a catalog history at a clock boundary. *)
Theorem cycle_hyps : forall words events, Forall (CatalogEvent P Cat) events -> ClockBoundary (rs words events) ->
 (exists seed, changed_signal F.rise = 0%nat /\ new_value F.rise = 1 /\ read_signal (rs words events) 0%nat = 0 /\ read_signal (rs words events) 1%nat = 1 /\
   Ed.NetWords (rs words events) /\ CombLFP P seed (rs words events) /\
   CombLFP P (write_signal (rs words events) (changed_signal F.rise) (new_value F.rise)) (phase_driven_state P F.rise (rs words events))) /\
 (exists seed, changed_signal F.fall = 0%nat /\ new_value F.fall = 0 /\ read_signal (rise_state words events) 0%nat = 1 /\ read_signal (rise_state words events) 1%nat = 1 /\
   Ed.NetWords (rise_state words events) /\ CombLFP P seed (rise_state words events) /\
   CombLFP P (write_signal (rise_state words events) (changed_signal F.fall) (new_value F.fall)) (phase_driven_state P F.fall (rise_state words events))) /\
 ClockBoundary (fall_state words events) /\
 (exists seed, CombLFP P seed (fall_state words events)).
Proof.
 intros words events HE [HB0 HB1].
 split; [exact (E.env_rise_hyps words events HE (conj HB0 HB1))|].
 destruct (boundary_after_rise words events HB1) as [R0 R1].
 split; [exact (env_fall_hyps words (events ++ [F.rise]) (catalog_rise events HE) R0 R1)|].
 split; [exact (boundary_after_fall words events R1)|].
 destruct (E.env_state words _ (catalog_rise_fall events HE)) as [_ Hs]. exact Hs.
Qed.

(** The state after a whole cycle has all net words and is a comb fixed point (used by the INV at the next step). *)
Theorem fall_state_shape : forall words events, Forall (CatalogEvent P Cat) events ->
 CatalogShape P Cat (fall_state words events) /\ exists seed, CombLFP P seed (fall_state words events).
Proof. intros words events HE. exact (E.env_state words _ (catalog_rise_fall events HE)). Qed.
End BzTmplPhase.
Goal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.
Print Assumptions BzTmplPhase.rs_snoc.
Print Assumptions BzTmplPhase.rise_state_eq.
Print Assumptions BzTmplPhase.fall_state_eq.
Print Assumptions BzTmplPhase.catalog_rise_fall.
Print Assumptions BzTmplPhase.boundary_after_rise.
Print Assumptions BzTmplPhase.boundary_after_fall.
Print Assumptions BzTmplPhase.env_fall_hyps.
Print Assumptions BzTmplPhase.cycle_hyps.
Print Assumptions BzTmplPhase.fall_state_shape.
