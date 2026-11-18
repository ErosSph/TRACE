(** Bzeeno cycle route: the stage tags after one cycle (hand-written core, tools/cpu_tmpl_bzgate.py).
    With o_not_stall = 1 at the driven rise state, the tags [MEM; EX; ID] after `events ++ [rise] ++ [fall]` are [old EX; old ID; admitted]
    where admitted = Some (fetch pc 119) iff o_flush = 0 at the driven rise state.
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVBankAlignment Lang.ExtendedSVDependencyCatalog Lang.ExtendedSVScalarHistory Lang.ExtendedSVBoundedCatalogPhase GeneratedClockCycleJoint.CycleJoint GeneratedRuntimeInput.ConfiguredAST
 GeneratedDependencyCatalog.Catalog GeneratedSeedBoot.FrozenEnvironment
 TmplBzEdge.BzTmplEdge TmplBzEnv.BzTmplEnv TmplBzPhase.BzTmplPhase TmplBzValid.BzTmplValid TmplBzXfer.BzTmplXfer TmplBzFrame.BzTmplFrame TmplBzInv.BzTmplInv.
Import ListNotations ExtendedSV ExtendedSVBankAlignment ExtendedSVDependencyCatalog ExtendedSVScalarHistory ExtendedSVBoundedCatalogPhase.
Local Open Scope Z_scope.
Local Opaque PhaseSemantics BzeenoLoadUseJalASTConfigured3122be4a95.bzeeno_load_use_jal_program.
Module BzTmplShape.
Notation P := BzeenoLoadUseJalASTConfigured3122be4a95.bzeeno_load_use_jal_program (only parsing).
Module Ph := TmplBzPhase.BzTmplPhase.BzTmplPhase.
Module En := TmplBzEnv.BzTmplEnv.BzTmplEnv.
Module Va := TmplBzValid.BzTmplValid.BzTmplValid.
Module Xf := TmplBzXfer.BzTmplXfer.BzTmplXfer.
Module Fr := TmplBzFrame.BzTmplFrame.BzTmplFrame.
Module F := GeneratedSeedBoot.FrozenEnvironment.
Notation Cat := GeneratedDependencyCatalog.Catalog.actual_catalog.

Lemma bit1 (x : Z) : norm 1 (Z.land (norm 1 x) 1) = norm 1 x.
Proof. destruct (norm_bounds 1 x) as [H1 H2]. cbn in H2. assert (norm 1 x = 0 \/ norm 1 x = 1) by lia. destruct H as [H|H]; rewrite H; reflexivity. Qed.

Section Shape.
Context (words : list Z).
Local Notation rs := (En.rs words).
Definition drv (events : list Event) : State := phase_driven_state P F.rise (rs events).
Definition flushD (events : list Event) : Z := norm 1 (read_signal (drv events) 157%nat).
Definition stallD (events : list Event) : Z := norm 1 (read_signal (drv events) 156%nat).
Definition tag (S : State) (v pc : nat) : option Z := BzTmplInv.tok S v pc.

Theorem stages_after_cycle events :
 Forall (CatalogEvent P Cat) events -> ClockBoundary (rs events) -> stallD events = 1 ->
 [tag (Ph.fall_state words events) 286 287; tag (Ph.fall_state words events) 250 245; tag (Ph.fall_state words events) 141 139] =
 [tag (rs events) 250 245; tag (rs events) 141 139;
  if Z.eqb (flushD events) 0 then Some (norm 32 (read_signal (rs events) 119%nat)) else None].
Proof.
 intros HE HB Hn. destruct (Ph.cycle_hyps words events HE HB) as [[seed [Hc [Hv [H0 [H1 [HW [HL HD]]]]]]] [[seed2 [Hc2 [Hv2 [H02 [H12 [HW2 [HL2 HD2]]]]]]] _]].
 pose proof (conj Hc (conj Hv (conj H0 (conj H1 (conj HW (conj HL HD)))))) as HH.

 assert (V141 := Va.valid_141 F.rise (rs events) seed (flushD events) (stallD events) Hc Hv H0 H1 HW HL HD eq_refl eq_refl).
 assert (V250 := Va.valid_250 F.rise (rs events) seed (flushD events) (stallD events) Hc Hv H0 H1 HW HL HD eq_refl eq_refl).
 assert (V286 := Va.valid_286 F.rise (rs events) seed (flushD events) (stallD events) Hc Hv H0 H1 HW HL HD eq_refl eq_refl).
 assert (X139 := Xf.xfer_139 F.rise (rs events) seed (flushD events) (stallD events) HH eq_refl eq_refl).
 assert (X245 := Xf.xfer_245 F.rise (rs events) seed HH).
 assert (X287 := Xf.xfer_287 F.rise (rs events) seed HH).
 rewrite Hn in V141, V250, X139. 
 rewrite <- Ph.rise_state_eq in V141, V250, V286, X139, X245, X287. rewrite Ph.fall_state_eq.
 set (mid := Ph.rise_state words events) in *.
 unfold tag, BzTmplInv.tok, BzTmplInv.rg.
 rewrite (Fr.fall_frame_286 F.fall mid seed2 Hc2 Hv2 H02 H12 HW2 HL2 HD2),
   (Fr.fall_frame_287 F.fall mid seed2 Hc2 Hv2 H02 H12 HW2 HL2 HD2),
   (Fr.fall_frame_250 F.fall mid seed2 Hc2 Hv2 H02 H12 HW2 HL2 HD2),
   (Fr.fall_frame_245 F.fall mid seed2 Hc2 Hv2 H02 H12 HW2 HL2 HD2),
   (Fr.fall_frame_141 F.fall mid seed2 Hc2 Hv2 H02 H12 HW2 HL2 HD2),
   (Fr.fall_frame_139 F.fall mid seed2 Hc2 Hv2 H02 H12 HW2 HL2 HD2).
 rewrite V141, V250, V286, X139, X245, X287. rewrite bit1.
 destruct (Z.eqb (flushD events) 0) eqn:Ef; cbn;
  rewrite ?norm_idempotent; reflexivity.
Qed.
End Shape.
End BzTmplShape.
Goal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.
Print Assumptions BzTmplShape.stages_after_cycle.
