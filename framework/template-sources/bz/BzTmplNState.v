(** Bzeeno cycle route: o_not_stall = 1 at the driven rising-edge state, from the INV (load flags 0 and a legal word at IF/ID; hand-written core).
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVBankAlignment Lang.ExtendedSVDependencyCatalog Lang.ExtendedSVScalarHistory Lang.ExtendedSVBoundedCatalogPhase
 Lang.ExtendedSVSeqTree GeneratedClockCycleJoint.CycleJoint GeneratedRuntimeInput.ConfiguredAST GeneratedDependencyCatalog.Catalog GeneratedSeedBoot.FrozenEnvironment
 TmplBzEdge.BzTmplEdge TmplBzEnv.BzTmplEnv TmplBzStage.BzTmplStage TmplBzCtlIn.BzTmplCtlIn TmplBzNOne.BzTmplNOne TmplBzInv.BzTmplInv
 coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte.
Import ListNotations ExtendedSV ExtendedSVBankAlignment ExtendedSVDependencyCatalog ExtendedSVScalarHistory ExtendedSVBoundedCatalogPhase.
Local Open Scope Z_scope.
Local Opaque PhaseSemantics BzeenoLoadUseJalASTConfigured3122be4a95.bzeeno_load_use_jal_program.
Module BzTmplNState.
Notation P := BzeenoLoadUseJalASTConfigured3122be4a95.bzeeno_load_use_jal_program (only parsing).
Module En := TmplBzEnv.BzTmplEnv.BzTmplEnv.
Module Ed := TmplBzEdge.BzTmplEdge.BzTmplEdge.
Module St := TmplBzStage.BzTmplStage.BzTmplStage.
Module F := GeneratedSeedBoot.FrozenEnvironment.
Notation Cat := GeneratedDependencyCatalog.Catalog.actual_catalog.
Section NState.
Context {word : Interface.word 32} {BW : Bitwidth 32} {Registers : map.map Decode.Register word} {Mem : map.map word byte}
 {word_ok : word.ok word} {registers_ok : map.ok Registers} {mem_ok : map.ok Mem}.
Context (words : list Z).
Theorem n_one_state events :
 Forall (CatalogEvent P Cat) events -> ClockBoundary (En.rs words events) -> BzTmplInv.Struct (En.rs words events) ->
 norm 1 (read_signal (phase_driven_state P F.rise (En.rs words events)) 156%nat) = 1.
Proof.
 intros HE HB HS.
 destruct (En.env_rise_hyps words events HE HB) as [seed [Hc [Hv [H0 [H1 [HW [HL HD]]]]]]].
 destruct HS as [_ [_ [_ [_ [[L232 L277] [i [Hdec Hleg]]]]]]].
 pose proof (Ed.prim_driven F.rise (En.rs words events) Hc) as [_ D1].
 set (D := phase_driven_state P F.rise (En.rs words events)) in *.
 assert (U140 : read_signal D 140%nat = read_signal (En.rs words events) 140%nat) by exact (ExtendedSVSeqTree.driven_unchanged P F.rise (En.rs words events) 140%nat St.comb_unw_140 ltac:(rewrite Hc; discriminate)).
 assert (U232 : read_signal D 232%nat = read_signal (En.rs words events) 232%nat) by exact (ExtendedSVSeqTree.driven_unchanged P F.rise (En.rs words events) 232%nat St.comb_unw_232 ltac:(rewrite Hc; discriminate)).
 assert (U277 : read_signal D 277%nat = read_signal (En.rs words events) 277%nat) by exact (ExtendedSVSeqTree.driven_unchanged P F.rise (En.rs words events) 277%nat St.comb_unw_277 ltac:(rewrite Hc; discriminate)).
 refine (BzTmplNOne.n_one_word _ D (BzTmplInv.rg (En.rs words events) 140 32) i HD _ _ _ _ Hdec Hleg).
 - unfold BzTmplInv.rg. rewrite U140. reflexivity.
 - rewrite (BzTmplCtlIn.ctlin_153 _ D HD), U232. exact L232.
 - rewrite (BzTmplCtlIn.ctlin_151 _ D HD), U277. exact L277.
 - rewrite (BzTmplCtlIn.ctlin_142 _ D HD), D1, H1. reflexivity.
Qed.
End NState.
End BzTmplNState.
Goal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.
Print Assumptions BzTmplNState.n_one_state.
