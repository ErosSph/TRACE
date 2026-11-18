(** Bzeeno goal_arch: the RF bank and the RAM after the cycle against the ISA state advanced by the retiring MEM token
    (tools/cpu_tmpl_bzarch.py; composes BzTmplArchRF, BzTmplIsa, the INV stage relations).
    The statement is the goal of the step module (the definitions below are copied from it by the generator).
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import ZArith List Lia.
From ITree Require Import ITree ITreeFacts.
Require Import Ex.External.CPUGeneratedJointTemplate Ex.External.CPUGeneratedJointITree Ex.External.CPUPipelineQueue Ex.External.CPUPipelineStages
 Ex.External.CPUPipelineStagesContext Ex.External.CPUPipelineMultiRetire Ex.External.CPUPipelineCycle Ex.External.CPUPipelineStaged
 Ex.External.CPUPipelineStagedContext Ex.External.CPUPipelineCycle2 Ex.External.CPUPipelineObligations Ex.External.CPUPipelineObligationsM
 Ex.External.CV32E40PTwoCommitITreeInterface Ex.RvCore.FormalSpec Lang.ExtendedSV Lang.ExtendedSVDependencyCatalog Lang.ExtendedSVBoundedCatalogPhase Lang.ExtendedSVBankOperand
 Ex.External.CPUProgramROM Ex.External.CPUJumpFamilyProgramDomain Ex.External.CPUISARegView
 GeneratedRuntimeInput.ConfiguredAST GeneratedWriteValidityBoot.WriteValidityBoot
 GeneratedClockCycleJoint.CycleJoint GeneratedSeedBoot.FrozenEnvironment
 GeneratedCapturedHistoryBoot.CapturedHistoryBoot TmplBzEnv.BzTmplEnv TmplBzShape.BzTmplShape
 TmplBzRank.BzTmplRank TmplBzDefs.BzTmplDefs TmplBzPhase.BzTmplPhase TmplBzInv.BzTmplInv TmplBzArchRF.BzTmplArchRF TmplBzIsa.BzTmplIsa
 GeneratedJumpITree.JumpITree
 coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte riscv.Utility.Utility riscv.Spec.Decode.
Import ListNotations CPUGeneratedJointTemplate CPUGeneratedJointITree CPUPipelineQueue CPUPipelineStages
 CPUPipelineStagesContext CPUPipelineMultiRetire CPUPipelineCycle CPUPipelineStaged
 CPUPipelineStagedContext CPUPipelineCycle2 CPUPipelineObligations CPUPipelineObligationsM
 CV32E40PTwoCommitITreeInterface ExtendedSV ExtendedSVDependencyCatalog ExtendedSVBoundedCatalogPhase.
Local Open Scope itree_scope.
Local Open Scope Z_scope.
Module BzTmplArch.
Module Ph := TmplBzPhase.BzTmplPhase.BzTmplPhase.
Module En := TmplBzEnv.BzTmplEnv.BzTmplEnv.
Module AR := TmplBzArchRF.BzTmplArchRF.BzTmplArchRF.
Notation Cat := GeneratedDependencyCatalog.Catalog.actual_catalog.
Import BzTmplDefs.
Section Skeleton.
Context {word:Interface.word 32}{BW:Bitwidth 32}{Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}{registers_ok:map.ok Registers}{mem_ok:map.ok Mem}.


Lemma envs_of_front (words:list Z) events frontier :
 BzTmplInv.front_rel words events frontier ->
 Forall (CatalogEvent BzeenoLoadUseJalASTConfigured3122be4a95.bzeeno_load_use_jal_program Cat) events /\ ClockBoundary (En.rs words events) /\ BzTmplInv.Struct (En.rs words events).
Proof. intros [HE [HB [HS _]]]. split; [exact (Forall_impl _ (fun ev H => proj1 H) HE)|]. split; assumption. Qed.

Lemma retiring_eq (words:list Z)(HC:CPUJumpFamilyProgramDomain.check_program words=true) s :
 shape_retiring ((plan_shape words HC) s) (sd_stages (design words HC) s) = opt (BzTmplInv.tok (En.rs words s) 286 287).
Proof. unfold plan_shape. cbn[design sd_stages]. unfold BzTmplInv.stages. cbn zeta.
 destruct (Z.eqb (BzTmplShape.flushD words s) 0); reflexivity. Qed.

Theorem arch_proved (words:list Z)(HC:CPUJumpFamilyProgramDomain.check_program words=true): goal_arch words HC.
Proof.
 unfold goal_arch. intros s retired frontier HP advanced HCh.
 destruct HP as [HA [HF HSR]].
 cbn[design sd_arch sd_front] in HA, HF. 
 destruct (envs_of_front words s frontier HF) as [HE [HB HS]].
 rewrite (retiring_eq words HC s) in HCh.
 cbn[design sd_arch sd_step]. unfold BzTmplInv.arch_rel in *. destruct HA as [HRF HRAM].
 pose proof (AR.rf_cycle words s HE HB (CPUISARegView.isa_view retired) HRF) as [RF1 RF0].
 destruct HS as [_ [HSE [HSM _]]].
 unfold BzTmplInv.tok in HCh.
 destruct (Z.eqb (BzTmplInv.rg (En.rs words s) 286 1) 0) eqn:E286.
 - (* no token at EX/MEM *)
   apply Z.eqb_eq in E286. cbn[opt] in HCh. inversion HCh; subst advanced.
   destruct (HSM E286) as [H283 [H278 H277]].
   unfold BzTmplInv.rg in H283, H278.
   split.
   + exact (RF0 (or_intror H283)).
   + unfold JumpITree.actual_cycle. rewrite <- HRAM. exact (AR.ram_cycle words s HE HB H278).
 - assert (E286n : BzTmplInv.rg (En.rs words s) 286 1 <> 0) by (apply Z.eqb_neq; exact E286).
   cbn[opt] in HCh.
   inversion HCh as [|a t b ts c Heff Hrest]; subst. inversion Hrest; subst.
   cbn[design sd_stages] in HSR. unfold BzTmplInv.stages, BzTmplInv.tok in HSR. cbv zeta in HSR. rewrite E286 in HSR.
   destruct (sr_some_inv _ _ _ _ _ _ _ HSR) as [c [Heff' [HR _]]].
   cbn[design sd_stage] in HR. unfold BzTmplInv.stage_rel in HR.
   cbn[design sd_effect] in Heff, Heff'.
   assert (Hc : c = advanced) by (rewrite Heff in Heff'; congruence). subst c.
   split.
   + eapply BzTmplIsa.rfrel_mem; [exact HC|exact HR|exact Heff|exact RF1|exact RF0].
   + destruct HR as [_ [_ [_ [H278 _]]]]. unfold BzTmplInv.rg in H278. unfold JumpITree.actual_cycle. rewrite <- HRAM. exact (AR.ram_cycle words s HE HB H278).
Qed.
End Skeleton.
End BzTmplArch.
Goal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.
Print Assumptions BzTmplArch.arch_proved.
