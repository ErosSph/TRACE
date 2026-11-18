(** Bzeeno D step: shared definitions of the staged design, the plan and the goals (tools/cpu_tmpl_bzarch.py).
    The text of the definitions is copied verbatim from the accepted step module; arch/front/admission prove the goals stated here, and the
    final step module aliases its own definitions to these constants (conversion of the plan matches is expensive otherwise).
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
 TmplBzRank.BzTmplRank TmplBzPhase.BzTmplPhase TmplBzInv.BzTmplInv
 GeneratedJumpITree.JumpITree
 coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte riscv.Utility.Utility riscv.Spec.Decode.
Import ListNotations CPUGeneratedJointTemplate CPUGeneratedJointITree CPUPipelineQueue CPUPipelineStages
 CPUPipelineStagesContext CPUPipelineMultiRetire CPUPipelineCycle CPUPipelineStaged
 CPUPipelineStagedContext CPUPipelineCycle2 CPUPipelineObligations CPUPipelineObligationsM
 CV32E40PTwoCommitITreeInterface ExtendedSV ExtendedSVDependencyCatalog ExtendedSVBoundedCatalogPhase.
Local Open Scope itree_scope.
Local Open Scope Z_scope.
Module BzTmplDefs.
Section Skeleton.
Context {word:Interface.word 32}{BW:Bitwidth 32}{Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}{registers_ok:map.ok Registers}{mem_ok:map.ok Mem}.

Definition design(words:list Z)(HC:CPUJumpFamilyProgramDomain.check_program words=true):StagedDesign(list Event)(Z):={|
 sd_step:=JumpITree.actual_cycle;
 sd_commits:=JumpITree.actual_observer words;
 sd_effect:=checked_pc_effect;
 sd_pc:=fun pc=>pc;
 sd_effect_sound:=checked_pc_effect_sound;
 sd_stages:=BzTmplInv.stages words;
 sd_arch:=BzTmplInv.arch_rel words;
 sd_front:=BzTmplInv.front_rel words;
 sd_stage:=BzTmplInv.stage_rel words|}.
Definition plan_shape(words:list Z)(HC:CPUJumpFamilyProgramDomain.check_program words=true):=(fun events=>if Z.eqb (BzTmplShape.flushD words events) 0 then Advance (Some (BzTmplInv.rg (BzTmplEnv.rs words events) 119 32)) else Advance None).
Definition plan_next(words:list Z)(HC:CPUJumpFamilyProgramDomain.check_program words=true):=(fun (events:list Event) (_:FormalSpec.State) (f:FormalSpec.State)=>if Z.eqb (BzTmplShape.flushD words events) 0 then snd (FormalSpec.run1 f) else f).
Definition goal_shape(words:list Z)(HC:CPUJumpFamilyProgramDomain.check_program words=true):Prop:=
 forall s retired frontier,staged_physical (design words HC) s retired frontier->
  sd_stages (design words HC)(sd_step (design words HC) s)=shape_post((plan_shape words HC) s)(sd_stages (design words HC) s).
Definition goal_transport(words:list Z)(HC:CPUJumpFamilyProgramDomain.check_program words=true):Prop:=
 forall s retired frontier,staged_physical (design words HC) s retired frontier->
  shape_transport_ctx(sd_effect (design words HC))((plan_shape words HC) s)(sd_stage (design words HC) s)(sd_stage (design words HC)(sd_step (design words HC) s))retired(sd_stages (design words HC) s).
Definition goal_admission(words:list Z)(HC:CPUJumpFamilyProgramDomain.check_program words=true):Prop:=
 forall s retired frontier,staged_physical (design words HC) s retired frontier->
  shape_admission(sd_effect (design words HC))((plan_shape words HC) s)(sd_stage (design words HC)(sd_step (design words HC) s))(sd_stages (design words HC) s)frontier((plan_next words HC) s retired frontier).
Definition goal_observer(words:list Z)(HC:CPUJumpFamilyProgramDomain.check_program words=true):Prop:=
 forall s retired frontier,staged_physical (design words HC) s retired frontier->
  sd_commits (design words HC) s=observe(to_pipeline (design words HC))(shape_retiring((plan_shape words HC) s)(sd_stages (design words HC) s)).
Definition goal_front(words:list Z)(HC:CPUJumpFamilyProgramDomain.check_program words=true):Prop:=
 forall s retired frontier,staged_physical (design words HC) s retired frontier->
  sd_front (design words HC)(sd_step (design words HC) s)((plan_next words HC) s retired frontier).
Definition goal_arch(words:list Z)(HC:CPUJumpFamilyProgramDomain.check_program words=true):Prop:=
 forall s retired frontier,staged_physical (design words HC) s retired frontier->
  forall advanced,EffectChain(sd_effect (design words HC))retired(shape_retiring((plan_shape words HC) s)(sd_stages (design words HC) s))advanced->sd_arch (design words HC)(sd_step (design words HC) s)advanced.
Definition goal_rank(words:list Z)(HC:CPUJumpFamilyProgramDomain.check_program words=true):Prop:=
 OrderedWaitDecreases(JumpITree.actual_cycle)(JumpITree.actual_observer words)(PipelineJoint(to_pipeline(design words HC)))((@BzTmplRank.tmpl_rank_ev FormalSpec.State words)).
Definition goal_boot(words:list Z)(HC:CPUJumpFamilyProgramDomain.check_program words=true):Prop:=
 PipelineJoint(to_pipeline(design words HC))([])(JumpITree.initial words).
Definition goal_startup(words:list Z)(HC:CPUJumpFamilyProgramDomain.check_program words=true):Prop:=
 ordered_scheduler(JumpITree.actual_cycle)(JumpITree.actual_observer words)([]) ≈
 ordered_scheduler(JumpITree.actual_cycle)(JumpITree.actual_observer words)([]).



End Skeleton.
End BzTmplDefs.
Goal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.
Print Assumptions BzTmplDefs.design.
Print Assumptions BzTmplDefs.goal_arch.
