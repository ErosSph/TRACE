(** The per-design obligation list (design-independent).

    A design gives a CYCLE PLAN: [plan_shape s] (how the stage tags move in
    the cycle from runtime state [s]) and [plan_next s retired frontier] (the
    frontier ISA state after the cycle). Each obligation below is then a
    separate, small statement that can be proved on its own, by hand or with
    an LLM:
    - [ob_shape]: the stage tags move by the planned shape;
    - [ob_transport]: per-index stage transport, with the token's actual
      position and cut ([shape_transport_ctx]);
    - [ob_admission]: the admitted token (if any) extends the frontier to the
      planned next frontier, and its youngest-stage relation holds;
    - [ob_observer]: the commit observer reports the retiring token;
    - [ob_front]: the fetch view holds after the cycle at the planned frontier;
    - [ob_arch]: the architectural view holds after the cycle at the state
      advanced by the retiring token (e.g. register file via
      [CPURetireTemplate.retire_rf_template]).
    [obligations_ctx] assembles them into [StagedObligationCtx]; the ITree
    refinement follows by [staged_ctx_infinite_refinement]. *)
From Coq Require Import ZArith List Lia.
From ITree Require Import ITree ITreeFacts.
Require Import Ex.External.CPUGeneratedJointTemplate Ex.External.CPUPipelineQueue
 Ex.External.CPUPipelineStages Ex.External.CPUPipelineStagesContext
 Ex.External.CPUPipelineCycle Ex.External.CPUPipelineStaged Ex.External.CPUPipelineStagedContext
 Ex.External.CV32E40PTwoCommitITreeInterface Ex.RvCore.FormalSpec
 coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte riscv.Utility.Utility.
Import ListNotations CPUGeneratedJointTemplate CPUPipelineQueue CPUPipelineStages CPUPipelineStagesContext
 CPUPipelineCycle CPUPipelineStaged CPUPipelineStagedContext CV32E40PTwoCommitITreeInterface.

Local Open Scope itree_scope.

Module CPUPipelineObligations.
Section Obligations.
Context {word:Interface.word 32}{BW:Bitwidth 32}{MW:MachineWidth word}.
Context {Registers:map.map Decode.Register word}{Mem:map.map word byte}.
Context {Runtime Token:Type}.

Record CycleObligations(d:StagedDesign Runtime Token)
 (plan_shape:Runtime->Shape(Token:=Token))
 (plan_next:Runtime->FormalSpec.State->FormalSpec.State->FormalSpec.State):Prop:={
 ob_shape:forall s retired frontier,staged_physical d s retired frontier->
  sd_stages d(sd_step d s)=shape_post(plan_shape s)(sd_stages d s);
 ob_transport:forall s retired frontier,staged_physical d s retired frontier->
  shape_transport_ctx(sd_effect d)(plan_shape s)(sd_stage d s)(sd_stage d(sd_step d s))retired(sd_stages d s);
 ob_admission:forall s retired frontier,staged_physical d s retired frontier->
  shape_admission(sd_effect d)(plan_shape s)(sd_stage d(sd_step d s))(sd_stages d s)frontier(plan_next s retired frontier);
 ob_observer:forall s retired frontier,staged_physical d s retired frontier->
  sd_commits d s=observe(to_pipeline d)(shape_retiring(plan_shape s)(sd_stages d s));
 ob_front:forall s retired frontier,staged_physical d s retired frontier->
  sd_front d(sd_step d s)(plan_next s retired frontier);
 ob_arch:forall s retired frontier,staged_physical d s retired frontier->
  forall advanced,EffectChain(sd_effect d)retired(shape_retiring(plan_shape s)(sd_stages d s))advanced->
  sd_arch d(sd_step d s)advanced
}.

Theorem obligations_ctx(d:StagedDesign Runtime Token)plan_shape plan_next:
 CycleObligations d plan_shape plan_next->StagedObligationCtx d.
Proof. intros HO s retired frontier HP.
 exists(plan_shape s),(plan_next s retired frontier).
 split;[exact(ob_shape _ _ _ HO s retired frontier HP)|].
 split;[exact(ob_transport _ _ _ HO s retired frontier HP)|].
 split;[exact(ob_admission _ _ _ HO s retired frontier HP)|].
 split;[exact(ob_observer _ _ _ HO s retired frontier HP)|].
 split;[exact(ob_front _ _ _ HO s retired frontier HP)|].
 exact(ob_arch _ _ _ HO s retired frontier HP).
Qed.

Theorem obligations_infinite_refinement(d:StagedDesign Runtime Token)plan_shape plan_next
 (rank:Runtime->FormalSpec.State->nat):
 CycleObligations d plan_shape plan_next->
 OrderedWaitDecreases(sd_step d)(sd_commits d)(PipelineJoint(to_pipeline d))rank->
 forall s isa,PipelineJoint(to_pipeline d)s isa->
 ordered_scheduler(sd_step d)(sd_commits d)s ≈FormalSpec.riscv_itree_with_state isa.
Proof. intros HO HR;exact(staged_ctx_infinite_refinement d rank(obligations_ctx d plan_shape plan_next HO)HR). Qed.

(** With no post-fetch stages, transport holds trivially. *)
Theorem transport_no_stages(effect:Token->FormalSpec.State->option FormalSpec.State)sh R R' retired:
 (forall j,sh<>Bubble j)->shape_transport_ctx effect sh R R' retired[].
Proof. intro HB;destruct sh as[a|j|];cbn[shape_transport_ctx];unfold TransportFrom.
 - intros l1 t l2 c HL;destruct l1;discriminate.
 - exfalso;exact(HB j eq_refl).
 - intros l1 t l2 c HL;destruct l1;discriminate.
Qed.
End Obligations.
End CPUPipelineObligations.
Print Assumptions CPUPipelineObligations.obligations_ctx.
Print Assumptions CPUPipelineObligations.obligations_infinite_refinement.
Print Assumptions CPUPipelineObligations.transport_no_stages.
