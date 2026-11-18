(** Multi-retire obligation list (design-independent).

    The [ShapeM] counterpart of [CPUPipelineObligations.CycleObligations]:
    a design gives a cycle plan [plan_shape s : ShapeM] (an old single-retire
    shape, or [SMRetire k adm] for k oldest slots leaving at once) and
    [plan_next s retired frontier]; each conjunct of
    [CPUPipelineCycle2.StagedObligationM] is then a separate field:
    - [obm_shape]: the stage tags move by the planned shape;
    - [obm_bounds]: for [SMRetire k], 1 <= k <= 2 and k <= number of slots;
    - [obm_transport] / [obm_admission]: per-index transport and admission,
      for the base shape or the multi-retire move;
    - [obm_observer]: the observer reports the retiring tokens (0..2);
    - [obm_front] / [obm_arch]: fetch view and architectural view afterwards.
    [obligations_m_staged] assembles them into [StagedObligationM]; the ITree
    refinement follows by [staged_m_infinite_refinement]. *)
From Coq Require Import ZArith List Lia.
From ITree Require Import ITree ITreeFacts.
Require Import Ex.External.CPUGeneratedJointTemplate Ex.External.CPUPipelineQueue
 Ex.External.CPUPipelineStages Ex.External.CPUPipelineStagesContext Ex.External.CPUPipelineMultiRetire
 Ex.External.CPUPipelineCycle Ex.External.CPUPipelineStaged Ex.External.CPUPipelineCycle2
 Ex.External.CV32E40PTwoCommitITreeInterface Ex.RvCore.FormalSpec
 coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte riscv.Utility.Utility.
Import ListNotations CPUGeneratedJointTemplate CPUPipelineQueue CPUPipelineStages CPUPipelineStagesContext
 CPUPipelineMultiRetire CPUPipelineCycle CPUPipelineStaged CPUPipelineCycle2 CV32E40PTwoCommitITreeInterface.
Local Open Scope itree_scope.

Module CPUPipelineObligationsM.
Section ObligationsM.
Context {word:Interface.word 32}{BW:Bitwidth 32}{MW:MachineWidth word}.
Context {Registers:map.map Decode.Register word}{Mem:map.map word byte}.
Context {Runtime Token:Type}.

Definition shapem_bounds(sh:ShapeM(Token:=Token))(old:list(option Token)):Prop:=
 match sh with SMBase _=>True|SMRetire k _=>1<=k<=2/\(k<=length old)%nat end.
Definition shapem_transport(effect:Token->FormalSpec.State->option FormalSpec.State)(sh:ShapeM(Token:=Token))
 (R R':nat->Token->FormalSpec.State->Prop)(retired:FormalSpec.State)(old:list(option Token)):Prop:=
 match sh with
 |SMBase b=>shape_transport_ctx effect b R R' retired old
 |SMRetire k _=>retire_transport effect k R R' retired old end.
Definition shapem_admission(effect:Token->FormalSpec.State->option FormalSpec.State)(sh:ShapeM(Token:=Token))
 (R':nat->Token->FormalSpec.State->Prop)(old:list(option Token))(frontier next:FormalSpec.State):Prop:=
 match sh with
 |SMBase b=>shape_admission effect b R' old frontier next
 |SMRetire _ adm=>retire_admission effect adm R' old frontier next end.

Record CycleObligationsM(d:StagedDesign Runtime Token)
 (plan_shape:Runtime->ShapeM(Token:=Token))
 (plan_next:Runtime->FormalSpec.State->FormalSpec.State->FormalSpec.State):Prop:={
 obm_shape:forall s retired frontier,staged_physical d s retired frontier->
  sd_stages d(sd_step d s)=shapem_post(plan_shape s)(sd_stages d s);
 obm_bounds:forall s retired frontier,staged_physical d s retired frontier->
  shapem_bounds(plan_shape s)(sd_stages d s);
 obm_transport:forall s retired frontier,staged_physical d s retired frontier->
  shapem_transport(sd_effect d)(plan_shape s)(sd_stage d s)(sd_stage d(sd_step d s))retired(sd_stages d s);
 obm_admission:forall s retired frontier,staged_physical d s retired frontier->
  shapem_admission(sd_effect d)(plan_shape s)(sd_stage d(sd_step d s))(sd_stages d s)frontier
   (plan_next s retired frontier);
 obm_observer:forall s retired frontier,staged_physical d s retired frontier->
  sd_commits d s=observe2(to_pipeline d)(shapem_retiring(plan_shape s)(sd_stages d s));
 obm_front:forall s retired frontier,staged_physical d s retired frontier->
  sd_front d(sd_step d s)(plan_next s retired frontier);
 obm_arch:forall s retired frontier,staged_physical d s retired frontier->
  forall advanced,EffectChain(sd_effect d)retired(shapem_retiring(plan_shape s)(sd_stages d s))advanced->
  sd_arch d(sd_step d s)advanced
}.

Theorem obligations_m_staged(d:StagedDesign Runtime Token)plan_shape plan_next:
 CycleObligationsM d plan_shape plan_next->StagedObligationM d.
Proof. intros HO s retired frontier HP.
 exists(plan_shape s),(plan_next s retired frontier).
 pose proof(obm_bounds _ _ _ HO s retired frontier HP)as HB.
 pose proof(obm_transport _ _ _ HO s retired frontier HP)as HT.
 pose proof(obm_admission _ _ _ HO s retired frontier HP)as HA.
 split;[exact(obm_shape _ _ _ HO s retired frontier HP)|].
 split.
 { unfold shapem_bounds,shapem_transport,shapem_admission in *.
   destruct(plan_shape s)as[b|k adm];[exact(conj HT HA)|].
   destruct HB as[HK HL];exact(conj HK(conj HL(conj HT HA))). }
 split;[exact(obm_observer _ _ _ HO s retired frontier HP)|].
 split;[exact(obm_front _ _ _ HO s retired frontier HP)|].
 exact(obm_arch _ _ _ HO s retired frontier HP).
Qed.

Theorem obligations_m_infinite_refinement(d:StagedDesign Runtime Token)plan_shape plan_next
 (rank:Runtime->FormalSpec.State->nat):
 CycleObligationsM d plan_shape plan_next->
 OrderedWaitDecreases(sd_step d)(sd_commits d)(PipelineJoint(to_pipeline d))rank->
 forall s isa,PipelineJoint(to_pipeline d)s isa->
 ordered_scheduler(sd_step d)(sd_commits d)s ≈FormalSpec.riscv_itree_with_state isa.
Proof. intros HO HR;exact(staged_m_infinite_refinement d rank(obligations_m_staged d plan_shape plan_next HO)HR). Qed.
End ObligationsM.
End CPUPipelineObligationsM.
Print Assumptions CPUPipelineObligationsM.obligations_m_staged.
Print Assumptions CPUPipelineObligationsM.obligations_m_infinite_refinement.
