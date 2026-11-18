(** Context-aware stage-wise obligation (design-independent).

    Same as [CPUPipelineStaged.StagedObligation] except that stage transport
    is [CPUPipelineStagesContext.shape_transport_ctx]: each per-index fact may
    use the token's actual position, its actual cut, and the relations of
    all older stages up to that cut (what operand forwarding needs).
    [staged_ctx_cycle_obligation] derives [CycleObligation], so the ITree
    refinement follows as before. [staged_obligation_ctx_of_plain] shows the
    plain obligation implies this one; designs proved with the plain
    interface (e.g. DarkRISCV) remain valid unchanged. *)
From Coq Require Import ZArith List Lia.
From ITree Require Import ITree ITreeFacts.
Require Import Ex.External.CPUGeneratedJointTemplate Ex.External.CPUPipelineQueue
 Ex.External.CPUPipelineStages Ex.External.CPUPipelineStagesContext
 Ex.External.CPUPipelineCycle Ex.External.CPUPipelineStaged
 Ex.External.CV32E40PTwoCommitITreeInterface Ex.RvCore.FormalSpec
 coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte riscv.Utility.Utility.
Import ListNotations CPUGeneratedJointTemplate CPUPipelineQueue CPUPipelineStages CPUPipelineStagesContext
 CPUPipelineCycle CPUPipelineStaged CV32E40PTwoCommitITreeInterface.
Local Open Scope itree_scope.

Module CPUPipelineStagedContext.
Section StagedContext.
Context {word:Interface.word 32}{BW:Bitwidth 32}{MW:MachineWidth word}.
Context {Registers:map.map Decode.Register word}{Mem:map.map word byte}.
Context {Runtime Token:Type}.

Definition StagedObligationCtx(d:StagedDesign Runtime Token):Prop:=
 forall s retired frontier,staged_physical d s retired frontier->
 exists sh next,
  sd_stages d(sd_step d s)=shape_post sh(sd_stages d s)/\
  shape_transport_ctx(sd_effect d)sh(sd_stage d s)(sd_stage d(sd_step d s))retired(sd_stages d s)/\
  shape_admission(sd_effect d)sh(sd_stage d(sd_step d s))(sd_stages d s)frontier next/\
  sd_commits d s=observe(to_pipeline d)(shape_retiring sh(sd_stages d s))/\
  sd_front d(sd_step d s)next/\
  (forall advanced,EffectChain(sd_effect d)retired(shape_retiring sh(sd_stages d s))advanced->
     sd_arch d(sd_step d s)advanced).

Theorem staged_ctx_cycle_obligation(d:StagedDesign Runtime Token):
 StagedObligationCtx d->CycleObligation(to_pipeline d).
Proof. intros HO s retired frontier HP _.
 destruct(HO s retired frontier HP)as[sh[next[Hpost[HT[HA[HObs[HF HArch]]]]]]].
 destruct HP as[_[_ HS]].
 exists(shape_admitted sh),(shape_retiring sh(sd_stages d s)),next.
 change(pd_stages(to_pipeline d))with(sd_stages d).
 change(pd_step(to_pipeline d))with(sd_step d).
 change(pd_effect(to_pipeline d))with(sd_effect d).
 change(pd_commits(to_pipeline d))with(sd_commits d).
 change(pd_physical(to_pipeline d))with(staged_physical d).
 split;[rewrite Hpost;exact(shape_step_ctx(sd_effect d)sh _ _ _ _ HT)|].
 split.
 { revert HA;unfold shape_admission;destruct(shape_admitted sh)as[t|];intro HA;cbn[opt].
   - destruct HA as[HE _];econstructor;[exact HE|constructor].
   - subst next;constructor. }
 split;[exact HObs|].
 intros advanced HC.
 destruct(shape_stages_ctx(sd_effect d)sh _ _ _ _ _ _ HS HT HA)as[advanced'[HC' HS']].
 pose proof(chain_deterministic(sd_effect d)_ _ _ _ HC HC')as HEq;subst advanced'.
 unfold staged_physical;rewrite Hpost;split;[exact(HArch advanced HC)|split;[exact HF|exact HS']].
Qed.

Theorem staged_obligation_ctx_of_plain(d:StagedDesign Runtime Token):
 StagedObligation d->StagedObligationCtx d.
Proof. intros HO s retired frontier HP.
 destruct(HO s retired frontier HP)as[sh[next[Hpost[HT[HA[HObs[HF HArch]]]]]]].
 exists sh,next;split;[exact Hpost|split;[exact(transport_ctx_of_plain(sd_effect d)sh _ _ retired _ HT)|]].
 exact(conj HA(conj HObs(conj HF HArch))).
Qed.

Theorem staged_ctx_infinite_refinement(d:StagedDesign Runtime Token)(rank:Runtime->FormalSpec.State->nat):
 StagedObligationCtx d->
 OrderedWaitDecreases(sd_step d)(sd_commits d)(PipelineJoint(to_pipeline d))rank->
 forall s isa,PipelineJoint(to_pipeline d)s isa->
 ordered_scheduler(sd_step d)(sd_commits d)s ≈FormalSpec.riscv_itree_with_state isa.
Proof. intros HO HR;exact(pipeline_infinite_refinement(to_pipeline d)rank(staged_ctx_cycle_obligation d HO)HR). Qed.
End StagedContext.
End CPUPipelineStagedContext.
Print Assumptions CPUPipelineStagedContext.staged_ctx_cycle_obligation.
Print Assumptions CPUPipelineStagedContext.staged_obligation_ctx_of_plain.
Print Assumptions CPUPipelineStagedContext.staged_ctx_infinite_refinement.
