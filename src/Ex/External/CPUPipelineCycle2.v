(** Two-commit pipeline cycle theorem (design-independent).

    Extends [CPUPipelineCycle] to pipelines that retire up to TWO tokens in
    one cycle (Codex's [CycleCommits] has [TwoCommits]):
    - [StepM]: the stage tags move either by an old [Step] or by
      [CPUPipelineMultiRetire.retire_post k];
    - [observe2]: 0 / 1 / 2 retiring tokens give [SilentCycle] / [OneCommit] /
      [TwoCommits] of their PCs, oldest first;
    - [CycleObligation2] -> [OrderedCycleSafety] -> infinite ITree, building
      the two-step ISA trace ([two_isa_steps]) when two tokens retire.
    Staged level: [ShapeM] (multi-retire move or any old shape) and
    [StagedObligationM] -> [CycleObligation2], with context-aware transport.
    Single-retire designs are the special case [ShapeM = SMBase _]. *)
From Coq Require Import ZArith List Lia.
From ITree Require Import ITree ITreeFacts.
Require Import Ex.External.CPUGeneratedJointTemplate Ex.External.CPUPipelineQueue
 Ex.External.CPUPipelineStages Ex.External.CPUPipelineStagesContext Ex.External.CPUPipelineMultiRetire
 Ex.External.CPUPipelineCycle Ex.External.CPUPipelineStaged
 Ex.External.CV32E40PTwoCommitITreeInterface Ex.RvCore.FormalSpec
 coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte riscv.Utility.Utility.
Import ListNotations CPUGeneratedJointTemplate CPUPipelineQueue CPUPipelineStages CPUPipelineStagesContext
 CPUPipelineMultiRetire CPUPipelineCycle CPUPipelineStaged CV32E40PTwoCommitITreeInterface.
Local Open Scope itree_scope.

Module CPUPipelineCycle2.
Section Cycle2.
Context {word:Interface.word 32}{BW:Bitwidth 32}{MW:MachineWidth word}.
Context {Registers:map.map Decode.Register word}{Mem:map.map word byte}.
Context {Runtime Token:Type}.

Inductive StepM:list(option Token)->option Token->list(option Token)->list Token->Prop:=
| stepm_base:forall old adm post ret,Step old adm post ret->StepM old adm post ret
| stepm_retire:forall k old adm,1<=k<=length old->StepM old adm(retire_post k adm old)(retire_retiring k old).

Theorem stepm_queue(old:list(option Token))(adm:option Token)(post:list(option Token))(ret:list Token):
 StepM old adm post ret->present old++opt adm=ret++present post.
Proof. intro H;destruct H as[old adm post ret HS|k old adm HK];[exact(step_queue _ _ _ _ HS)|exact(retire_queue k adm old)]. Qed.

Definition observe2(d:PipelineDesign Runtime Token)(retiring:list Token):CycleCommits:=
 match retiring with
 |[]=>SilentCycle|[t]=>OneCommit(pd_pc d t)|t::u::_=>TwoCommits(pd_pc d t)(pd_pc d u) end.

Definition CycleObligation2(d:PipelineDesign Runtime Token):Prop:=
 forall s retired frontier,pd_physical d s retired frontier->EffectChain(pd_effect d)retired(pending d s)frontier->
 exists admitted retiring next_frontier,
  StepM(pd_stages d s)admitted(pd_stages d(pd_step d s))retiring/\
  (length retiring<=2)%nat/\
  EffectChain(pd_effect d)frontier(opt admitted)next_frontier/\
  pd_commits d s=observe2 d retiring/\
  (forall advanced,EffectChain(pd_effect d)retired retiring advanced->pd_physical d(pd_step d s)advanced next_frontier).

Theorem pipeline2_cycle_safety(d:PipelineDesign Runtime Token):
 CycleObligation2 d->OrderedCycleSafety(pd_step d)(pd_commits d)(PipelineJoint d).
Proof. intros HO s retired[frontier[HP HC]].
 destruct(HO s retired frontier HP HC)as[admitted[retiring[next[HS[HLen[HE[HObs HPost]]]]]]].
 pose proof(stepm_queue _ _ _ _ HS)as HQ.
 pose proof(chain_append(pd_effect d)_ _ _ _ _ HC HE)as HW.
 unfold pending in HW;rewrite HQ in HW.
 destruct(chain_split(pd_effect d)retiring retired(present(pd_stages d(pd_step d s)))next HW)as[advanced[HR HRest]].
 rewrite HObs.
 destruct retiring as[|t[|u[|w rest]]];cbn in HLen;[| | |lia].
 - inversion HR;subst;exists next;split;[apply HPost;constructor|exact HRest].
 - inversion HR as[|a t' b ts c HEff HNil];subst;inversion HNil;subst.
   destruct(pd_effect_sound d t retired advanced HEff)as[HRun HPc].
   exists advanced;split.
   + cbn[observe2];exact(one_isa_step _ _ _ HRun HPc).
   + exists next;split;[apply HPost;econstructor;[exact HEff|constructor]|exact HRest].
 - inversion HR as[|a t' m ts c HE1 HN1];subst.
   inversion HN1 as[|a' u' b ts' c' HE2 HN2];subst;inversion HN2;subst.
   destruct(pd_effect_sound d t retired m HE1)as[HRun1 HPc1].
   destruct(pd_effect_sound d u m advanced HE2)as[HRun2 HPc2].
   exists advanced;split.
   + cbn[observe2];exact(two_isa_steps _ _ _ _ _ HRun1 HPc1 HRun2 HPc2).
   + exists next;split;[apply HPost;econstructor;[exact HE1|econstructor;[exact HE2|constructor]]|exact HRest].
Qed.

Theorem pipeline2_infinite_refinement(d:PipelineDesign Runtime Token)(rank:Runtime->FormalSpec.State->nat):
 CycleObligation2 d->OrderedWaitDecreases(pd_step d)(pd_commits d)(PipelineJoint d)rank->
 forall s isa,PipelineJoint d s isa->ordered_scheduler(pd_step d)(pd_commits d)s ≈FormalSpec.riscv_itree_with_state isa.
Proof. intros HO HR;exact(ordered_cycle_safety_and_rank_to_itree(pd_step d)(pd_commits d)(PipelineJoint d)rank
 (pipeline2_cycle_safety d HO)HR). Qed.

(** Staged level. *)
Inductive ShapeM:=SMBase(sh:Shape(Token:=Token))|SMRetire(k:nat)(adm:option Token).
Definition shapem_post(sh:ShapeM)(old:list(option Token)):list(option Token):=
 match sh with SMBase b=>shape_post b old|SMRetire k adm=>retire_post k adm old end.
Definition shapem_retiring(sh:ShapeM)(old:list(option Token)):list Token:=
 match sh with SMBase b=>shape_retiring b old|SMRetire k _=>retire_retiring k old end.
Definition shapem_admitted(sh:ShapeM):option Token:=
 match sh with SMBase b=>shape_admitted b|SMRetire _ adm=>adm end.

Definition StagedObligationM(d:StagedDesign Runtime Token):Prop:=
 forall s retired frontier,staged_physical d s retired frontier->
 exists sh next,
  sd_stages d(sd_step d s)=shapem_post sh(sd_stages d s)/\
  match sh with
  |SMBase b=>shape_transport_ctx(sd_effect d)b(sd_stage d s)(sd_stage d(sd_step d s))retired(sd_stages d s)/\
     shape_admission(sd_effect d)b(sd_stage d(sd_step d s))(sd_stages d s)frontier next
  |SMRetire k adm=>1<=k<=2/\(k<=length(sd_stages d s))%nat/\
     retire_transport(sd_effect d)k(sd_stage d s)(sd_stage d(sd_step d s))retired(sd_stages d s)/\
     retire_admission(sd_effect d)adm(sd_stage d(sd_step d s))(sd_stages d s)frontier next end/\
  sd_commits d s=observe2(to_pipeline d)(shapem_retiring sh(sd_stages d s))/\
  sd_front d(sd_step d s)next/\
  (forall advanced,EffectChain(sd_effect d)retired(shapem_retiring sh(sd_stages d s))advanced->
     sd_arch d(sd_step d s)advanced).

Theorem staged_m_cycle_obligation(d:StagedDesign Runtime Token):
 StagedObligationM d->CycleObligation2(to_pipeline d).
Proof. intros HO s retired frontier HP _.
 destruct(HO s retired frontier HP)as[sh[next[Hpost[HT[HObs[HF HArch]]]]]].
 destruct HP as[_[_ HS]].
 exists(shapem_admitted sh),(shapem_retiring sh(sd_stages d s)),next.
 change(pd_stages(to_pipeline d))with(sd_stages d).
 change(pd_step(to_pipeline d))with(sd_step d).
 change(pd_effect(to_pipeline d))with(sd_effect d).
 change(pd_commits(to_pipeline d))with(sd_commits d).
 change(pd_physical(to_pipeline d))with(staged_physical d).
 rewrite Hpost.
 assert(HMove:exists advanced,EffectChain(sd_effect d)retired(shapem_retiring sh(sd_stages d s))advanced/\
   StagesRel(sd_effect d)(sd_stage d(sd_step d s))0 advanced(shapem_post sh(sd_stages d s))next).
 { destruct sh as[b|k adm];cbn[shapem_retiring shapem_post].
   - destruct HT as[HT HA];exact(shape_stages_ctx _ b _ _ _ _ _ _ HS HT HA).
   - destruct HT as[HK[HKL[HT HA]]];exact(retire_stages _ k adm _ _ _ _ _ _(conj(proj1 HK)HKL)HS HT HA). }
 split.
 { destruct sh as[b|k adm];cbn[shapem_admitted shapem_post shapem_retiring].
   - apply stepm_base;destruct HT as[HT _];exact(shape_step_ctx _ b _ _ _ _ HT).
   - apply stepm_retire;destruct HT as[HK[HKL _]];lia. }
 split.
 { destruct sh as[b|k adm];cbn[shapem_retiring].
   - destruct HT as[HT _];pose proof(step_retiring_single _ _ _ _(shape_step_ctx _ b _ _ _ _ HT));lia.
   - destruct HT as[HK _];pose proof(retire_retiring_length k(sd_stages d s));lia. }
 split.
 { destruct sh as[b|k adm];cbn[shapem_admitted].
   - destruct HT as[_ HA];revert HA;unfold shape_admission;destruct(shape_admitted b)as[t|];intro HA;cbn[opt].
     + destruct HA as[HE _];econstructor;[exact HE|constructor].
     + subst next;constructor.
   - destruct HT as[_[_[_ HA]]];revert HA;unfold retire_admission;destruct adm as[t|];intro HA;cbn[opt].
     + destruct HA as[HE _];econstructor;[exact HE|constructor].
     + subst next;constructor. }
 split;[exact HObs|].
 intros advanced HC.
 destruct HMove as[advanced'[HC' HS']].
 pose proof(chain_deterministic(sd_effect d)_ _ _ _ HC HC')as HEq;subst advanced'.
 unfold staged_physical;rewrite Hpost;split;[exact(HArch advanced HC)|split;[exact HF|exact HS']].
Qed.

Theorem staged_m_infinite_refinement(d:StagedDesign Runtime Token)(rank:Runtime->FormalSpec.State->nat):
 StagedObligationM d->
 OrderedWaitDecreases(sd_step d)(sd_commits d)(PipelineJoint(to_pipeline d))rank->
 forall s isa,PipelineJoint(to_pipeline d)s isa->
 ordered_scheduler(sd_step d)(sd_commits d)s ≈FormalSpec.riscv_itree_with_state isa.
Proof. intros HO HR;exact(pipeline2_infinite_refinement(to_pipeline d)rank(staged_m_cycle_obligation d HO)HR). Qed.
End Cycle2.
End CPUPipelineCycle2.
Print Assumptions CPUPipelineCycle2.stepm_queue.
Print Assumptions CPUPipelineCycle2.pipeline2_cycle_safety.
Print Assumptions CPUPipelineCycle2.pipeline2_infinite_refinement.
Print Assumptions CPUPipelineCycle2.staged_m_cycle_obligation.
Print Assumptions CPUPipelineCycle2.staged_m_infinite_refinement.
