(** Stage-wise obligations for the generic pipeline cycle theorem
    (design-independent).

    A design's physical relation is split into three generic parts:
    - [sd_arch]: the architectural view (register file, data memory) matches
      the RETIRED ISA state;
    - [sd_front]: the fetch view (next PC, instruction source) matches the
      FRONTIER ISA state;
    - [sd_stage s k t cut]: stage k's payload in RTL state s matches token t
      at its cut (operands, ALU result, write port, ...).
    [StagedObligation] asks, per cycle, only for local facts: which shape the
    stage tags take, per-index stage transport, the admitted token's effect
    and stage relation, the observer, the new fetch view, and the
    architectural update by the retiring token. [staged_cycle_obligation]
    derives Codex-style [CycleObligation] from them, so the ITree refinement
    follows from [CPUPipelineCycle.pipeline_infinite_refinement]. *)
From Coq Require Import ZArith List Lia.
From ITree Require Import ITree ITreeFacts.
Require Import Ex.External.CPUGeneratedJointTemplate Ex.External.CPUPipelineQueue
 Ex.External.CPUPipelineStages Ex.External.CPUPipelineCycle
 Ex.External.CV32E40PTwoCommitITreeInterface Ex.RvCore.FormalSpec
 coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte riscv.Utility.Utility.
Import ListNotations CPUGeneratedJointTemplate CPUPipelineQueue CPUPipelineStages CPUPipelineCycle
 CV32E40PTwoCommitITreeInterface.
Local Open Scope itree_scope.

Module CPUPipelineStaged.
Record StagedDesign{word:Interface.word 32}{BW:Bitwidth 32}{MW:MachineWidth word}
 {Registers:map.map Decode.Register word}{Mem:map.map word byte}(Runtime Token:Type):Type:={
 sd_step:Runtime->Runtime;
 sd_commits:Runtime->CycleCommits;
 sd_effect:Token->FormalSpec.State->option FormalSpec.State;
 sd_pc:Token->Z;
 sd_effect_sound:forall t a b,sd_effect t a=Some b->
   FormalSpec.run1 a=(Some tt,b)/\sd_pc t=word.unsigned(getPc a);
 sd_stages:Runtime->list(option Token);
 sd_arch:Runtime->FormalSpec.State->Prop;
 sd_front:Runtime->FormalSpec.State->Prop;
 sd_stage:Runtime->nat->Token->FormalSpec.State->Prop
}.
Arguments sd_step {word BW MW Registers Mem Runtime Token}.
Arguments sd_commits {word BW MW Registers Mem Runtime Token}.
Arguments sd_effect {word BW MW Registers Mem Runtime Token}.
Arguments sd_pc {word BW MW Registers Mem Runtime Token}.
Arguments sd_effect_sound {word BW MW Registers Mem Runtime Token}.
Arguments sd_stages {word BW MW Registers Mem Runtime Token}.
Arguments sd_arch {word BW MW Registers Mem Runtime Token}.
Arguments sd_front {word BW MW Registers Mem Runtime Token}.
Arguments sd_stage {word BW MW Registers Mem Runtime Token}.

Section Staged.
Context {word:Interface.word 32}{BW:Bitwidth 32}{MW:MachineWidth word}.
Context {Registers:map.map Decode.Register word}{Mem:map.map word byte}.
Context {Runtime Token:Type}.

Definition staged_physical(d:StagedDesign Runtime Token)(s:Runtime)(retired frontier:FormalSpec.State):Prop:=
 sd_arch d s retired/\sd_front d s frontier/\
 StagesRel(sd_effect d)(sd_stage d s)0 retired(sd_stages d s)frontier.

Definition to_pipeline(d:StagedDesign Runtime Token):PipelineDesign Runtime Token:={|
 pd_step:=sd_step d;pd_commits:=sd_commits d;pd_effect:=sd_effect d;pd_pc:=sd_pc d;
 pd_effect_sound:=sd_effect_sound d;pd_stages:=sd_stages d;pd_physical:=staged_physical d|}.

(** The per-cycle local facts a design proves. *)
Definition StagedObligation(d:StagedDesign Runtime Token):Prop:=
 forall s retired frontier,staged_physical d s retired frontier->
 exists sh next,
  sd_stages d(sd_step d s)=shape_post sh(sd_stages d s)/\
  shape_transport sh(sd_stage d s)(sd_stage d(sd_step d s))(sd_stages d s)/\
  shape_admission(sd_effect d)sh(sd_stage d(sd_step d s))(sd_stages d s)frontier next/\
  sd_commits d s=observe(to_pipeline d)(shape_retiring sh(sd_stages d s))/\
  sd_front d(sd_step d s)next/\
  (forall advanced,EffectChain(sd_effect d)retired(shape_retiring sh(sd_stages d s))advanced->
     sd_arch d(sd_step d s)advanced).

Theorem staged_cycle_obligation(d:StagedDesign Runtime Token):
 StagedObligation d->CycleObligation(to_pipeline d).
Proof. intros HO s retired frontier HP _.
 destruct(HO s retired frontier HP)as[sh[next[Hpost[HT[HA[HObs[HF HArch]]]]]]].
 destruct HP as[_[_ HS]].
 exists(shape_admitted sh),(shape_retiring sh(sd_stages d s)),next.
 change(pd_stages(to_pipeline d))with(sd_stages d).
 change(pd_step(to_pipeline d))with(sd_step d).
 change(pd_effect(to_pipeline d))with(sd_effect d).
 change(pd_commits(to_pipeline d))with(sd_commits d).
 change(pd_physical(to_pipeline d))with(staged_physical d).
 split;[rewrite Hpost;exact(shape_step sh _ _ _ HT)|].
 split.
 { revert HA;unfold shape_admission;destruct(shape_admitted sh)as[t|];intro HA;cbn[opt].
   - destruct HA as[HE _];econstructor;[exact HE|constructor].
   - subst next;constructor. }
 split;[exact HObs|].
 intros advanced HC.
 destruct(shape_stages(sd_effect d)sh _ _ _ _ _ _ HS HT HA)as[advanced'[HC' HS']].
 pose proof(chain_deterministic(sd_effect d)_ _ _ _ HC HC')as HEq;subst advanced'.
 unfold staged_physical;rewrite Hpost;split;[exact(HArch advanced HC)|split;[exact HF|exact HS']].
Qed.

Theorem staged_infinite_refinement(d:StagedDesign Runtime Token)(rank:Runtime->FormalSpec.State->nat):
 StagedObligation d->
 OrderedWaitDecreases(sd_step d)(sd_commits d)(PipelineJoint(to_pipeline d))rank->
 forall s isa,PipelineJoint(to_pipeline d)s isa->
 ordered_scheduler(sd_step d)(sd_commits d)s ≈FormalSpec.riscv_itree_with_state isa.
Proof. intros HO HR;exact(pipeline_infinite_refinement(to_pipeline d)rank(staged_cycle_obligation d HO)HR). Qed.

(** Reset: all stages empty, architectural and fetch views at the ISA initial state. *)
Theorem staged_initial(d:StagedDesign Runtime Token)(s:Runtime)(isa:FormalSpec.State)(n:nat):
 sd_stages d s=repeat None n->sd_arch d s isa->sd_front d s isa->PipelineJoint(to_pipeline d)s isa.
Proof. intros HE HA HF;exists isa;split.
 - change(pd_physical(to_pipeline d))with(staged_physical d).
   unfold staged_physical;rewrite HE;split;[exact HA|split;[exact HF|apply stages_empty]].
 - change(pending(to_pipeline d)s)with(present(sd_stages d s)).
   rewrite HE;exact(stages_chain(sd_effect d)_ _ _ _ _(stages_empty(sd_effect d)(sd_stage d s)0 isa n)).
Qed.
End Staged.
End CPUPipelineStaged.
Print Assumptions CPUPipelineStaged.staged_cycle_obligation.
Print Assumptions CPUPipelineStaged.staged_infinite_refinement.
Print Assumptions CPUPipelineStaged.staged_initial.
