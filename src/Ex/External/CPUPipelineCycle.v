(** Generic pipeline cycle theorem (design-independent).

    A design supplies its RTL state type and cycle function, its commit
    observer, a token type with an ISA effect (e.g. the original
    [instruction_effect]), its post-fetch stage tags (oldest first, any number
    of stages) and a physical relation between the RTL state, the retired ISA
    state and the frontier ISA state (RF/PC/ROM/RAM views). If every cycle
    satisfies the LOCAL obligation [CycleObligation] -- the stage tags move in
    one of the [CPUPipelineQueue.Step] shapes, the admitted token's effect
    extends the frontier, the observer reports exactly the retiring token, and
    the physical relation is transported -- then the stage-based joint is an
    [OrderedCycleSafety] invariant, and with a decreasing silent-cycle rank the
    RTL scheduler refines the original ISA ITree. The joint and its queue
    induction are constructed here; nothing about a particular CPU is assumed. *)
From Coq Require Import ZArith List Lia.
From ITree Require Import ITree ITreeFacts.
Require Import Ex.External.CPUGeneratedJointTemplate Ex.External.CPUPipelineQueue
 Ex.External.CV32E40PTwoCommitITreeInterface Ex.RvCore.FormalSpec
 coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte riscv.Utility.Utility.
Import ListNotations CPUGeneratedJointTemplate CPUPipelineQueue CV32E40PTwoCommitITreeInterface.
Local Open Scope itree_scope.

Module CPUPipelineCycle.
(** The pipeline interface a design instantiates. *)
Record PipelineDesign{word:Interface.word 32}{BW:Bitwidth 32}{MW:MachineWidth word}
 {Registers:map.map Decode.Register word}{Mem:map.map word byte}(Runtime Token:Type):Type:={
 pd_step:Runtime ->Runtime;
 pd_commits:Runtime ->CycleCommits;
 pd_effect:Token ->FormalSpec.State ->option FormalSpec.State;
 pd_pc:Token ->Z;
 (** The token effect is one original ISA step at the token's PC. *)
 pd_effect_sound:forall t a b,pd_effect t a=Some b ->
   FormalSpec.run1 a=(Some tt,b) /\pd_pc t=word.unsigned(getPc a);
 (** Post-fetch stage tags, oldest first; any number of stages. *)
 pd_stages:Runtime ->list(option Token);
 (** RTL state, retired ISA state, frontier ISA state. *)
 pd_physical:Runtime ->FormalSpec.State ->FormalSpec.State ->Prop
}.
Arguments pd_step {word BW MW Registers Mem Runtime Token}.
Arguments pd_commits {word BW MW Registers Mem Runtime Token}.
Arguments pd_effect {word BW MW Registers Mem Runtime Token}.
Arguments pd_pc {word BW MW Registers Mem Runtime Token}.
Arguments pd_effect_sound {word BW MW Registers Mem Runtime Token}.
Arguments pd_stages {word BW MW Registers Mem Runtime Token}.
Arguments pd_physical {word BW MW Registers Mem Runtime Token}.

Section Cycle.
Context {word:Interface.word 32}{BW:Bitwidth 32}{MW:MachineWidth word}.
Context {Registers:map.map Decode.Register word}{Mem:map.map word byte}.
Context {Runtime Token:Type}.

Definition pending(d:PipelineDesign Runtime Token)(s:Runtime):list Token:=present(pd_stages d s).
Definition PipelineJoint(d:PipelineDesign Runtime Token)(s:Runtime)(retired:FormalSpec.State):Prop:=
 exists frontier,pd_physical d s retired frontier /\EffectChain(pd_effect d)retired(pending d s)frontier.

Definition observe(d:PipelineDesign Runtime Token)(retiring:list Token):CycleCommits:=match retiring with
 |[]=>SilentCycle|t::_=>OneCommit(pd_pc d t)end.

(** The per-cycle local obligation a design must discharge. *)
Definition CycleObligation(d:PipelineDesign Runtime Token):Prop:=
 forall s retired frontier,pd_physical d s retired frontier ->EffectChain(pd_effect d)retired(pending d s)frontier ->
 exists admitted retiring next_frontier,
  Step(pd_stages d s)admitted(pd_stages d(pd_step d s))retiring /\
  EffectChain(pd_effect d)frontier(opt admitted)next_frontier /\
  pd_commits d s=observe d retiring /\
  (forall advanced,EffectChain(pd_effect d)retired retiring advanced ->pd_physical d(pd_step d s)advanced next_frontier).

Theorem pipeline_cycle_safety(d:PipelineDesign Runtime Token):
 CycleObligation d ->OrderedCycleSafety(pd_step d)(pd_commits d)(PipelineJoint d).
Proof. intros HO s retired[frontier[HP HC]].
 destruct(HO s retired frontier HP HC)as[admitted[retiring[next[HS[HE[HObs HPost]]]]]].
 pose proof(step_queue _ _ _ _ HS)as HQ.
 pose proof(chain_append(pd_effect d)_ _ _ _ _ HC HE)as HW.
 unfold pending in HW;rewrite HQ in HW.
 destruct(chain_split(pd_effect d)retiring retired(present(pd_stages d(pd_step d s)))next HW)as[advanced[HR HRest]].
 pose proof(step_retiring_single _ _ _ _ HS)as HLen.
 rewrite HObs.
 destruct retiring as[|t[|u rest]];cbn in HLen;[|clear HLen|lia].
 - inversion HR;subst;exists next;split;[apply HPost;constructor|exact HRest].
 - inversion HR as[|a t' b ts c HEff HNil];subst;inversion HNil;subst.
   destruct(pd_effect_sound d t retired advanced HEff)as[HRun HPc].
   exists advanced;split.
   + cbn[observe];exact(one_isa_step _ _ _ HRun HPc).
   + exists next;split;[apply HPost;econstructor;[exact HEff|constructor]|exact HRest].
Qed.

Theorem pipeline_infinite_refinement(d:PipelineDesign Runtime Token)(rank:Runtime ->FormalSpec.State ->nat):
 CycleObligation d ->OrderedWaitDecreases(pd_step d)(pd_commits d)(PipelineJoint d)rank ->
 forall s isa,PipelineJoint d s isa ->ordered_scheduler(pd_step d)(pd_commits d)s ≈FormalSpec.riscv_itree_with_state isa.
Proof. intros HO HR;exact(ordered_cycle_safety_and_rank_to_itree(pd_step d)(pd_commits d)(PipelineJoint d)rank
 (pipeline_cycle_safety d HO)HR). Qed.

(** Reset: an empty pipeline with a physical relation at the ISA initial state is a joint. *)
Theorem pipeline_initial(d:PipelineDesign Runtime Token)s isa:pending d s=[] ->pd_physical d s isa isa ->PipelineJoint d s isa.
Proof. intros HE HP;exists isa;split;[exact HP|];rewrite HE;constructor. Qed.
End Cycle.
End CPUPipelineCycle.
Print Assumptions CPUPipelineCycle.pipeline_cycle_safety.
Print Assumptions CPUPipelineCycle.pipeline_infinite_refinement.
Print Assumptions CPUPipelineCycle.pipeline_initial.
