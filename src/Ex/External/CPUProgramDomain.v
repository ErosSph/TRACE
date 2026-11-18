(** ISA-only domains, parameterized by the actual target initial state.
    No ROM padding, RTL behavior or future submission is assumed here. *)
From Coq Require Import ZArith.
Require Import Ex.RvCore.FormalSpec
 Ex.External.CV32E40PTwoCommitITreeInterface
 coqutil.Map.Interface coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Byte
 riscv.Spec.Decode riscv.Utility.MkMachineWidth riscv.Utility.Utility.
Import CV32E40PTwoCommitITreeInterface.
Module CPUProgramDomain.
Section Architecture.
Context {word : Interface.word 32} {BW : Bitwidth 32} {MW : MachineWidth word}.
Context {Registers : map.map Decode.Register word} {Mem : map.map word byte}.

Record Domain (initial : FormalSpec.State) : Type := {
 holds : FormalSpec.State -> Prop;
 initial_holds : holds initial;
 run1_preserves : forall a b, holds a ->
   FormalSpec.run1 a = (Some tt,b) -> holds b
}.

Lemma visible_preserves initial (d : Domain initial) result a b :
 holds initial d a -> VisibleISASteps result a b -> holds initial d b.
Proof.
 intros HA HV. destruct HV as [pc a b HR HP|p q a m b H1 P1 H2 P2].
 - exact (run1_preserves initial d a b HA HR).
 - exact (run1_preserves initial d m b
     (run1_preserves initial d a m HA H1) H2).
Qed.

Section RTL.
Context {S : Type} (step : S -> S) (commits : S -> CycleCommits).
Variable joint : S -> FormalSpec.State -> Prop.
Variable initial : FormalSpec.State.
Variable domain : Domain initial.
Definition WithDomain s a := joint s a /\ holds initial domain a.

(** The hardware obligation may use the current ISA domain. Its postcondition
    need only restore the hardware joint: ISA preservation is reused once. *)
Definition GuardedCycleSafety := forall s a,
 joint s a -> holds initial domain a ->
 match commits s with
 | SilentCycle => joint (step s) a
 | result => exists b, VisibleISASteps result a b /\ joint (step s) b
 end.

Theorem compose_cycle_safety : GuardedCycleSafety ->
 OrderedCycleSafety step commits WithDomain.
Proof.
 intros HC s a [HJ HD]. specialize (HC s a HJ HD).
 unfold WithDomain. destruct (commits s) eqn:HE.
 - split; assumption.
 - destruct HC as [b [HV HPost]]. exists b;split;[exact HV|].
   split;[exact HPost|exact (visible_preserves initial domain _ a b HD HV)].
 - destruct HC as [b [HV HPost]]. exists b;split;[exact HV|].
   split;[exact HPost|exact (visible_preserves initial domain _ a b HD HV)].
Qed.

Theorem compose_progress rank : OrderedWaitDecreases step commits joint rank ->
 OrderedWaitDecreases step commits WithDomain rank.
Proof. intros HP s a [HJ HD] HS. exact (HP s a HJ HS). Qed.

Theorem compose_initial boot : joint boot initial -> WithDomain boot initial.
Proof. intro HJ;split;[exact HJ|exact (initial_holds initial domain)]. Qed.
End RTL.
End Architecture.
End CPUProgramDomain.
Print Assumptions CPUProgramDomain.compose_cycle_safety.
Print Assumptions CPUProgramDomain.compose_progress.
