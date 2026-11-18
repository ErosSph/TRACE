(** Design-independent packaging of the existing ordered ITree lifting.
    A new CPU must supply proofs about its actual transition and observer.
    The contract does not prescribe signal IDs, pipeline depth, reset style,
    or RF clock edge. It does not infer the CPU invariant from source names.
    A frontend/manifest separately pins these terms to the imported design. *)
From ITree Require Import ITree ITreeFacts.
Require Import Ex.RvCore.FormalSpec
 Ex.External.CV32E40PTwoCommitITreeInterface
 coqutil.Map.Interface coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Byte
 riscv.Spec.Decode riscv.Utility.MkMachineWidth riscv.Utility.Utility.
Import CV32E40PTwoCommitITreeInterface.
Local Open Scope itree_scope.
Module CPUDesignContract.
Section Architecture.
Context {word : Interface.word 32} {BW : Bitwidth 32} {MW : MachineWidth word}.
Context {Registers : map.map Decode.Register word} {Mem : map.map word byte}.

Record DesignContract : Type := {
 cpu_state : Type;
 cpu_cycle : cpu_state -> cpu_state;
 cpu_commits : cpu_state -> CycleCommits;
 cpu_reset : cpu_state;
 cpu_boot : cpu_state;
 cpu_isa_initial : FormalSpec.State;
 cpu_joint : cpu_state -> FormalSpec.State -> Prop;
 cpu_wait_rank : cpu_state -> FormalSpec.State -> nat;
 cpu_startup_checked :
   ordered_scheduler cpu_cycle cpu_commits cpu_reset ≈
   ordered_scheduler cpu_cycle cpu_commits cpu_boot;
 cpu_initial_checked : cpu_joint cpu_boot cpu_isa_initial;
 cpu_cycle_checked : OrderedCycleSafety cpu_cycle cpu_commits cpu_joint;
 cpu_progress_checked :
   OrderedWaitDecreases cpu_cycle cpu_commits cpu_joint cpu_wait_rank
}.

Theorem design_contract_infinite_refinement (c : DesignContract) :
 ordered_scheduler (cpu_cycle c) (cpu_commits c) (cpu_reset c) ≈
 FormalSpec.riscv_itree_with_state (cpu_isa_initial c).
Proof.
 transitivity (ordered_scheduler (cpu_cycle c) (cpu_commits c) (cpu_boot c)).
 - exact (cpu_startup_checked c).
 - eapply ordered_cycle_safety_and_rank_to_itree
     with (Inv := cpu_joint c) (rank := cpu_wait_rank c).
   + exact (cpu_cycle_checked c).
   + exact (cpu_progress_checked c).
   + exact (cpu_initial_checked c).
Qed.
End Architecture.
End CPUDesignContract.
