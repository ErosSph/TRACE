(** Fixed-target acceptance for cross-CPU proof generation.
    The framework supplies the target; a candidate supplies only its invariant,
    rank, and proofs. Selecting a faithful target is a separate source-binding
    obligation, not something this packaging theorem infers from signal names. *)
From ITree Require Import ITree ITreeFacts.
Require Import Ex.RvCore.FormalSpec
 Ex.External.CPUDesignContract Ex.External.CV32E40PTwoCommitITreeInterface
 coqutil.Map.Interface coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Byte
 riscv.Spec.Decode riscv.Utility.MkMachineWidth riscv.Utility.Utility.
Import CV32E40PTwoCommitITreeInterface.
Local Open Scope itree_scope.

Module CPUDesignTarget.
Section Architecture.
Context {word : Interface.word 32} {BW : Bitwidth 32} {MW : MachineWidth word}.
Context {Registers : map.map Decode.Register word} {Mem : map.map word byte}.

Record Target : Type := {
 target_state : Type;
 target_cycle : target_state -> target_state;
 target_commits : target_state -> CycleCommits;
 target_reset : target_state;
 target_boot : target_state;
 target_isa_initial : FormalSpec.State;
 target_arch_relation : target_state -> FormalSpec.State -> Prop
}.

Record Certificate (t : Target) : Type := {
 certificate_joint : target_state t -> FormalSpec.State -> Prop;
 certificate_rank : target_state t -> FormalSpec.State -> nat;
 certificate_arch_checked : forall s a,
   certificate_joint s a -> target_arch_relation t s a;
 certificate_startup_checked :
   ordered_scheduler (target_cycle t) (target_commits t) (target_reset t) ≈
   ordered_scheduler (target_cycle t) (target_commits t) (target_boot t);
 certificate_initial_checked :
   certificate_joint (target_boot t) (target_isa_initial t);
 certificate_cycle_checked :
   OrderedCycleSafety (target_cycle t) (target_commits t) certificate_joint;
 certificate_progress_checked :
   OrderedWaitDecreases (target_cycle t) (target_commits t)
     certificate_joint certificate_rank
}.

Definition to_design_contract (t : Target) (c : Certificate t) :
 CPUDesignContract.DesignContract :=
 {| CPUDesignContract.cpu_state := target_state t;
    CPUDesignContract.cpu_cycle := target_cycle t;
    CPUDesignContract.cpu_commits := target_commits t;
    CPUDesignContract.cpu_reset := target_reset t;
    CPUDesignContract.cpu_boot := target_boot t;
    CPUDesignContract.cpu_isa_initial := target_isa_initial t;
    CPUDesignContract.cpu_joint := certificate_joint t c;
    CPUDesignContract.cpu_wait_rank := certificate_rank t c;
    CPUDesignContract.cpu_startup_checked := certificate_startup_checked t c;
    CPUDesignContract.cpu_initial_checked := certificate_initial_checked t c;
    CPUDesignContract.cpu_cycle_checked := certificate_cycle_checked t c;
    CPUDesignContract.cpu_progress_checked := certificate_progress_checked t c |}.

(** Migrate an already checked concrete contract to the stricter candidate
    interface without recomputing its RTL or altering any execution field. *)
Definition target_of_checked_contract (c : CPUDesignContract.DesignContract) : Target :=
 {| target_state := CPUDesignContract.cpu_state c;
    target_cycle := CPUDesignContract.cpu_cycle c;
    target_commits := CPUDesignContract.cpu_commits c;
    target_reset := CPUDesignContract.cpu_reset c;
    target_boot := CPUDesignContract.cpu_boot c;
    target_isa_initial := CPUDesignContract.cpu_isa_initial c;
    target_arch_relation := CPUDesignContract.cpu_joint c |}.

Definition certificate_of_checked_contract (c : CPUDesignContract.DesignContract) :
 Certificate (target_of_checked_contract c) :=
 Build_Certificate (target_of_checked_contract c)
   (CPUDesignContract.cpu_joint c) (CPUDesignContract.cpu_wait_rank c)
   (fun _ _ H => H)
   (CPUDesignContract.cpu_startup_checked c)
   (CPUDesignContract.cpu_initial_checked c)
   (CPUDesignContract.cpu_cycle_checked c)
   (CPUDesignContract.cpu_progress_checked c).

Theorem pinned_target_infinite_refinement (t : Target) (c : Certificate t) :
 ordered_scheduler (target_cycle t) (target_commits t) (target_reset t) ≈
 FormalSpec.riscv_itree_with_state (target_isa_initial t).
Proof.
 exact (CPUDesignContract.design_contract_infinite_refinement
   (to_design_contract t c)).
Qed.

Theorem certified_boot_arch_relation (t : Target) (c : Certificate t) :
 target_arch_relation t (target_boot t) (target_isa_initial t).
Proof.
 exact (certificate_arch_checked t c _ _ (certificate_initial_checked t c)).
Qed.

End Architecture.
End CPUDesignTarget.
Print Assumptions CPUDesignTarget.pinned_target_infinite_refinement.
Print Assumptions CPUDesignTarget.certified_boot_arch_relation.
