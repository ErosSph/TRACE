(** A reusable graph-certificate route to the fixed-target ITree interface.
    Nodes are CURRENT RTL/ISA state pairs, never promises of future behavior.
    Every edge must be proved about the target's actual cycle and actual run1.
    A finite graph is useful for a periodic program, not a proof about every
    program or all possible states of an unrestricted CPU. *)
From Coq Require Import Arith Lia.
From ITree Require Import ITree ITreeFacts.
Require Import Ex.RvCore.FormalSpec Ex.External.CPUDesignTarget
 Ex.External.CV32E40PTwoCommitITreeInterface
 coqutil.Map.Interface coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Byte
 riscv.Spec.Decode riscv.Utility.MkMachineWidth riscv.Utility.Utility.
Import CPUDesignTarget CV32E40PTwoCommitITreeInterface.
Local Open Scope itree_scope.
Module CPUCheckedCycleGraph.
Section Architecture.
Context {word : Interface.word 32} {BW : Bitwidth 32} {MW : MachineWidth word}.
Context {Registers : map.map Decode.Register word} {Mem : map.map word byte}.

Record Graph (t : Target) (Index : Type) := {
 node_rtl : Index -> target_state t;
 node_isa : Index -> FormalSpec.State;
 node_next : Index -> Index;
 node_wait : Index -> nat;
 graph_rank : target_state t -> FormalSpec.State -> nat;
 graph_rank_nodes : forall i, graph_rank (node_rtl i) (node_isa i) = node_wait i;
 graph_actual_edges : forall i, target_cycle t (node_rtl i) = node_rtl (node_next i);
 graph_isa_edges : forall i,
   match target_commits t (node_rtl i) with
   | SilentCycle => node_isa (node_next i) = node_isa i
   | result => VisibleISASteps result (node_isa i) (node_isa (node_next i))
   end;
 graph_silent_rank : forall i, target_commits t (node_rtl i) = SilentCycle ->
   (node_wait (node_next i) < node_wait i)%nat;
 graph_arch_nodes : forall i, target_arch_relation t (node_rtl i) (node_isa i);
 graph_initial_node : Index;
 graph_boot : target_boot t = node_rtl graph_initial_node;
 graph_initial_isa : target_isa_initial t = node_isa graph_initial_node;
 graph_startup :
   ordered_scheduler (target_cycle t) (target_commits t) (target_reset t) ≈
   ordered_scheduler (target_cycle t) (target_commits t) (target_boot t)
}.

Definition Joint t Index (g : Graph t Index) rtl isa : Prop :=
 exists i, rtl = node_rtl t Index g i /\ isa = node_isa t Index g i.

Theorem graph_cycle_safety t Index (g : Graph t Index) :
 OrderedCycleSafety (target_cycle t) (target_commits t) (Joint t Index g).
Proof.
 intros rtl isa [i [Hr Ha]]. subst rtl isa.
 pose proof (graph_isa_edges t Index g i) as Hisa.
 rewrite (graph_actual_edges t Index g i).
 destruct (target_commits t (node_rtl t Index g i)) eqn:Hcommit.
 - unfold Joint. exists (node_next t Index g i). split; [reflexivity|].
   symmetry. exact Hisa.
 - exists (node_isa t Index g (node_next t Index g i)).
   split; [exact Hisa|]. unfold Joint.
   exists (node_next t Index g i). auto.
 - exists (node_isa t Index g (node_next t Index g i)).
   split; [exact Hisa|]. unfold Joint.
   exists (node_next t Index g i). auto.
Qed.

Theorem graph_progress t Index (g : Graph t Index) :
 OrderedWaitDecreases (target_cycle t) (target_commits t) (Joint t Index g)
   (graph_rank t Index g).
Proof.
 intros rtl isa [i [Hr Ha]] Hsilent. subst rtl isa.
 pose proof (graph_isa_edges t Index g i) as Hisa.
 rewrite Hsilent in Hisa.
 assert (Hpost : graph_rank t Index g
   (target_cycle t (node_rtl t Index g i)) (node_isa t Index g i) =
   node_wait t Index g (node_next t Index g i)).
 { rewrite (graph_actual_edges t Index g i), <- Hisa. apply graph_rank_nodes. }
 rewrite Hpost, graph_rank_nodes.
 apply graph_silent_rank. exact Hsilent.
Qed.

Theorem graph_rejects_silent_self_edge t Index (g : Graph t Index) i :
 node_next t Index g i = i ->
 target_commits t (node_rtl t Index g i) = SilentCycle -> False.
Proof.
 intros Hnext Hsilent.
 pose proof (graph_silent_rank t Index g i Hsilent) as Hrank.
 rewrite Hnext in Hrank. lia.
Qed.

Definition graph_certificate t Index (g : Graph t Index) : Certificate t.
Proof.
 refine {| certificate_joint := Joint t Index g;
           certificate_rank := graph_rank t Index g;
           certificate_startup_checked := graph_startup t Index g;
           certificate_cycle_checked := graph_cycle_safety t Index g;
           certificate_progress_checked := graph_progress t Index g |}.
 - intros rtl isa [i [Hr Ha]]. subst rtl isa. apply graph_arch_nodes.
 - unfold Joint. exists (graph_initial_node t Index g).
   split; [apply graph_boot|apply graph_initial_isa].
Defined.

Theorem graph_infinite_refinement t Index (g : Graph t Index) :
 ordered_scheduler (target_cycle t) (target_commits t) (target_reset t) ≈
 FormalSpec.riscv_itree_with_state (target_isa_initial t).
Proof. exact (pinned_target_infinite_refinement t (graph_certificate t Index g)). Qed.
End Architecture.
End CPUCheckedCycleGraph.
Print Assumptions CPUCheckedCycleGraph.graph_infinite_refinement.
