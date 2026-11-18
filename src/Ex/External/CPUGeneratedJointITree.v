(** Mainline ITree lifting of the NEW generated pending-effect invariant.
    Local transfer, physical architecture, reset and progress are explicit
    generation obligations; no existing CPU global invariant is imported. *)
From Coq Require Import List ZArith.
From ITree Require Import ITree ITreeFacts.
Require Import Ex.RvCore.FormalSpec Ex.External.CPUGeneratedJointTemplate
 Ex.External.CPUGeneratedProgress Ex.External.CPUDesignTarget Ex.External.CV32E40PTwoCommitITreeInterface
 coqutil.Map.Interface coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Byte
 riscv.Spec.Decode riscv.Utility.MkMachineWidth riscv.Utility.Utility.
Import CPUGeneratedJointTemplate CV32E40PTwoCommitITreeInterface ListNotations.
Local Open Scope itree_scope.
Module CPUGeneratedJointITree.
Section Architecture.
Context {word : Interface.word 32} {BW : Bitwidth 32} {MW : MachineWidth word}.
Context {Registers : map.map Decode.Register word} {Mem : map.map word byte}.

Definition checked_pc_effect (pc : Z) (a : FormalSpec.State) : option FormalSpec.State :=
 if Z.eqb pc (word.unsigned (getPc a)) then
   let '(result,b) := FormalSpec.run1 a in
   match result with Some tt => Some b | None => None end
 else None.

Lemma checked_pc_effect_sound pc a b :
 checked_pc_effect pc a = Some b ->
 FormalSpec.run1 a = (Some tt,b) /\ pc = word.unsigned (getPc a).
Proof.
 unfold checked_pc_effect.
 destruct (Z.eqb pc (word.unsigned (getPc a))) eqn:HP; [|discriminate].
 apply Z.eqb_eq in HP.
 destruct (FormalSpec.run1 a) as [[[]|] next] eqn:HR; [|discriminate].
 intro H; inversion H; subst; auto.
Qed.

Definition committed_pcs (result : CycleCommits) : list Z :=
 match result with
 | SilentCycle => [] | OneCommit pc => [pc] | TwoCommits p q => [p;q]
 end.

Lemma checked_chain_observation result a b :
 EffectChain checked_pc_effect a (committed_pcs result) b ->
 match result with
 | SilentCycle => b = a
 | visible => VisibleISASteps visible a b
 end.
Proof.
 destruct result as [|pc|older younger]; cbn [committed_pcs]; intros H.
 - inversion H; reflexivity.
 - inversion H as [|a0 pc0 middle ts final HE HT]; subst.
   inversion HT; subst.
   apply checked_pc_effect_sound in HE as [HR HP].
   constructor; assumption.
 - inversion H as [|a0 pc0 middle ts final HE HT]; subst.
   inversion HT as [|m0 pc1 next rest final0 HE2 HT2]; subst.
   inversion HT2; subst.
   apply checked_pc_effect_sound in HE as [HR HP].
   apply checked_pc_effect_sound in HE2 as [HR2 HP2].
   econstructor; eassumption.
Qed.

Section PinnedTarget.
Variable target : CPUDesignTarget.Target.
Variable pending : CPUDesignTarget.target_state target -> list Z.
Variable Physical : CPUDesignTarget.target_state target ->
 FormalSpec.State -> FormalSpec.State -> Prop.

Definition GeneratedJoint := Joint checked_pc_effect pending Physical.

(** The retiring prefix is fixed by the target's ORIGINAL observer. A local
    checker must prove this queue operation and physical-state transfer;
    it cannot replace the observer or pick a different global invariant. *)
Definition LocalCycleTransfers : Prop :=
 forall s retired frontier, Physical s retired frontier ->
 EffectChain checked_pc_effect retired (pending s) frontier ->
 exists kept accepted_tail next_frontier,
 QueueTransfer checked_pc_effect pending Physical s
   (CPUDesignTarget.target_cycle target s) retired frontier
   (committed_pcs (CPUDesignTarget.target_commits target s))
   kept accepted_tail next_frontier.

Definition LocalStreamingTransfers : Prop :=
 forall s retired frontier, Physical s retired frontier ->
 EffectChain checked_pc_effect retired (pending s) frontier ->
 exists admitted next_frontier,
 StreamingTransfer checked_pc_effect pending Physical s
   (CPUDesignTarget.target_cycle target s) retired frontier
   (committed_pcs (CPUDesignTarget.target_commits target s)) admitted next_frontier.

Theorem generated_ordered_cycle_safety : LocalCycleTransfers ->
 OrderedCycleSafety (CPUDesignTarget.target_cycle target)
   (CPUDesignTarget.target_commits target) GeneratedJoint.
Proof.
 intros Hlocal s retired Hjoint.
 destruct (joint_cycle checked_pc_effect pending Physical
   (CPUDesignTarget.target_cycle target)
   (fun s => committed_pcs (CPUDesignTarget.target_commits target s))
   Hlocal s retired Hjoint) as [advanced [Hret Hpost]].
 pose proof (checked_chain_observation
   (CPUDesignTarget.target_commits target s) retired advanced Hret) as Hobs.
 destruct (CPUDesignTarget.target_commits target s).
 - subst advanced; exact Hpost.
 - exists advanced; auto.
 - exists advanced; auto.
Qed.

Theorem generated_streaming_cycle_safety : LocalStreamingTransfers ->
 OrderedCycleSafety (CPUDesignTarget.target_cycle target)
   (CPUDesignTarget.target_commits target) GeneratedJoint.
Proof.
 intros Hlocal s retired Hjoint.
 destruct (streaming_joint_cycle checked_pc_effect pending Physical
   (CPUDesignTarget.target_cycle target)
   (fun s => committed_pcs (CPUDesignTarget.target_commits target s))
   Hlocal s retired Hjoint) as [advanced [Hret Hpost]].
 pose proof (checked_chain_observation
   (CPUDesignTarget.target_commits target s) retired advanced Hret) as Hobs.
 destruct (CPUDesignTarget.target_commits target s).
 - subst advanced; exact Hpost.
 - exists advanced; auto.
 - exists advanced; auto.
Qed.

(** Event equivalence alone must not be mistaken for RF/memory agreement.
    This independent finite-prefix corollary keeps the physical architecture
    relation at EVERY number of actual target cycles, including silent ones. *)
Fixpoint cycle_after (n : nat) (s : CPUDesignTarget.target_state target) :=
 match n with
 | O => s
 | S remaining => cycle_after remaining (CPUDesignTarget.target_cycle target s)
 end.

Fixpoint cycle_pc_prefix (n : nat) (s : CPUDesignTarget.target_state target) : list Z :=
 match n with
 | O => []
 | S remaining =>
   committed_pcs (CPUDesignTarget.target_commits target s) ++
   cycle_pc_prefix remaining (CPUDesignTarget.target_cycle target s)
 end.

Theorem generated_finite_architecture
 (Hlocal : LocalCycleTransfers)
 (Hphysical : forall s retired frontier, Physical s retired frontier ->
   CPUDesignTarget.target_arch_relation target s retired) :
 forall n s retired, GeneratedJoint s retired ->
 exists advanced,
   EffectChain checked_pc_effect retired (cycle_pc_prefix n s) advanced /\
   GeneratedJoint (cycle_after n s) advanced /\
   CPUDesignTarget.target_arch_relation target (cycle_after n s) advanced.
Proof.
 induction n as [|n IH]; intros s retired Hjoint.
 - exists retired; split; [constructor|]. split; [exact Hjoint|].
   exact (joint_architecture checked_pc_effect pending Physical
     (CPUDesignTarget.target_arch_relation target) Hphysical s retired Hjoint).
 - destruct (joint_cycle checked_pc_effect pending Physical
     (CPUDesignTarget.target_cycle target)
     (fun s => committed_pcs (CPUDesignTarget.target_commits target s))
     Hlocal s retired Hjoint) as [middle [Hfirst Hmiddle]].
   destruct (IH (CPUDesignTarget.target_cycle target s) middle Hmiddle)
     as [advanced [Hrest [Hpost Harch]]].
   exists advanced; split.
   + cbn [cycle_pc_prefix]. eapply chain_append; eassumption.
   + cbn [cycle_after]. auto.
Qed.

Definition generated_search_rank (fuel : nat)
 (s : CPUDesignTarget.target_state target) (_ : FormalSpec.State) : nat :=
 CPUGeneratedProgress.CPUGeneratedProgress.search_rank
   (CPUDesignTarget.target_cycle target) (CPUDesignTarget.target_commits target) fuel s.

Theorem generated_search_wait_decreases fuel :
 CPUGeneratedProgress.CPUGeneratedProgress.BoundedProgress
   (CPUDesignTarget.target_cycle target) (CPUDesignTarget.target_commits target)
   fuel GeneratedJoint ->
 OrderedWaitDecreases (CPUDesignTarget.target_cycle target)
   (CPUDesignTarget.target_commits target) GeneratedJoint (generated_search_rank fuel).
Proof.
 exact (CPUGeneratedProgress.CPUGeneratedProgress.bounded_progress_rank
   (CPUDesignTarget.target_cycle target) (CPUDesignTarget.target_commits target)
   fuel GeneratedJoint).
Qed.

Definition generated_certificate
 (rank : CPUDesignTarget.target_state target -> FormalSpec.State -> nat)
 (Hphysical : forall s retired frontier, Physical s retired frontier ->
   CPUDesignTarget.target_arch_relation target s retired)
 (Hstartup : ordered_scheduler (CPUDesignTarget.target_cycle target)
   (CPUDesignTarget.target_commits target) (CPUDesignTarget.target_reset target) ≈
   ordered_scheduler (CPUDesignTarget.target_cycle target)
   (CPUDesignTarget.target_commits target) (CPUDesignTarget.target_boot target))
 (Hempty : pending (CPUDesignTarget.target_boot target) = [])
 (Hboot : Physical (CPUDesignTarget.target_boot target)
   (CPUDesignTarget.target_isa_initial target) (CPUDesignTarget.target_isa_initial target))
 (Hlocal : LocalCycleTransfers)
 (Hrank : OrderedWaitDecreases (CPUDesignTarget.target_cycle target)
   (CPUDesignTarget.target_commits target) GeneratedJoint rank) :
 CPUDesignTarget.Certificate target.
Proof.
 refine {| CPUDesignTarget.certificate_joint := GeneratedJoint;
   CPUDesignTarget.certificate_rank := rank;
   CPUDesignTarget.certificate_arch_checked := _;
   CPUDesignTarget.certificate_startup_checked := Hstartup;
   CPUDesignTarget.certificate_initial_checked := _;
   CPUDesignTarget.certificate_cycle_checked := generated_ordered_cycle_safety Hlocal;
   CPUDesignTarget.certificate_progress_checked := Hrank |}.
 - exact (joint_architecture checked_pc_effect pending Physical
     (CPUDesignTarget.target_arch_relation target) Hphysical).
 - apply joint_initial; assumption.
Defined.

Definition generated_streaming_certificate
 (rank : CPUDesignTarget.target_state target -> FormalSpec.State -> nat)
 (Hphysical : forall s retired frontier, Physical s retired frontier ->
   CPUDesignTarget.target_arch_relation target s retired)
 (Hstartup : ordered_scheduler (CPUDesignTarget.target_cycle target)
   (CPUDesignTarget.target_commits target) (CPUDesignTarget.target_reset target) ≈
   ordered_scheduler (CPUDesignTarget.target_cycle target)
   (CPUDesignTarget.target_commits target) (CPUDesignTarget.target_boot target))
 (Hempty : pending (CPUDesignTarget.target_boot target) = [])
 (Hboot : Physical (CPUDesignTarget.target_boot target)
   (CPUDesignTarget.target_isa_initial target) (CPUDesignTarget.target_isa_initial target))
 (Hlocal : LocalStreamingTransfers)
 (Hrank : OrderedWaitDecreases (CPUDesignTarget.target_cycle target)
   (CPUDesignTarget.target_commits target) GeneratedJoint rank) :
 CPUDesignTarget.Certificate target.
Proof.
 refine {| CPUDesignTarget.certificate_joint := GeneratedJoint;
   CPUDesignTarget.certificate_rank := rank;
   CPUDesignTarget.certificate_arch_checked := _;
   CPUDesignTarget.certificate_startup_checked := Hstartup;
   CPUDesignTarget.certificate_initial_checked := _;
   CPUDesignTarget.certificate_cycle_checked := generated_streaming_cycle_safety Hlocal;
   CPUDesignTarget.certificate_progress_checked := Hrank |}.
 - exact (joint_architecture checked_pc_effect pending Physical
     (CPUDesignTarget.target_arch_relation target) Hphysical).
 - apply joint_initial; assumption.
Defined.

Theorem generated_infinite_refinement
 (rank : CPUDesignTarget.target_state target -> FormalSpec.State -> nat)
 (Hphysical : forall s retired frontier, Physical s retired frontier ->
   CPUDesignTarget.target_arch_relation target s retired)
 (Hstartup : ordered_scheduler (CPUDesignTarget.target_cycle target)
   (CPUDesignTarget.target_commits target) (CPUDesignTarget.target_reset target) ≈
   ordered_scheduler (CPUDesignTarget.target_cycle target)
   (CPUDesignTarget.target_commits target) (CPUDesignTarget.target_boot target))
 (Hempty : pending (CPUDesignTarget.target_boot target) = [])
 (Hboot : Physical (CPUDesignTarget.target_boot target)
   (CPUDesignTarget.target_isa_initial target) (CPUDesignTarget.target_isa_initial target))
 (Hlocal : LocalCycleTransfers)
 (Hrank : OrderedWaitDecreases (CPUDesignTarget.target_cycle target)
   (CPUDesignTarget.target_commits target) GeneratedJoint rank) :
 ordered_scheduler (CPUDesignTarget.target_cycle target)
   (CPUDesignTarget.target_commits target) (CPUDesignTarget.target_reset target) ≈
 FormalSpec.riscv_itree_with_state (CPUDesignTarget.target_isa_initial target).
Proof.
 exact (CPUDesignTarget.pinned_target_infinite_refinement target
   (generated_certificate rank Hphysical Hstartup Hempty Hboot Hlocal Hrank)).
Qed.

(** An automatically computed search rank replaces a manually invented FSM
    rank. Hbounded is a REAL design proof obligation under the ORIGINAL
    environment, never an added bounded-response axiom. *)
Theorem generated_infinite_refinement_with_search
 (fuel : nat)
 (Hphysical : forall s retired frontier, Physical s retired frontier ->
   CPUDesignTarget.target_arch_relation target s retired)
 (Hstartup : ordered_scheduler (CPUDesignTarget.target_cycle target)
   (CPUDesignTarget.target_commits target) (CPUDesignTarget.target_reset target) ≈
   ordered_scheduler (CPUDesignTarget.target_cycle target)
   (CPUDesignTarget.target_commits target) (CPUDesignTarget.target_boot target))
 (Hempty : pending (CPUDesignTarget.target_boot target) = [])
 (Hboot : Physical (CPUDesignTarget.target_boot target)
   (CPUDesignTarget.target_isa_initial target) (CPUDesignTarget.target_isa_initial target))
 (Hlocal : LocalCycleTransfers)
 (Hbounded : CPUGeneratedProgress.CPUGeneratedProgress.BoundedProgress
   (CPUDesignTarget.target_cycle target) (CPUDesignTarget.target_commits target)
   fuel GeneratedJoint) :
 ordered_scheduler (CPUDesignTarget.target_cycle target)
   (CPUDesignTarget.target_commits target) (CPUDesignTarget.target_reset target) ≈
 FormalSpec.riscv_itree_with_state (CPUDesignTarget.target_isa_initial target).
Proof.
 exact (generated_infinite_refinement (generated_search_rank fuel)
   Hphysical Hstartup Hempty Hboot Hlocal
   (generated_search_wait_decreases fuel Hbounded)).
Qed.
End PinnedTarget.
End Architecture.
Print Assumptions checked_pc_effect_sound.
Print Assumptions generated_ordered_cycle_safety.
Print Assumptions generated_finite_architecture.
Print Assumptions generated_certificate.
Print Assumptions generated_infinite_refinement.
Print Assumptions generated_search_wait_decreases.
Print Assumptions generated_infinite_refinement_with_search.
Print Assumptions generated_streaming_cycle_safety.
Print Assumptions generated_streaming_certificate.
End CPUGeneratedJointITree.
