(** Opt-in scheduler interface for an older LSU WB and younger EX result
    in one ORIGINAL physical cycle. The observer emits 0/1/2 ordered PCs;
    TWO visible events do not run a second RTL cycle. No ISA oracle or
    CPU guarantee is built into the observer. A CPU instance must prove
    both run1 steps, their order, complete post-state Joint and progress.
    The original single-event scheduler and its 21-data-op proof remain
    unchanged. This generic lifting is NOT full38 CPU refinement. *)
From Coq Require Import ZArith List Arith Lia Wf_nat.
From ITree Require Import ITree ITreeFacts.
Require Import Ex.RvCore.FormalSpec Ex.External.CV32E40PAddiITree
  coqutil.Map.Interface coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Byte
  riscv.Spec.Decode riscv.Utility.MkMachineWidth riscv.Utility.Utility.
Import CV32E40PAddiITree.
Local Open Scope itree_scope.
Module CV32E40PTwoCommitITreeInterface.

Inductive CycleCommits := SilentCycle | OneCommit (pc : Z) |
  TwoCommits (older_pc younger_pc : Z).

Section Scheduler.
Context {S : Type} (step : S -> S) (commits : S -> CycleCommits).
CoFixpoint ordered_scheduler (s : S) : itree Events void :=
  match commits s with
  | SilentCycle => Tau (ordered_scheduler (step s))
  | OneCommit pc => Vis (inl1 (FormalSpec.Output pc))
      (fun _ => Tau (ordered_scheduler (step s)))
  | TwoCommits older younger => Vis (inl1 (FormalSpec.Output older))
      (fun _ => Vis (inl1 (FormalSpec.Output younger))
        (fun _ => Tau (ordered_scheduler (step s))))
  end.
Lemma ordered_scheduler_unfold s : ordered_scheduler s ≅
  match commits s with
  | SilentCycle => Tau (ordered_scheduler (step s))
  | OneCommit pc => Vis (inl1 (FormalSpec.Output pc))
      (fun _ => Tau (ordered_scheduler (step s)))
  | TwoCommits older younger => Vis (inl1 (FormalSpec.Output older))
      (fun _ => Vis (inl1 (FormalSpec.Output younger))
        (fun _ => Tau (ordered_scheduler (step s))))
  end.
Proof.
  rewrite (ITree.Eq.Eqit.itree_eta (ordered_scheduler s)).
  unfold observe. unfold ordered_scheduler at 1. cbn.
  destruct (commits s); reflexivity.
Qed.

Inductive FirstVisibleCycle : S -> nat -> CycleCommits -> S -> Prop :=
| visible_now s result : commits s = result -> result <> SilentCycle ->
    FirstVisibleCycle s 1 result (step s)
| silent_wait s n result post : commits s = SilentCycle ->
    FirstVisibleCycle (step s) n result post ->
    FirstVisibleCycle s (Datatypes.S n) result post.

Definition emit_visible (result : CycleCommits) (tail : itree Events void) :=
  match result with
  | SilentCycle => tail
  | OneCommit pc => Vis (inl1 (FormalSpec.Output pc)) (fun _ => tail)
  | TwoCommits older younger => Vis (inl1 (FormalSpec.Output older))
      (fun _ => Vis (inl1 (FormalSpec.Output younger)) (fun _ => tail))
  end.

Theorem first_visible_cycle_itree s n result post :
  FirstVisibleCycle s n result post ->
  ordered_scheduler s ≈ emit_visible result (ordered_scheduler post).
Proof.
  intros H. induction H.
  - rewrite ordered_scheduler_unfold, H.
    destruct result; [contradiction| |]; cbn [emit_visible].
    + apply eqit_Vis. intros []. apply eqit_Tau_l. reflexivity.
    + apply eqit_Vis. intros []. apply eqit_Vis. intros [].
      apply eqit_Tau_l. reflexivity.
  - rewrite ordered_scheduler_unfold, H. apply eqit_Tau_l. exact IHFirstVisibleCycle.
Qed.

Section ISA.
Context {word : Interface.word 32} {BW : Bitwidth 32} {MW : MachineWidth word}.
Context {Registers : map.map Decode.Register word} {Mem : map.map word byte}.
Variable Inv : S -> FormalSpec.State -> Prop.

Inductive VisibleISASteps : CycleCommits -> FormalSpec.State -> FormalSpec.State -> Prop :=
| one_isa_step pc isa isa' : FormalSpec.run1 isa = (Some tt, isa') ->
    pc = word.unsigned (getPc isa) -> VisibleISASteps (OneCommit pc) isa isa'
| two_isa_steps older younger isa middle isa' :
    FormalSpec.run1 isa = (Some tt, middle) ->
    older = word.unsigned (getPc isa) ->
    FormalSpec.run1 middle = (Some tt, isa') ->
    younger = word.unsigned (getPc middle) ->
    VisibleISASteps (TwoCommits older younger) isa isa'.

Definition OrderedCycleSafety := forall rtl isa, Inv rtl isa ->
  match commits rtl with
  | SilentCycle => Inv (step rtl) isa
  | result => exists isa', VisibleISASteps result isa isa' /\ Inv (step rtl) isa'
  end.
Definition OrderedWaitDecreases (rank : S -> FormalSpec.State -> nat) :=
  forall rtl isa, Inv rtl isa -> commits rtl = SilentCycle ->
    (rank (step rtl) isa < rank rtl isa)%nat.
Local Opaque FormalSpec.run1.

Lemma visible_isa_steps_itree result isa isa' : VisibleISASteps result isa isa' ->
  FormalSpec.riscv_itree_with_state isa ≈
    emit_visible result (FormalSpec.riscv_itree_with_state isa').
Proof.
  intros H. destruct H as [pc isa isa' HR HPC|older younger isa middle isa' H1 HP1 H2 HP2].
  - cbn [emit_visible]. rewrite (formal_success_unfold isa isa' HR), HPC. reflexivity.
  - cbn [emit_visible]. rewrite (formal_success_unfold isa middle H1), HP1.
    apply eqit_Vis. intros [].
    rewrite (formal_success_unfold middle isa' H2), HP2. reflexivity.
Qed.

Theorem safety_along_first_visible : OrderedCycleSafety ->
  forall rtl n result post, FirstVisibleCycle rtl n result post ->
  forall isa, Inv rtl isa -> exists isa', VisibleISASteps result isa isa' /\ Inv post isa'.
Proof.
  intros HS rtl n result post HP. induction HP; intros isa HI.
  - pose proof (HS s isa HI) as HC. rewrite H in HC.
    destruct result; [contradiction|exact HC|exact HC].
  - apply IHHP. specialize (HS s isa HI). now rewrite H in HS.
Qed.

Theorem ordered_bounded_first_visible rank : OrderedCycleSafety -> OrderedWaitDecreases rank ->
  forall rtl isa, Inv rtl isa -> exists n result post isa',
    (n <= Datatypes.S (rank rtl isa))%nat /\ FirstVisibleCycle rtl n result post /\
    VisibleISASteps result isa isa' /\ Inv post isa'.
Proof.
  intros HS HD.
  assert (Aux : forall k rtl isa, rank rtl isa = k -> Inv rtl isa ->
    exists n result post isa', (n <= Datatypes.S k)%nat /\
      FirstVisibleCycle rtl n result post /\ VisibleISASteps result isa isa' /\ Inv post isa').
  { intro k. induction k using lt_wf_ind. intros rtl isa HK HI.
    pose proof (HS rtl isa HI) as HC. destruct (commits rtl) as [|pc|older younger] eqn:HE.
    - pose proof (HD rtl isa HI HE) as HL.
      destruct (H (rank (step rtl) isa) ltac:(lia) (step rtl) isa eq_refl HC)
        as (n & result & post & isa' & HB & HP & HR & HPOST).
      exists (Datatypes.S n), result, post, isa'. split; [lia|].
      split; [eapply silent_wait; eauto|]. auto.
    - destruct HC as (isa' & HR & HPOST).
      exists 1%nat, (OneCommit pc), (step rtl), isa'. split; [lia|].
      split; [eapply visible_now; [exact HE|discriminate]|]. auto.
    - destruct HC as (isa' & HR & HPOST).
      exists 1%nat, (TwoCommits older younger), (step rtl), isa'. split; [lia|].
      split; [eapply visible_now; [exact HE|discriminate]|]. auto. }
  intros rtl isa HI. exact (Aux (rank rtl isa) rtl isa eq_refl HI).
Qed.

Theorem ordered_cycle_safety_and_rank_to_itree rank :
  OrderedCycleSafety -> OrderedWaitDecreases rank ->
  forall rtl isa, Inv rtl isa ->
  ordered_scheduler rtl ≈ FormalSpec.riscv_itree_with_state isa.
Proof.
  intros HS HD. einit. ecofix CIH. intros rtl isa HI.
  destruct (ordered_bounded_first_visible rank HS HD rtl isa HI)
    as (n & result & post & isa' & HB & HP & HR & HPOST).
  edrop. rewrite (first_visible_cycle_itree rtl n result post HP),
    (visible_isa_steps_itree result isa isa' HR).
  destruct result; [inversion HR| |]; cbn [emit_visible]; evis; try evis.
Qed.
End ISA.
End Scheduler.
Print Assumptions first_visible_cycle_itree.
Print Assumptions ordered_bounded_first_visible.
Print Assumptions ordered_cycle_safety_and_rank_to_itree.
End CV32E40PTwoCommitITreeInterface.
