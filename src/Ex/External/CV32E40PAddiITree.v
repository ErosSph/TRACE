(** The real cycle scheduler as an ITree. No commit oracle and no restart.
    The first-retirement lemma is independent of ISA correctness. *)
From Coq Require Import ZArith List.
From ITree Require Import ITree ITreeFacts.
From FreeSim Require Import ModSemE.
Require Import Ex.RvCore.FormalSpec.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Byte.
Require Import riscv.Spec.Decode riscv.Utility.MkMachineWidth riscv.Utility.Utility.
Require Import Ex.External.CV32E40PReq39Trace Ex.External.CV32E40PAddiReachability.
Import CV32E40PReq39Trace CV32E40PAddiReachability.
Local Open Scope itree_scope.
Module CV32E40PAddiITree.
  #[local] Opaque retiring_token advance_retirement.
  Definition Events := FormalSpec.riscv_ioE +' ModSemE.eventE.
  CoFixpoint scheduler_itree {S : Type} (step : S -> S)
      (retire : S -> option Z) (s : S) : itree Events void :=
    match retire s with
    | None => Tau (scheduler_itree step retire (step s))
    | Some pc => Vis (inl1 (FormalSpec.Output pc))
        (fun _ => Tau (scheduler_itree step retire (step s)))
    end.
  Definition rtl_itree (image : InstructionImage) :=
    scheduler_itree (advance_retirement image)
      (fun s => option_map token_pc (retiring_token image s)).

  Lemma rtl_unfold : forall image s,
    rtl_itree image s ≅
      match retiring_token image s with
      | None => Tau (rtl_itree image (advance_retirement image s))
      | Some token => Vis (inl1 (FormalSpec.Output (token_pc token)))
          (fun _ => Tau (rtl_itree image (advance_retirement image s)))
      end.
  Proof.
    intros. rewrite (ITree.Eq.Eqit.itree_eta (rtl_itree image s)).
    unfold rtl_itree, observe. unfold scheduler_itree at 1. cbn.
    destruct (retiring_token image s); reflexivity.
  Qed.
  Print Assumptions rtl_unfold.

  Theorem next_retirement_itree : forall image s n token post,
    NextRetirement image s n token post ->
    rtl_itree image s ≈
      Vis (inl1 (FormalSpec.Output (token_pc token))) (fun _ => rtl_itree image post).
  Proof.
    intros image s n token post H. induction H.
    - rewrite rtl_unfold, H. apply eqit_Vis. intros [].
      apply eqit_Tau_l. reflexivity.
    - rewrite rtl_unfold, H. apply eqit_Tau_l. exact IHNextRetirement.
  Qed.
  Print Assumptions next_retirement_itree.
  Section ISABridge.
    Context {word : Interface.word 32} {BW : Bitwidth 32} {MW : MachineWidth word}.
    Context {Registers : map.map Decode.Register word} {Mem : map.map word byte}.
    Lemma formal_success_unfold : forall (s s' : FormalSpec.State),
      FormalSpec.run1 s = (Some tt, s') ->
      FormalSpec.riscv_itree_with_state s ≈
        Vis (inl1 (FormalSpec.Output (word.unsigned (getPc s))))
          (fun _ => FormalSpec.riscv_itree_with_state s').
    Proof.
      intros s s' Hrun.
      unfold FormalSpec.riscv_itree_with_state at 1. unfold rec_fix.
      rewrite ITree.Interp.RecursionFacts.rec_as_interp.
      cbn -[FormalSpec.run1]. rewrite Hrun.
      rewrite ITree.Interp.InterpFacts.interp_bind,
        ITree.Interp.InterpFacts.interp_trigger. cbn [recursive].
      unfold recursive at 1. cbn -[FormalSpec.run1].
      rewrite ?ITree.Eq.Eqit.bind_bind, ?ITree.Eq.Eqit.bind_trigger.
      apply eqit_Vis. intros [].
      rewrite ?ITree.Eq.Eqit.bind_tau, ?ITree.Eq.Eqit.bind_ret_l, ?ITree.Eq.Eqit.tau_eutt.
      rewrite ITree.Interp.RecursionFacts.interp_recursive_call. reflexivity.
    Qed.
    (** This is a lifting theorem, NOT a discharged CV32E40P invariant.
        Hprogress must be proved from reset-reachable pipeline states.
        Its finite first-retirement witness also rules out infinite stalling. *)
    Theorem itree_refinement_from_inductive_progress :
      forall image (Inv : RetirementState -> FormalSpec.State -> Prop),
      (forall rtl isa, Inv rtl isa ->
        exists n token post isa',
          NextRetirement image rtl n token post /\
          FormalSpec.run1 isa = (Some tt, isa') /\
          token_pc token = word.unsigned (getPc isa) /\ Inv post isa') ->
      forall rtl isa, Inv rtl isa ->
        rtl_itree image rtl ≈ FormalSpec.riscv_itree_with_state isa.
    Proof.
      intros image Inv Hprogress. einit. ecofix CIH. intros rtl isa Hinv.
      destruct (Hprogress rtl isa Hinv) as (n & token & post & isa' & Hnext & Hrun & Hpc & Hpost).
      edrop.
      rewrite (next_retirement_itree image rtl n token post Hnext).
      rewrite (formal_success_unfold isa isa' Hrun), Hpc.
      evis.
    Qed.
    Print Assumptions formal_success_unfold.
    Print Assumptions itree_refinement_from_inductive_progress.
  End ISABridge.
End CV32E40PAddiITree.
