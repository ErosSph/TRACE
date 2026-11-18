(** Separate per-cycle safety from finite waiting. Neither obligation is
    assumed inside Inv. This is infrastructure, not a discharged CPU invariant. *)
From Coq Require Import ZArith List Arith Lia Wf_nat.
From ITree Require Import ITree ITreeFacts.
Require Import Ex.RvCore.FormalSpec.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Byte.
Require Import riscv.Spec.Decode riscv.Utility.MkMachineWidth riscv.Utility.Utility.
Require Import Ex.External.CV32E40PReq39Trace Ex.External.CV32E40PAddiReachability
 Ex.External.CV32E40PAddiITree Ex.External.CV32E40PAddiNopISAInvariant.
Import CV32E40PReq39Trace CV32E40PAddiReachability CV32E40PAddiITree CV32E40PAddiNopISAInvariant.
Local Open Scope itree_scope.
Module CV32E40PAddiCycleInduction.
 Definition ProgramScope (image : InstructionImage) := Forall GoodADDI image.
 Section ISA.
 Context {word : Interface.word 32} {BW : Bitwidth 32} {MW : MachineWidth word}.
 Context {Registers : map.map Decode.Register word} {Mem : map.map word byte}.
 Variable image : InstructionImage.
 Variable Inv : RetirementState -> FormalSpec.State -> Prop.
 Definition CycleSafety : Prop := forall rtl isa, Inv rtl isa ->
   match retiring_token image rtl with
   | None => Inv (advance_retirement image rtl) isa
   | Some token => exists isa', FormalSpec.run1 isa = (Some tt, isa') /\
       token_pc token = word.unsigned (getPc isa) /\
       Inv (advance_retirement image rtl) isa'
   end.
 (** A rank is a current-state natural number, not a future trace witness.
     The CPU instance must supply its formula and prove this obligation. *)
 Definition WaitDecreases (rank : RetirementState -> FormalSpec.State -> nat) : Prop :=
   forall rtl isa, Inv rtl isa -> retiring_token image rtl = None ->
     (rank (advance_retirement image rtl) isa < rank rtl isa)%nat.
 #[local] Opaque advance_retirement retiring_token FormalSpec.run1.
 Theorem safety_along_first_retirement : CycleSafety ->
   forall rtl n token post, NextRetirement image rtl n token post ->
   forall isa, Inv rtl isa -> exists isa',
     FormalSpec.run1 isa = (Some tt, isa') /\
     token_pc token = word.unsigned (getPc isa) /\ Inv post isa'.
 Proof.
   intros Hsafe rtl n token post Hpath. induction Hpath; intros isa Hi.
   - specialize (Hsafe s isa Hi). rewrite H in Hsafe. exact Hsafe.
   - apply IHHpath. specialize (Hsafe s isa Hi). now rewrite H in Hsafe.
 Qed.
 Theorem bounded_next_retirement rank : CycleSafety -> WaitDecreases rank ->
   forall rtl isa, Inv rtl isa -> exists n token post isa',
     (n <= S (rank rtl isa))%nat /\ NextRetirement image rtl n token post /\
     FormalSpec.run1 isa = (Some tt, isa') /\
     token_pc token = word.unsigned (getPc isa) /\ Inv post isa'.
 Proof.
   intros Hsafe Hdec.
   assert (Aux : forall k rtl isa, rank rtl isa = k -> Inv rtl isa ->
     exists n token post isa', (n <= S k)%nat /\ NextRetirement image rtl n token post /\
       FormalSpec.run1 isa = (Some tt, isa') /\
       token_pc token = word.unsigned (getPc isa) /\ Inv post isa').
   { intro k. induction k using lt_wf_ind. intros rtl isa Hrank Hi.
     pose proof (Hsafe rtl isa Hi) as Hstep.
     destruct (retiring_token image rtl) as [token |] eqn:Ht.
     - destruct Hstep as (isa' & Hrun & Hpc & Hinv).
       exists 1%nat, token, (advance_retirement image rtl), isa'.
       split; [lia|]. split; [now constructor|]. auto.
     - pose proof (Hdec rtl isa Hi Ht) as Hlt.
       destruct (H (rank (advance_retirement image rtl) isa) ltac:(lia)
         (advance_retirement image rtl) isa eq_refl Hstep)
         as (n & token & post & isa' & Hbound & Hpath & Hrun & Hpc & Hinv).
       exists (S n), token, post, isa'. split; [lia|].
       split; [eapply retire_wait; eauto|]. auto. }
   intros rtl isa Hi. exact (Aux (rank rtl isa) rtl isa eq_refl Hi).
 Qed.
 Theorem cycle_safety_and_rank_to_itree rank : CycleSafety -> WaitDecreases rank ->
   forall rtl isa, Inv rtl isa -> rtl_itree image rtl ≈ FormalSpec.riscv_itree_with_state isa.
 Proof.
   intros Hs Hd. apply (itree_refinement_from_inductive_progress image Inv).
   intros rtl isa Hi.
   destruct (bounded_next_retirement rank Hs Hd rtl isa Hi)
     as (n & token & post & isa' & Hbound & Hpath & Hrun & Hpc & Hinv).
   exists n, token, post, isa'. auto.
 Qed.
 End ISA.
 Print Assumptions safety_along_first_retirement.
 Print Assumptions bounded_next_retirement.
 Print Assumptions cycle_safety_and_rank_to_itree.
End CV32E40PAddiCycleInduction.
