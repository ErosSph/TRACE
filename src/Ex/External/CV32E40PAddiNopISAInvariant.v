(** ISA-side induction for an ADDI image with a total NOP tail.
    This does NOT assert a CV32E40P pipeline invariant. *)
From Coq Require Import ZArith List Lia.
Require Import Ex.External.CV32E40PAddiNopROM Ex.External.CV32E40PReq39Trace
  Ex.External.CV32E40PReq40StateRel.
Require Import Ex.RvCore.FormalSpec Ex.RvCore.Machine.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth
  coqutil.Map.Interface coqutil.Byte riscv.Utility.MkMachineWidth.
Import CV32E40PAddiNopROM CV32E40PReq39Trace CV32E40PReq40StateRel.
Local Open Scope Z_scope.
Module CV32E40PAddiNopISAInvariant.
  Definition GoodADDI instruction : Prop := exists rd rs imm,
    legal_reg rd /\ legal_reg rs /\ legal_addi_imm imm /\
    Decode.decode Decode.RV32I (instruction mod 2^32) =
      Decode.IInstruction (Decode.Addi rd rs imm).
  Lemma nop_is_addi : GoodADDI nop.
  Proof. exists 0, 0, 0. repeat split; unfold legal_reg, legal_addi_imm; lia || reflexivity. Qed.
  Lemma good_nth image n : Forall GoodADDI image -> GoodADDI (nth n image nop).
  Proof.
    intros H. induction H in n |- *; destruct n; cbn; auto using nop_is_addi.
  Qed.
  Theorem image_fetch_is_addi image pc :
    Forall GoodADDI image -> GoodADDI (instruction_from_image image pc).
  Proof.
    intros H. unfold instruction_from_image.
    destruct (andb (Z.leb 0 pc) (Z.eqb (pc mod 4) 0));
      auto using good_nth, nop_is_addi.
  Qed.

  Lemma aligned_successor p : p mod 4 = 0 -> ((p+4) mod 2^32) mod 4 = 0.
  Proof.
    intros H. apply Z.mod_divide; [lia|].
    exists (p / 4 + 1 - 1073741824 * ((p+4) / 4294967296)).
    change (2^32) with 4294967296.
    rewrite Z.mod_eq by lia. pose proof (Z.div_mod p 4 ltac:(lia)). nia.
  Qed.

  Section ISA.
  Context {word : Interface.word 32} {BW : Bitwidth 32}.
  Context {Registers : map.map Decode.Register word} {Mem : map.map word byte}.
  Context {word_ok : word.ok word} {registers_ok : map.ok Registers} {mem_ok : map.ok Mem}.
  #[local] Opaque nop_rom FormalSpec.run1.
  Definition ISAInvariant image (s : FormalSpec.State) : Prop :=
    getInstMem s = nop_rom image /\ word.unsigned (getPc s) mod 4 = 0 /\
    word.unsigned (getNextPc s) = (word.unsigned (getPc s)+4) mod 2^32.

  Theorem isa_success_and_preservation image s :
    Forall GoodADDI image -> ISAInvariant image s ->
    exists s', FormalSpec.run1 s = (Some tt, s') /\ ISAInvariant image s' /\
      getInstMem s' = getInstMem s /\ getDataMem s' = getDataMem s.
  Proof.
    intros Himage (Hmem & Halign & Hnext).
    destruct (image_fetch_is_addi image (word.unsigned (getPc s)) Himage)
      as (rd & rs & imm & Hrd & Hrs & Himm & Hdecode).
    assert (Haddi : ADDIAtPC s rd rs imm).
    { econstructor; [exact Halign| |].
      - rewrite Hmem. apply nop_rom_fetch. exact Halign.
      - rewrite LittleEndian.combine_split. exact Hdecode. }
    exists (addi_isa_post s rd rs imm). split.
    - exact (run1_addi_exact s rd rs imm Hrd Hrs Himm Haddi).
    - unfold ISAInvariant, addi_isa_post. cbn [getInstMem getDataMem getPc getNextPc].
      split.
      + split; [exact Hmem|]. split.
        * rewrite Hnext. apply aligned_successor. exact Halign.
        * rewrite word.unsigned_add, word.unsigned_of_Z.
          change (4 mod 2^32) with 4. reflexivity.
      + split; reflexivity.
  Qed.
  Inductive ISARuns : nat -> FormalSpec.State -> FormalSpec.State -> Prop :=
  | runs_zero : forall s, ISARuns O s s
  | runs_step : forall n s s1 s2, FormalSpec.run1 s = (Some tt, s1) ->
      ISARuns n s1 s2 -> ISARuns (S n) s s2.
  Theorem arbitrary_finite_isa_progress image s n :
    Forall GoodADDI image -> ISAInvariant image s ->
    exists s', ISARuns n s s' /\ ISAInvariant image s'.
  Proof.
    intros Hp. induction n as [|n IH] in s |- *; intros Hi.
    - exists s. split; [constructor|exact Hi].
    - destruct (isa_success_and_preservation image s Hp Hi) as (s1 & Hrun & Hinv & _).
      destruct (IH s1 Hinv) as (s2 & Hsteps & Hfinal).
      exists s2. split; [econstructor; eauto|exact Hfinal].
  Qed.
  End ISA.
  Print Assumptions isa_success_and_preservation.
  Print Assumptions arbitrary_finite_isa_progress.
End CV32E40PAddiNopISAInvariant.
