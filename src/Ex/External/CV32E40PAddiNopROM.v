(** Opt-in total byte ROM. Unspecified instruction words are NOP, exactly
    as in the existing OBI environment. The old zero-filled baseline is intact.
    The finite map initializer is logical: never compute its 2^32 stores. *)
From Coq Require Import ZArith List Lia.
Require Import Ex.External.CV32E40PReq39Trace.
Require Import Ex.RvCore.FormalSpec.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Word.Properties
  coqutil.Word.LittleEndian coqutil.Byte.
Require Import riscv.Utility.Words32Naive riscv.Utility.DefaultMemImpl32.
Import CV32E40PReq39Trace.
Local Open Scope Z_scope.

Module CV32E40PAddiNopROM.
  Definition image_byte image address : byte :=
    byte.of_Z (Z.shiftr (instruction_from_image image (4 * (address / 4)))
      (8 * (address mod 4))).

  Section GenericMemory.
  Context {word : Interface.word 32} {Mem : map.map word byte}.
  Context {word_ok : word.ok word} {mem_ok : map.ok Mem}.
  Fixpoint initialized_until (f : Z -> byte) (n : nat) : Mem :=
    match n with
    | O => map.empty
    | S k => map.put (initialized_until f k) (word.of_Z (Z.of_nat k)) (f (Z.of_nat k))
    end.
  Definition nop_rom image : Mem := initialized_until (image_byte image) (2^32).

  Lemma initialized_access f len (w : word) :
    (len <= 2^32)%nat -> word.unsigned w < Z.of_nat len ->
    map.get (initialized_until f len) w = Some (f (word.unsigned w)).
  Proof.
    induction len as [|len IH]; intros Hlen Hw; [pose proof (word.unsigned_range w); lia|].
    change (map.get (map.put (initialized_until f len)
      (word.of_Z (Z.of_nat len)) (f (Z.of_nat len))) w = Some (f (word.unsigned w))).
    destruct (Z.eq_dec (word.unsigned w) (Z.of_nat len)) as [Heq|Hneq].
    - rewrite <- Heq.
      rewrite word.of_Z_unsigned. apply map.get_put_same.
    - rewrite map.get_put_diff.
      + apply IH; lia.
      + intro Heq. apply Hneq. rewrite Heq, word.unsigned_of_Z.
        unfold word.wrap. apply Z.mod_small. split; [lia|].
        assert (Hlt : (len < 2^32)%nat) by lia.
        apply Nat2Z.inj_lt in Hlt. rewrite Nat2Z.inj_pow in Hlt. exact Hlt.
  Qed.
  Lemma nop_rom_access image (w : word) :
    map.get (nop_rom image) w = Some (image_byte image (word.unsigned w)).
  Proof.
    apply initialized_access; [lia|].
    rewrite Nat2Z.inj_pow. apply word.unsigned_range.
  Qed.
  End GenericMemory.
  #[local] Opaque nop_rom.

  Lemma aligned_lane image pc lane :
    pc mod 4 = 0 -> 0 <= lane < 4 ->
    image_byte image (pc + lane) =
      byte.of_Z (Z.shiftr (instruction_from_image image pc) (8 * lane)).
  Proof.
    intros Halign Hlane. unfold image_byte.
    assert (Hdiv : (pc + lane) / 4 = pc / 4).
    { symmetry. apply Z.div_unique with (r := lane); [lia|].
      pose proof (Z.div_mod pc 4 ltac:(lia)). lia. }
    assert (Hmod : (pc + lane) mod 4 = lane).
    { rewrite Z.add_mod, Halign, Z.add_0_l, Z.mod_mod by lia. apply Z.mod_small; lia. }
    rewrite Hdiv, Hmod.
    replace (4 * (pc / 4)) with pc by (pose proof (Z.div_mod pc 4 ltac:(lia)); lia).
    reflexivity.
  Qed.

  Section Fetch.
  Context {word : Interface.word 32} {Mem : map.map word byte}.
  Context {word_ok : word.ok word} {mem_ok : map.ok Mem}.
  Lemma load_total image n (addresses : HList.tuple word n) :
    map.getmany_of_tuple (nop_rom image) addresses =
      Some (HList.tuple.map (fun a => image_byte image (word.unsigned a)) addresses).
  Proof.
    induction n as [|n IH]; [destruct addresses; reflexivity|].
    destruct addresses as [a rest].
    change (match map.get (nop_rom image) a with
      | None => None
      | Some b => match map.getmany_of_tuple (nop_rom image) rest with
        | None => None | Some bs => Some (PrimitivePair.pair.mk b bs) end end =
      Some (PrimitivePair.pair.mk (image_byte image (word.unsigned a))
        (HList.tuple.map (fun a => image_byte image (word.unsigned a)) rest))).
    rewrite nop_rom_access, IH. reflexivity.
  Qed.

  Theorem nop_rom_fetch image (pc : word) : word.unsigned pc mod 4 = 0 ->
    Memory.load_bytes 4 (nop_rom image) pc =
      Some (LittleEndian.split 4 (instruction_from_image image (word.unsigned pc))).
  Proof.
    intros Halign. unfold Memory.load_bytes. rewrite load_total.
    unfold Memory.footprint.
    cbn [HList.tuple.unfoldn HList.tuple.map].
    pose proof (word.unsigned_range pc) as Hrange.
    assert (Hbound : word.unsigned pc <= 2^32 - 4).
    { pose proof (Z.div_mod (word.unsigned pc) 4 ltac:(lia)). lia. }
    rewrite !word.unsigned_add, !word.unsigned_of_Z. unfold word.wrap.
    change (1 mod 2^32) with 1.
    rewrite !Z.mod_small by lia.
    replace (word.unsigned pc + 1 + 1 + 1) with (word.unsigned pc + 3) by lia.
    replace (word.unsigned pc + 1 + 1) with (word.unsigned pc + 2) by lia.
    replace (word.unsigned pc) with (word.unsigned pc + 0) at 1 by lia.
    rewrite !aligned_lane by lia.
    unfold LittleEndian.split_deprecated.
    rewrite !Z.shiftr_shiftr by lia.
    rewrite Z.shiftr_0_r.
    reflexivity.
  Qed.
  End Fetch.

  Print Assumptions nop_rom_access.
  Print Assumptions aligned_lane.
  Print Assumptions nop_rom_fetch.
End CV32E40PAddiNopROM.
