(** Dense word images and the shared little-endian ISA instruction memory.
    CPU-independent indices and data; no RTL signal roots or CPU invariant. *)
From Coq Require Import ZArith List Lia.
Require Import Lib.Lib Ex.RvCore.FormalSpec Ex.External.BzeenoFormalSim
 coqutil.Byte coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Word.Properties
 coqutil.Map.Interface riscv.Spec.Decode riscv.Utility.MkMachineWidth riscv.Utility.Utility.
Import ListNotations SZNotations.
Local Open Scope Z_scope.
#[local] Existing Instance SZ_sz_ops.
#[local] Existing Instance hmap_array_ops.
Module CPUProgramROM.
Definition entries_from start(image:list Z):list(Z*Z):=
 combine(List.map Z.of_nat(seq start(length image)))image.
Definition entries image:=entries_from 0 image.
Lemma indexed_rom_lookup image start i:
 szNormZ(hbits(hselectA(BzeenoFormalSim.program_rom(entries_from start image))
  (Z.of_nat(start+i))))=(nth i image 0)mod 2^32.
Proof.
 revert start i. induction image as[|x xs IH];intros start i.
 - destruct i;reflexivity.
 - cbn[entries_from length seq List.map combine BzeenoFormalSim.program_rom hselectA fst snd].
   destruct i as[|i].
   + rewrite Nat.add_0_r,Z.eqb_refl. reflexivity.
   + assert(NE:Z.eqb(Z.of_nat(start+S i))(Z.of_nat start)=false).
     { apply Z.eqb_neq. lia. }
     rewrite NE. replace(start+S i)%nat with(S start+i)%nat by lia.
     exact(IH(S start)i).
Qed.
Lemma entries_from_bounded image start:
 (Z.of_nat(start+length image)<=2^30)%Z ->
 Forall(fun iv:Z*Z=>0<=fst iv<2^30)(entries_from start image).
Proof.
 revert start. induction image as[|x xs IH];intros start HB;[constructor|].
 cbn[entries_from length seq List.map combine]. constructor.
 - cbn[fst]. rewrite Nat2Z.inj_add in HB. cbn[length]in HB. lia.
 - apply IH. replace(S start+length xs)%nat with(start+length(x::xs))%nat by(cbn;lia).
   exact HB.
Qed.
Section ISA.
Context {word:Interface.word 32}{BW:Bitwidth 32}{MW:MachineWidth word}.
Context {Registers:map.map Decode.Register word}{Mem:map.map word byte}.
Context {word_ok:word.ok word}{mem_ok:map.ok Mem}{registers_ok:map.ok Registers}.
Theorem dense_image_little_endian_load image pc i:
 Z.of_nat(length image)<=2^30 ->word.unsigned pc=4*Z.of_nat i ->
 exists tup,Memory.load_bytes 4(FormalSpec.formal_initial_imem(entries image))pc=Some tup /\
 LittleEndian.combine 4 tup=(nth i image 0)mod 2^32.
Proof.
 intros HB HP.
 assert(HE:Forall(fun iv:Z*Z=>0<=fst iv<2^30)(entries image)).
 { apply entries_from_bounded. exact HB. }
 destruct(BzeenoFormalSim.formal_initial_rom_values_related(entries image)HE pc(Z.of_nat i)HP)
  as[tup[HL HV]]. exists tup. split;[exact HL|].
 exact(eq_trans HV(indexed_rom_lookup image 0 i)).
Qed.
End ISA.
End CPUProgramROM.
Print Assumptions CPUProgramROM.dense_image_little_endian_load.
