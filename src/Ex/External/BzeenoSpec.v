(** ISA-level specification interface for the repaired bzeeno RV32I core.

    This does not reuse the paper case-study's implementation simulation.
    It reuses only the architecture-independent RV32I machine specification
    [FormalSpec].  A future [BzeenoFormalSim] must prove that the pipeline's
    observable commit stream refines [riscv_itree] under [Assumptions]. *)
From Coq Require Import ZArith.BinInt Lists.List.
Require Import Ex.RvCore.FormalSpec.
Require Import coqutil.Word.Interface coqutil.Map.Interface.
Require Import coqutil.Word.Bitwidth.
Require Import riscv.Spec.Machine.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.MkMachineWidth.
Require Import riscv.Utility.Utility.

Import ListNotations.

Module BzeenoSpec.
  Definition ProgramImage := list (Z * Z).

  (** The derived RTL has a 101-word instruction ROM and a 128-byte data RAM.
      The bounds are semantic assumptions, not silently imposed by a Coq
      array lookup.  Alignment is needed for the repaired halfword/word RAM
      behavior. *)
  Record Assumptions (program : ProgramImage) : Prop := {
    program_rom_bound : List.Forall (fun iv : Z * Z => (0 <= fst iv < 101)%Z) program;
    program_word_addressed : List.Forall (fun iv : Z * Z => (0 <= fst iv)%Z) program;
  }.

  Definition data_addr_in_range (addr : Z) : Prop := (0 <= addr < 128)%Z.
  Definition halfword_aligned (addr : Z) : Prop := (addr mod 2 = 0)%Z.
  Definition word_aligned (addr : Z) : Prop := (addr mod 4 = 0)%Z.

  Section RV32I.
    Context {word : Interface.word 32} {BW : Bitwidth 32} {MW : MachineWidth word}.
    Context {Registers : map.map Decode.Register word} {Mem : map.map word byte}.

    (** Initial architectural state and infinite ISA behavior for this exact
        program image.  [formal_initial_imem] installs each (word index,
        instruction) pair at byte address [4 * index], matching the RTL ROM
        index [pc[31:2]]. *)
    Definition initial_state (program : ProgramImage) : FormalSpec.State :=
      FormalSpec.initial_state (FormalSpec.formal_initial_imem program).

    Definition rv32i_spec (program : ProgramImage) :=
      FormalSpec.riscv_itree (FormalSpec.formal_initial_imem program).
  End RV32I.
End BzeenoSpec.
