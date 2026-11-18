(** Symbolic reference execution for five loads and three stores.

    This is an ISA-side component, NOT a CPU cycle/refinement theorem.
    Outcomes describe reads/writes of the CURRENT abstract byte memory;
    they are not assumed RTL post-states. The original Machine requires
    four-byte alignment even for byte/halfword accesses. No semantics,
    scheduler, reset, OBI environment, or hardware is changed here. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Ex.External.CV32E40PReq41Instruction
  Ex.External.CV32E40PReq40StateRel Ex.External.CV32E40PDataOpExecution
  Ex.External.CV32E40PBranchExecution Ex.External.CV32E40PAddiNopISAInvariant.
Require Import Ex.RvCore.FormalSpec Ex.RvCore.Machine.
Require Import riscv.Spec.Execute riscv.Spec.ExecuteI riscv.Utility.Monads
  riscv.Proofs.VerifyDecode.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth
  coqutil.Map.Interface coqutil.Byte coqutil.Datatypes.HList.
Import ListNotations CV32E40PReq41Instruction CV32E40PReq40StateRel
  CV32E40PDataOpExecution CV32E40PBranchExecution CV32E40PAddiNopISAInvariant.
Local Open Scope Z_scope.
Module CV32E40PMemoryExecution.

Definition memory_rs1 i := match i with
  | Decode.Lb _ rs _ | Decode.Lh _ rs _ | Decode.Lw _ rs _
  | Decode.Lbu _ rs _ | Decode.Lhu _ rs _
  | Decode.Sb rs _ _ | Decode.Sh rs _ _ | Decode.Sw rs _ _ => rs
  | _ => 0 end.
Definition memory_rs2 i := match i with
  | Decode.Sb _ rs _ | Decode.Sh _ rs _ | Decode.Sw _ rs _ => rs
  | _ => 0 end.
Definition memory_immediate i := match immediate_field i with
  | Some imm => imm | None => 0 end.

Lemma memory_decoded_operands_legal code i :
  (InFamily FamilyLoad i \/ InFamily FamilyStore i) ->
  Decode.decode Decode.RV32I code = Decode.IInstruction i -> LegalOperands i.
Proof.
  intros HF HD.
  destruct (verify_decode Decode.RV32I code eq_refl) as [HV|HB];
    [rewrite HD in HV|congruence].
  destruct HF as [HF|HF]; destruct i;
    cbn [InFamily family_of] in HF; try discriminate.
  all: cbv [verify respects_bounds apply_InstructionMapper Verifier
    map_I map_S verify_I verify_S bitwidth verify_iset] in HV.
  all: unfold LegalOperands; cbn [destination_register source_registers];
    repeat constructor; unfold legal_reg; intuition lia.
Qed.

Section ISA.
Context {word : Interface.word 32} {BW : Bitwidth 32}.
Context {Registers : map.map Decode.Register word} {Mem : map.map word byte}.
Context {word_ok : word.ok word} {registers_ok : map.ok Registers} {mem_ok : map.ok Mem}.

Definition memory_address (s : FormalSpec.State) i : word :=
  word.add (formal_register_word s (memory_rs1 i))
    (word.of_Z (memory_immediate i)).
Definition MemoryAligned (s : FormalSpec.State) i : Prop :=
  word.unsigned (memory_address s i) mod 4 = 0.

Definition register_write (s : FormalSpec.State) rd (value : word) : Registers :=
  if Z.eq_dec rd 0 then getRegs s else map.put (getRegs s) rd value.
Definition memory_post (s : FormalSpec.State) i (value : word) (mem : Mem)
    : FormalSpec.State :=
  {| getRegs := match destination_register i with
       | Some rd => register_write s rd value | None => getRegs s end;
     getPc := getNextPc s;
     getNextPc := word.add (getNextPc s) (word.of_Z 4);
     getInstMem := getInstMem s; getDataMem := mem |}.

(** The tuple is obtained from Memory.load_bytes, not chosen by a CPU
    witness. Signed/unsigned extensions are the original riscv-coq ones. *)
Definition LoadOutcome (s : FormalSpec.State) i (value : word) : Prop :=
  match i with
  | Decode.Lb _ _ _ => exists bytes : tuple byte 1,
      Memory.load_bytes 1 (getDataMem s) (memory_address s i) = Some bytes /\
      value = Utility.int8ToReg bytes
  | Decode.Lh _ _ _ => exists bytes : tuple byte 2,
      Memory.load_bytes 2 (getDataMem s) (memory_address s i) = Some bytes /\
      value = Utility.int16ToReg bytes
  | Decode.Lw _ _ _ => exists bytes : tuple byte 4,
      Memory.load_bytes 4 (getDataMem s) (memory_address s i) = Some bytes /\
      value = Utility.int32ToReg bytes
  | Decode.Lbu _ _ _ => exists bytes : tuple byte 1,
      Memory.load_bytes 1 (getDataMem s) (memory_address s i) = Some bytes /\
      value = Utility.uInt8ToReg bytes
  | Decode.Lhu _ _ _ => exists bytes : tuple byte 2,
      Memory.load_bytes 2 (getDataMem s) (memory_address s i) = Some bytes /\
      value = Utility.uInt16ToReg bytes
  | _ => False end.

Definition StoreOutcome (s : FormalSpec.State) i (mem : Mem) : Prop :=
  match i with
  | Decode.Sb _ _ _ => Memory.store_bytes 1 (getDataMem s) (memory_address s i)
      (Utility.regToInt8 (formal_register_word s (memory_rs2 i))) = Some mem
  | Decode.Sh _ _ _ => Memory.store_bytes 2 (getDataMem s) (memory_address s i)
      (Utility.regToInt16 (formal_register_word s (memory_rs2 i))) = Some mem
  | Decode.Sw _ _ _ => Memory.store_bytes 4 (getDataMem s) (memory_address s i)
      (Utility.regToInt32 (formal_register_word s (memory_rs2 i))) = Some mem
  | _ => False end.

Lemma get_register_exact (s : FormalSpec.State) r : legal_reg r ->
  Machine.getRegister r s = (Some (formal_register_word s r), s).
Proof.
  intros HR. unfold Machine.getRegister; cbn [IsRiscvProgram].
  unfold formal_register_word. destruct (Z.eq_dec r 0); [reflexivity|].
  assert (HB : ((0 <? r) && (r <? 32))%bool = true).
  { apply andb_true_iff; split; apply Z.ltb_lt; unfold legal_reg in HR; lia. }
  rewrite HB. cbn [Bind Return OState_Monad OStateOperations.get].
  destruct (map.get (getRegs s) r); reflexivity.
Qed.
Lemma set_register_exact (s : FormalSpec.State) r value : legal_reg r ->
  Machine.setRegister r value s =
    (Some tt, withRegs (register_write s r value) s).
Proof.
  intros HR. unfold Machine.setRegister; cbn [IsRiscvProgram].
  unfold register_write. destruct (Z.eq_dec r 0).
  - destruct s; reflexivity.
  - assert (HB : ((0 <? r) && (r <? 32))%bool = true).
    { apply andb_true_iff; split; apply Z.ltb_lt; unfold legal_reg in HR; lia. }
    rewrite HB. destruct s; reflexivity.
Qed.
Lemma assert_aligned_exact (s : FormalSpec.State) (addr : word) :
  word.unsigned addr mod 4 = 0 -> assert_aligned addr s = (Some tt, s).
Proof.
  intros HA. unfold assert_aligned. rewrite aligned_guard_false by exact HA.
  reflexivity.
Qed.
Lemma load_bytes_exact (s : FormalSpec.State) n (addr : word) (bytes : tuple byte n) :
  word.unsigned addr mod 4 = 0 ->
  Memory.load_bytes n (getDataMem s) addr = Some bytes ->
  loadN n Machine.Execute addr s = (Some bytes, s).
Proof.
  intros HA HM. unfold loadN. cbn [Bind OState_Monad].
  rewrite assert_aligned_exact by exact HA.
  cbn [Bind Return OState_Monad OStateOperations.get].
  unfold fail_if_None. rewrite HM. reflexivity.
Qed.
Lemma store_bytes_exact (s : FormalSpec.State) n (addr : word)
    (bytes : tuple byte n) mem :
  word.unsigned addr mod 4 = 0 ->
  Memory.store_bytes n (getDataMem s) addr bytes = Some mem ->
  storeN n Machine.Execute addr bytes s = (Some tt, withDataMem mem s).
Proof.
  intros HA HM. unfold storeN. cbn [Bind OState_Monad].
  rewrite assert_aligned_exact by exact HA.
  cbn [Bind Return OState_Monad OStateOperations.get].
  unfold fail_if_None. rewrite HM. reflexivity.
Qed.

Theorem execute_load_exact (s : FormalSpec.State) i value :
  InFamily FamilyLoad i -> LegalOperands i -> MemoryAligned s i ->
  LoadOutcome s i value ->
  ISAStep s i (memory_post s i value (getDataMem s)).
Proof.
  intros HF HL HA HO. destruct i; cbn [InFamily family_of] in HF; try discriminate.
  all: unfold LegalOperands in HL; cbn [destination_register source_registers] in HL;
    destruct HL as [HR HS]; inversion HS; subst; clear HS.
  all: cbn [LoadOutcome] in HO; destruct HO as (bytes & HM & ->).
  all: unfold ISAStep; cbn [Execute.execute ExecuteI.execute Machine.translate
    Machine.DefaultRiscvState Bind Return OState_Monad];
    rewrite get_register_exact by assumption;
    cbn [Bind Return OState_Monad];
    unfold Machine.loadByte, Machine.loadHalf, Machine.loadWord;
    cbn [IsRiscvProgram].
  all: unfold MemoryAligned, memory_address in HA, HM;
    cbn [memory_rs1 memory_immediate immediate_field] in HA, HM;
    rewrite (load_bytes_exact s _ _ bytes) by assumption;
    cbn [Bind Return OState_Monad];
    rewrite set_register_exact by exact HR.
  all: destruct s; reflexivity.
Qed.

Theorem execute_store_exact (s : FormalSpec.State) i mem :
  InFamily FamilyStore i -> LegalOperands i -> MemoryAligned s i ->
  StoreOutcome s i mem ->
  ISAStep s i (memory_post s i (word.of_Z 0) mem).
Proof.
  intros HF HL HA HM. destruct i; cbn [InFamily family_of] in HF; try discriminate.
  all: unfold LegalOperands in HL; cbn [destination_register source_registers] in HL;
    destruct HL as [_ HS];
    repeat match goal with H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H end.
  all: unfold ISAStep; cbn [Execute.execute ExecuteI.execute Machine.translate
    Machine.DefaultRiscvState Bind Return OState_Monad];
    rewrite get_register_exact by assumption;
    cbn [Bind Return OState_Monad];
    rewrite get_register_exact by assumption;
    cbn [Bind Return OState_Monad];
    unfold Machine.storeByte, Machine.storeHalf, Machine.storeWord;
    cbn [IsRiscvProgram].
  all: unfold StoreOutcome, MemoryAligned, memory_address in HA, HM;
    cbn [memory_rs1 memory_rs2 memory_immediate immediate_field] in HA, HM;
    rewrite (store_bytes_exact s _ _ _ mem) by assumption.
  all: destruct s; reflexivity.
Qed.

Theorem current_load_run1_exact s i value : InFamily FamilyLoad i ->
  CurrentInstruction s i -> MemoryAligned s i -> LoadOutcome s i value ->
  FormalSpec.run1 s = (Some tt, memory_post s i value (getDataMem s)).
Proof.
  intros HF HC HA HO. eapply current_instruction_run1_step; [exact HC|].
  apply execute_load_exact; auto.
  destruct HC as [_ [bytes [_ HD]]].
  eapply memory_decoded_operands_legal; [now left|exact HD].
Qed.
Theorem current_store_run1_exact s i mem : InFamily FamilyStore i ->
  CurrentInstruction s i -> MemoryAligned s i -> StoreOutcome s i mem ->
  FormalSpec.run1 s = (Some tt, memory_post s i (word.of_Z 0) mem).
Proof.
  intros HF HC HA HM. eapply current_instruction_run1_step; [exact HC|].
  apply execute_store_exact; auto.
  destruct HC as [_ [bytes [_ HD]]].
  eapply memory_decoded_operands_legal; [now right|exact HD].
Qed.

Theorem memory_post_preserves_isa_shape image (s : FormalSpec.State) i value mem :
  ISAInvariant image s -> ISAInvariant image (memory_post s i value mem).
Proof.
  intros (HROM & HA & HN). unfold ISAInvariant, memory_post.
  cbn [getInstMem getPc getNextPc]. split; [exact HROM|]. split.
  - rewrite HN. now apply aligned_successor.
  - rewrite word.unsigned_add, word.unsigned_of_Z.
    change (4 mod 2^32) with 4. reflexivity.
Qed.
Theorem store_post_register_frame (s : FormalSpec.State) i mem :
  InFamily FamilyStore i -> getRegs (memory_post s i (word.of_Z 0) mem) = getRegs s.
Proof. intros HF. destruct i; cbn [InFamily family_of] in HF;
  try discriminate; reflexivity. Qed.
Theorem memory_post_register_read (s : FormalSpec.State) i rd value mem r :
  destination_register i = Some rd ->
  formal_register_word (memory_post s i value mem) r =
    if Z.eq_dec r 0 then word.of_Z 0 else
    if Z.eq_dec rd 0 then formal_register_word s r else
    if Z.eq_dec r rd then value else formal_register_word s r.
Proof.
  intros Hrd. unfold formal_register_word, memory_post; cbn [getRegs].
  rewrite Hrd. unfold register_write. destruct (Z.eq_dec r 0); [reflexivity|].
  destruct (Z.eq_dec rd 0); [reflexivity|].
  destruct (Z.eq_dec r rd) as [->|Hne].
  - rewrite map.get_put_same. reflexivity.
  - rewrite map.get_put_diff by congruence. reflexivity.
Qed.
End ISA.
Print Assumptions memory_decoded_operands_legal.
Print Assumptions execute_load_exact.
Print Assumptions execute_store_exact.
Print Assumptions current_load_run1_exact.
Print Assumptions current_store_run1_exact.
Print Assumptions memory_post_preserves_isa_shape.
Print Assumptions memory_post_register_read.
End CV32E40PMemoryExecution.
