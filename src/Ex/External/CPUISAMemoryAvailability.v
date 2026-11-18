(** Pure ORIGINAL ISA memory availability. Statements/proofs have no CPU
    reset, RTL phase, scheduler or physical invariant premises. Reference
    execution helpers currently retain historical CV names. *)
From Coq Require Import ZArith List.
Require Import Ex.RvCore.FormalSpec Ex.RvCore.Machine
 Ex.External.CV32E40PReq41Instruction Ex.External.CV32E40PReq40StateRel
 Ex.External.CV32E40PMemoryExecution.
Require Import coqutil.Map.Interface coqutil.Map.Properties coqutil.Word.Interface
 coqutil.Word.Properties coqutil.Word.Bitwidth coqutil.Byte
 coqutil.Datatypes.HList coqutil.Datatypes.PrimitivePair.
Import CV32E40PReq41Instruction CV32E40PReq40StateRel CV32E40PMemoryExecution.
Local Open Scope Z_scope.
Module CPUISAMemoryAvailability.

Lemma putmany_keeps_read_success {K V} {M:map.map K V} {OK:map.ok M}
 {key_eqb:K->K->bool} {key_eqb_spec:forall x y,BoolSpec(x=y)(x<>y)(key_eqb x y)}
 n (keys:tuple K n) (values:tuple V n) (m:M) k (reads:tuple K k) :
 map.getmany_of_tuple m reads<>None ->
 map.getmany_of_tuple (map.putmany_of_tuple keys values m) reads<>None.
Proof.
 induction n as[|n IH] in keys,values|-*.
 - destruct keys,values;exact(fun H=>H).
 - destruct keys as[key keys],values as[value values].
   cbn [map.putmany_of_tuple PrimitivePair.pair._1 PrimitivePair.pair._2].
   intro H;apply(map.put_preserves_getmany_of_tuple_success
     (key_eqb:=key_eqb)(key_eq_dec:=key_eqb_spec));now apply IH.
Qed.

Lemma store_preserves_read_success {width}{word:Interface.word width}
 {word_ok:word.ok word}{M:map.map word byte}{OK:map.ok M}
 n (m:M) addr bytes m' k readaddr :
 Memory.store_bytes n m addr bytes=Some m' ->
 Memory.load_bytes k m readaddr<>None ->Memory.load_bytes k m' readaddr<>None.
Proof.
 unfold Memory.store_bytes;destruct(Memory.load_bytes n m addr);[|discriminate].
 intro HE;inversion HE;subst m'.
 unfold Memory.load_bytes,Memory.unchecked_store_bytes.
 apply(putmany_keeps_read_success (key_eqb:=word.eqb)(key_eqb_spec:=word.eqb_spec)).
Qed.

Section ISA.
Context {word:Interface.word 32}{BW:Bitwidth 32}.
Context {Registers:map.map Decode.Register word}{Mem:map.map word byte}.
Context {word_ok:word.ok word}{registers_ok:map.ok Registers}{mem_ok:map.ok Mem}.

Definition RAMReadable (s:FormalSpec.State) : Prop := forall n,
 n=1%nat \/ n=2%nat \/ n=4%nat ->
 Memory.load_bytes n (getDataMem s) (word.of_Z 0)<>None.

Theorem readable_current_load_outcome (s:FormalSpec.State) i :
 RAMReadable s ->InFamily FamilyLoad i ->memory_address s i=word.of_Z 0 ->
 exists value,LoadOutcome s i value.
Proof.
 intros HM HF HA;destruct i;cbn [InFamily family_of] in HF;try discriminate HF;
 cbn [LoadOutcome];rewrite HA.
 - specialize(HM 1%nat(or_introl eq_refl)).
   destruct(Memory.load_bytes 1(getDataMem s)(word.of_Z 0))as[bytes|];[|contradiction].
   exists(Utility.int8ToReg bytes),bytes;split;reflexivity.
 - specialize(HM 2%nat(or_intror(or_introl eq_refl))).
   destruct(Memory.load_bytes 2(getDataMem s)(word.of_Z 0))as[bytes|];[|contradiction].
   exists(Utility.int16ToReg bytes),bytes;split;reflexivity.
 - specialize(HM 4%nat(or_intror(or_intror eq_refl))).
   destruct(Memory.load_bytes 4(getDataMem s)(word.of_Z 0))as[bytes|];[|contradiction].
   exists(Utility.int32ToReg bytes),bytes;split;reflexivity.
 - specialize(HM 1%nat(or_introl eq_refl)).
   destruct(Memory.load_bytes 1(getDataMem s)(word.of_Z 0))as[bytes|];[|contradiction].
   exists(Utility.uInt8ToReg bytes),bytes;split;reflexivity.
 - specialize(HM 2%nat(or_intror(or_introl eq_refl))).
   destruct(Memory.load_bytes 2(getDataMem s)(word.of_Z 0))as[bytes|];[|contradiction].
   exists(Utility.uInt16ToReg bytes),bytes;split;reflexivity.
Qed.

Theorem readable_current_store_outcome (s:FormalSpec.State) i :
 RAMReadable s ->InFamily FamilyStore i ->memory_address s i=word.of_Z 0 ->
 exists mem,StoreOutcome s i mem.
Proof.
 intros HM HF HA;destruct i;cbn [InFamily family_of] in HF;try discriminate HF;
 cbn [StoreOutcome];rewrite HA;unfold Memory.store_bytes.
 - specialize(HM 1%nat(or_introl eq_refl)).
   destruct(Memory.load_bytes 1(getDataMem s)(word.of_Z 0));[eexists;reflexivity|contradiction].
 - specialize(HM 2%nat(or_intror(or_introl eq_refl))).
   destruct(Memory.load_bytes 2(getDataMem s)(word.of_Z 0));[eexists;reflexivity|contradiction].
 - specialize(HM 4%nat(or_intror(or_intror eq_refl))).
   destruct(Memory.load_bytes 4(getDataMem s)(word.of_Z 0));[eexists;reflexivity|contradiction].
Qed.

Theorem store_outcome_preserves_readable (s:FormalSpec.State) i mem value :
 InFamily FamilyStore i ->StoreOutcome s i mem ->RAMReadable s ->
 RAMReadable(memory_post s i value mem).
Proof.
 intros HF HO HM n Hn;specialize(HM n Hn).
 change(Memory.load_bytes n mem(word.of_Z 0)<>None).
 destruct i;cbn [InFamily family_of] in HF;try discriminate HF;
 cbn [StoreOutcome] in HO;eapply store_preserves_read_success;eauto.
Qed.

Lemma static_zero_memory_address (s:FormalSpec.State) i :
 memory_rs1 i=0 ->memory_immediate i=0 ->memory_address s i=word.of_Z 0.
Proof.
 intros HS HI;unfold memory_address;rewrite HS,HI.
 unfold formal_register_word;destruct(Z.eq_dec 0 0);[apply word.add_0_r|contradiction].
Qed.
End ISA.
End CPUISAMemoryAvailability.
Print Assumptions CPUISAMemoryAvailability.store_preserves_read_success.
Print Assumptions CPUISAMemoryAvailability.readable_current_load_outcome.
Print Assumptions CPUISAMemoryAvailability.readable_current_store_outcome.
Print Assumptions CPUISAMemoryAvailability.store_outcome_preserves_readable.
Print Assumptions CPUISAMemoryAvailability.static_zero_memory_address.
