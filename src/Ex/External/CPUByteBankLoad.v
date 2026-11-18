(** CPU-independent finite byte-bank reads into the original ISA byte memory. *)
From Coq Require Import ZArith List Lia.
Require Import Lang.ExtendedSVBitSlice Ex.External.CPUByteBankArchitecture
 riscv.Platform.Memory coqutil.Word.Interface coqutil.Word.Properties coqutil.Map.Interface
 coqutil.Byte coqutil.Datatypes.HList coqutil.Datatypes.PrimitivePair.
Import ExtendedSVBitSlice CPUByteBankArchitecture.
Local Open Scope Z_scope.
Module CPUByteBankLoad.
Fixpoint bank_bytes n bank address:tuple byte n:=match n with
 |O=>tt|S n=>pair.mk(byte.of_Z(read_slice bank(8*address)8))(bank_bytes n bank(address+1))end.
Section Memory.
Context {word:Interface.word 32}{word_ok:word.ok word}.
Context {Mem:map.map word byte}{mem_ok:map.ok Mem}.
Lemma related_byte bank memory (address:word):BytesRelated 128 bank memory ->
 0<=word.unsigned address<128 ->
 map.get memory address=Some(byte.of_Z(read_slice bank(8*word.unsigned address)8)).
Proof.
 intros HR HB;destruct(HR address HB)as[b[HG HV]].
 rewrite HV,byte.of_Z_unsigned;exact HG.
Qed.
Lemma add_one_unsigned (address:word):0<=word.unsigned address<128 ->
 word.unsigned(word.add address(word.of_Z 1))=word.unsigned address+1.
Proof.
 intro HB;rewrite word.unsigned_add,word.unsigned_of_Z;unfold word.wrap.
 change(1 mod 2^32)with 1;apply Z.mod_small;lia.
Qed.
Theorem related_load_bytes n bank memory (address:word):
 BytesRelated 128 bank memory ->0<=word.unsigned address ->
 word.unsigned address+Z.of_nat n<=128 ->
 Memory.load_bytes n memory address=Some(bank_bytes n bank(word.unsigned address)).
Proof.
 intros HR;revert address;induction n as[|n IH];intros address Hlo Hhi.
 - reflexivity.
 - assert(HB:0<=word.unsigned address<128)by(rewrite Nat2Z.inj_succ in Hhi;lia).
   pose proof(IH(word.add address(word.of_Z 1)))as HT.
   rewrite(add_one_unsigned address HB)in HT.
   assert(HL:Memory.load_bytes n memory(word.add address(word.of_Z 1))=
    Some(bank_bytes n bank(word.unsigned address+1)))by(apply HT;rewrite Nat2Z.inj_succ in Hhi;lia).
   unfold Memory.load_bytes,map.getmany_of_tuple,Memory.footprint in *.
   cbn [tuple.unfoldn tuple.map tuple.option_all bank_bytes].
   rewrite(related_byte bank memory address HR HB),HL;reflexivity.
Qed.
End Memory.
End CPUByteBankLoad.
Print Assumptions CPUByteBankLoad.related_load_bytes.
