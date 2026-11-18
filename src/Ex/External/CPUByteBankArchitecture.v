(** CPU-independent byte-level relation for a finite packed RAM bank.
    The finite address domain is explicit: no modulo-aliasing claim outside
    the physical bank, and no expansion of the ISA's 2^32-byte zeroed map. *)
From Coq Require Import ZArith Lia.
Require Import Lang.ExtendedSVBitSlice Ex.RvCore.FormalSpec
 coqutil.Map.Interface coqutil.Word.Interface coqutil.Byte.
Import ExtendedSVBitSlice.
Local Open Scope Z_scope.
Module CPUByteBankArchitecture.
Section Architecture.
Context {word : Interface.word 32} {word_ok : word.ok word}.
Context {Mem : map.map word byte} {mem_ok : map.ok Mem}.

Definition BytesRelated (bytes bank : Z) (memory : Mem) : Prop :=
 forall address : word, 0 <= word.unsigned address < bytes ->
 exists b, map.get memory address = Some b /\
   read_slice bank (8 * word.unsigned address) 8 = byte.unsigned b.

Theorem zero_bank_matches_zeroed_memory bytes :
 BytesRelated bytes 0 FormalSpec.zeroed.
Proof.
 intros address Hrange. exists Byte.x00. split.
 - apply FormalSpec.zeroed_access.
 - unfold read_slice. rewrite Z.shiftr_0_l, Z.land_0_l. reflexivity.
Qed.

Theorem zero_frame_preserves_bytes bytes bank memory :
 bank = 0 -> memory = FormalSpec.zeroed -> BytesRelated bytes bank memory.
Proof. intros -> ->. apply zero_bank_matches_zeroed_memory. Qed.

End Architecture.
End CPUByteBankArchitecture.
Print Assumptions CPUByteBankArchitecture.zero_bank_matches_zeroed_memory.
