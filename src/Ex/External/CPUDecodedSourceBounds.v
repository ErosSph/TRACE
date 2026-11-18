(** Bounds follow from the original decoder, before any instruction executes.
    No DUT invariant or successful run1 premise is used. *)
From Coq Require Import ZArith List Lia Bool.
Require Import riscv.Spec.Decode coqutil.Z.BitOps.
Require Import Ex.External.CV32E40PReq41Instruction.
Import ListNotations CV32E40PReq41Instruction.
Local Open Scope Z_scope.
Module CPUDecodedSourceBounds.
Definition bounded (instruction:Decode.Instruction):Prop:=
 match instruction with
 |Decode.IInstruction i=>Forall(fun r=>0<=r<32)(source_registers i)
 |_=>True
 end.

Lemma decoder_bounded word:bounded(Decode.decode Decode.RV32I word).
Proof.
 assert(H1:0<=BitOps.bitSlice word 15 20<32).
 { exact(BitOps.bitSlice_bounds 15 20 word). }
 assert(H2:0<=BitOps.bitSlice word 20 25<32).
 { exact(BitOps.bitSlice_bounds 20 25 word). }
 unfold Decode.decode.
 cbv beta iota zeta delta [Decode.supportsM Decode.supportsA Decode.supportsF Decode.bitwidth].
 match goal with |- context[Decode.isValidI ?body]=>set(core:=body) end.
 assert(Hcore:Forall(fun r=>0<=r<32)(source_registers core)).
 { unfold core.
   repeat match goal with |- context[if ?test then _ else _] =>
     destruct test;try solve[cbn[source_registers];repeat first[assumption|constructor]]
   end.
 }
 match goal with |- context[Decode.isValidCSR ?body]=>set(csr:=body) end.
 destruct(Decode.isValidI core);destruct(Decode.isValidCSR csr);
 cbn[bounded];try exact I;exact Hcore.
Qed.

Theorem decoded_source_bounds word i:
 Decode.decode Decode.RV32I word=Decode.IInstruction i ->
 Forall(fun r=>0<=r<32)(source_registers i).
Proof. intro HD;pose proof(decoder_bounded word)as H;rewrite HD in H;exact H. Qed.
End CPUDecodedSourceBounds.
Print Assumptions CPUDecodedSourceBounds.decoded_source_bounds.
