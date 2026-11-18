(** CPU-independent store widths and the explicit zero-source loop encodings.
    This metadata is not a hardware correctness certificate. *)
From Coq Require Import ZArith.
Require Import riscv.Spec.Decode.
Local Open Scope Z_scope.
Module CPUStoreInstructionKind.
Inductive StoreKind:=StoreByte|StoreHalf|StoreWord.
Definition funct3 k:Z:=match k with StoreByte=>0|StoreHalf=>1|StoreWord=>2 end.
Definition code k:Z:=match k with StoreByte=>35|StoreHalf=>4131|StoreWord=>8227 end.
Definition bytes k:nat:=match k with StoreByte=>1%nat|StoreHalf=>2%nat|StoreWord=>4%nat end.
Definition byte_flag k:Z:=match k with StoreByte=>1|_=>0 end.
Definition half_flag k:Z:=match k with StoreHalf=>1|_=>0 end.
Definition instruction k:=match k with
 StoreByte=>Decode.Sb 0 0 0|StoreHalf=>Decode.Sh 0 0 0|StoreWord=>Decode.Sw 0 0 0 end.
Lemma decode_checked k:Decode.decode Decode.RV32I(code k)=Decode.IInstruction(instruction k).
Proof. destruct k;reflexivity. Qed.
End CPUStoreInstructionKind.
Print Assumptions CPUStoreInstructionKind.decode_checked.
