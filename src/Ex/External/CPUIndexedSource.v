From Coq Require Import ZArith List.
Require Import Lang.ExtendedSV Ex.External.CV32E40PReq41Instruction.
Import ExtendedSV CV32E40PReq41Instruction.

(** The position is in ISA read order, not a guessed RTL port number. *)
Definition IndexedSourceAddress width root (observed:State)
 (instruction:Decode.InstructionI) position : Prop :=
 match nth_error (source_registers instruction) position with
 | Some address => norm width (read_signal observed root)=address
 | None => True
 end.

Theorem indexed_source_address_member width root observed instruction position:
 nth_error (source_registers instruction) position <> None ->
 IndexedSourceAddress width root observed instruction position ->
 In (norm width (read_signal observed root)) (source_registers instruction).
Proof.
 unfold IndexedSourceAddress.
 destruct (nth_error (source_registers instruction) position) as [address|] eqn:HN.
 - intros _ HR; rewrite HR; eapply nth_error_In; exact HN.
 - intros H; exfalso; apply H; reflexivity.
Qed.
Print Assumptions indexed_source_address_member.
