(** Empty physical stages are not fictitious ISA writes. *)
From Coq Require Import List ZArith.
Require Import Ex.External.CPUReadyOperand.
Import ListNotations CPUReadyOperand.
Module CPUReadySlotCompaction.
Section Compact.
Context {V:Type}.
Fixpoint compact (slots:list(@Slot V)):list(@Slot V):=
 match slots with
 |[]=>[]
 |None::rest=>compact rest
 |Some value::rest=>Some value::compact rest
 end.

Theorem lookup_compact address slots:lookup address(compact slots)=lookup address slots.
Proof.
 induction slots as[|slot rest IH];[reflexivity|].
 destruct slot as[[rd value]|];cbn[compact lookup];rewrite IH;
 destruct(lookup address rest);reflexivity.
Qed.

Theorem resolve_compact (zero:V) physical address slots:
 resolve zero physical address(compact slots)=resolve zero physical address slots.
Proof. unfold resolve;now rewrite lookup_compact. Qed.
End Compact.

Example empty_hardware_stages_have_no_effect:
 @compact Z[None;None]=[].
Proof. reflexivity. Qed.

Example compact_keeps_unavailable_writer:
 @compact Z[None;Some(1%Z,None)]=[Some(1%Z,None)].
Proof. reflexivity. Qed.

Example compact_does_not_make_unavailable_result_ready:
 resolve 0%Z(fun _=>7%Z)1%Z(compact[None;Some(1%Z,None)])=None.
Proof. reflexivity. Qed.
End CPUReadySlotCompaction.
Print Assumptions CPUReadySlotCompaction.lookup_compact.
Print Assumptions CPUReadySlotCompaction.resolve_compact.
