(** Exact case-mux selection; branch priority and selector truncation retained. *)
From Coq Require Import ZArith Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVWordInvariant.
Import ExtendedSV ExtendedSVWordInvariant.
Local Open Scope Z_scope.
Module ExtendedSVSelectedData.
Inductive Selects (width sw:nat)(root:signal)(code:Z):Expr->Expr->Prop:=
| Leaf:forall e,Selects width sw root code e e
| Yes:forall key yes no leaf,norm sw key=code ->Selects width sw root code yes leaf ->
 Selects width sw root code(ECond width(EBinary 1 BEq(EVar sw root)(EConst sw key))yes no)leaf
| No:forall key yes no leaf,norm sw key<>code ->Selects width sw root code no leaf ->
 Selects width sw root code(ECond width(EBinary 1 BEq(EVar sw root)(EConst sw key))yes no)leaf.
Theorem selected_data width sw root code e leaf:Selects width sw root code e leaf ->
 forall s,norm sw(read_signal s root)=code ->norm width(eval_expr s e)=norm width(eval_expr s leaf).
Proof.
 intro HC;induction HC;intros s HS;[reflexivity| |].
 - cbn[eval_expr];rewrite HS,H,Z.eqb_refl.
   change(norm width(norm width(eval_expr s yes))=norm width(eval_expr s leaf)).
   rewrite norm_idempotent;now apply IHHC.
 - cbn[eval_expr];rewrite HS.
   assert(Hneq:Z.eqb code(norm sw key)=false)by(apply Z.eqb_neq;congruence).
   rewrite Hneq.
   change(norm width(norm width(eval_expr s no))=norm width(eval_expr s leaf)).
   rewrite norm_idempotent;now apply IHHC.
Qed.
End ExtendedSVSelectedData.
Print Assumptions ExtendedSVSelectedData.selected_data.
