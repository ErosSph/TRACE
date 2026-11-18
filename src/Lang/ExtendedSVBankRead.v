(** Checked raw register-bank read sites.  These facts identify a physical
    lane, not the instruction that owns its index or its architectural age. *)
From Coq Require Import ZArith List Lia Bool btauto.Btauto.
Require Import Lang.ExtendedSV Lang.ExtendedSVBitSlice
 Lang.ExtendedSVRegisterBank Lang.ExtendedSVBankAlignment.
Import ListNotations ExtendedSV ExtendedSVBitSlice ExtendedSVRegisterBank
 ExtendedSVBankAlignment.
Local Open Scope Z_scope.
Module ExtendedSVBankRead.

(** Paths are checked against the real process body, not a parser's summary. *)
Inductive SyntaxNode :=
| StmtNode (body:Stmt)
| ExprNode (expression:Expr)
| LValueNode (target:LValue)
| ArmNode (arm:option Expr * Stmt).

Definition syntax_children node : list SyntaxNode :=
 match node with
 | StmtNode SSkip => []
 | StmtNode (SAssign _ rhs lhs) => [ExprNode rhs; LValueNode lhs]
 | StmtNode (SSeq statements) => map StmtNode statements
 | StmtNode (SIf guard yes no) => [ExprNode guard; StmtNode yes; StmtNode no]
 | StmtNode (SCase scrutinee arms) => ExprNode scrutinee :: map ArmNode arms
 | ArmNode (key,body) =>
   match key with None => [StmtNode body] | Some e => [ExprNode e; StmtNode body] end
 | LValueNode (LVar _ _) => []
 | LValueNode (LSel _ base offset) => [LValueNode base; ExprNode offset]
 | ExprNode (EConst _ _) | ExprNode (EVar _ _) => []
 | ExprNode (ESel _ a b) | ExprNode (EConcat _ a b)
 | ExprNode (EBinary _ _ a b) => [ExprNode a; ExprNode b]
 | ExprNode (EReplicate _ _ body) | ExprNode (EExtend _ _ body)
 | ExprNode (EUnary _ _ body) => [ExprNode body]
 | ExprNode (ECond _ guard yes no) => [ExprNode guard; ExprNode yes; ExprNode no]
 end.

Fixpoint syntax_at node (path:list nat) : option SyntaxNode :=
 match path with
 | [] => Some node
 | index::rest =>
   match nth_error (syntax_children node) index with
   | Some child => syntax_at child rest | None => None end
 end.
Definition expression_at proc path : option Expr :=
 match syntax_at (StmtNode (process_body proc)) path with
 | Some (ExprNode e) => Some e | _ => None end.
Definition eval_read_site proc path s : option Z :=
 option_map (eval_expr s) (expression_at proc path).

Lemma read_slice_norm_inside total value offset width :
 0<=offset -> 0<=width -> offset+width<=Z.of_nat total ->
 read_slice (norm total value) offset width=read_slice value offset width.
Proof.
 intros HO HW HT. apply Z.bits_inj;intro bit.
 destruct (Z_lt_ge_dec bit 0) as [HN|HP].
 - repeat rewrite Z.testbit_neg_r by lia. reflexivity.
 - unfold read_slice. rewrite !Z.land_spec.
   destruct (Z_lt_ge_dec bit width) as [HL|HH].
   + rewrite mask_bit_low by lia. rewrite !Bool.andb_true_r.
     rewrite !Z.shiftr_spec by lia.
     unfold norm,mask. rewrite Z.land_spec.
     rewrite mask_bit_low by lia. now rewrite Bool.andb_true_r.
   + rewrite mask_bit_high by lia. now rewrite !Bool.andb_false_r.
Qed.

Theorem eval_packed_lane root total offset :
 (1024<=total)%nat -> bounded32b offset=true -> forall s,
 eval_expr s (ESel 32 (EVar total root) offset)=
 lane_read 32 (read_signal s root) (eval_expr s offset/32).
Proof.
 intros HT HB s. destruct (bounded32b_sound offset HB s) as [HI HM].
 pose proof (Z.div_mod (eval_expr s offset) 32 ltac:(lia)) as HD.
 assert (HO:eval_expr s offset=32*(eval_expr s offset/32)) by nia.
 change (read_slice (norm total (read_signal s root)) (eval_expr s offset) 32=
   read_slice (read_signal s root) (32*(eval_expr s offset/32)) 32).
 rewrite read_slice_norm_inside by (try lia;nia).
 f_equal. exact HO.
Qed.

Theorem checked_bank_read proc path root total offset :
 expression_at proc path=Some (ESel 32 (EVar total root) offset) ->
 (1024<=total)%nat -> bounded32b offset=true -> forall s,
 eval_read_site proc path s=Some
   (lane_read 32 (read_signal s root) (eval_expr s offset/32)).
Proof.
 intros HC HT HB s. unfold eval_read_site. rewrite HC.
 cbn [option_map]. now rewrite (eval_packed_lane root total offset HT HB s).
Qed.

Theorem checked_bank_read_related proc path root total offset :
 expression_at proc path=Some (ESel 32 (EVar total root) offset) ->
 (1024<=total)%nat -> bounded32b offset=true -> forall s view,
 BankRelated 32 32 (read_signal s root) view ->
 eval_read_site proc path s=Some (view (eval_expr s offset/32)).
Proof.
 intros HC HT HB s view HR.
 rewrite (checked_bank_read proc path root total offset HC HT HB s).
 rewrite HR;[reflexivity|exact (proj1 (bounded32b_sound offset HB s))].
Qed.

(** An x0-projecting relation does NOT justify a raw zero-lane read.  This
    theorem therefore explicitly excludes index zero; bypass/reset evidence
    must separately justify reads of zero. *)
Theorem checked_bank_read_projected proc path root total offset :
 expression_at proc path=Some (ESel 32 (EVar total root) offset) ->
 (1024<=total)%nat -> bounded32b offset=true -> forall s view,
 (forall i,0<=i<32 ->
   (if i=?0 then 0 else lane_read 32 (read_signal s root) i)=view i) ->
 eval_expr s offset/32<>0 ->
 eval_read_site proc path s=Some (view (eval_expr s offset/32)).
Proof.
 intros HC HT HB s view HR HN.
 rewrite (checked_bank_read proc path root total offset HC HT HB s).
 specialize (HR _ (proj1 (bounded32b_sound offset HB s))).
 apply Z.eqb_neq in HN. rewrite HN in HR. now rewrite HR.
Qed.
End ExtendedSVBankRead.
Print Assumptions ExtendedSVBankRead.checked_bank_read.
Print Assumptions ExtendedSVBankRead.checked_bank_read_related.
Print Assumptions ExtendedSVBankRead.checked_bank_read_projected.
