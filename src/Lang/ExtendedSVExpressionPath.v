(** Checked branch selection in normalized scalar next-value expressions.
    A path supplies REAL sampled guard facts; it is not an ISA role or an
    assertion that those guards hold on all reachable CPU states. *)
From Coq Require Import List ZArith Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVWordInvariant.
Import ListNotations ExtendedSV ExtendedSVWordInvariant.
Module ExtendedSVExpressionPath.

Fixpoint expression_path (width : nat) (e : Expr) (path : list bool) {struct path} : option Expr :=
 match path with
 | [] => Some e
 | choose_yes :: rest =>
   match e with
   | ECond w guard yes no =>
     if Nat.eqb w width then expression_path width (if choose_yes then yes else no) rest
     else None
   | _ => None
   end
 end.

Fixpoint PathHolds (s : State) (e : Expr) (path : list bool) {struct path} : Prop :=
 match path with
 | [] => True
 | choose_yes :: rest =>
   match e with
   | ECond _ guard yes no =>
     Z.eqb (eval_expr s guard) 0 = negb choose_yes /\
     PathHolds s (if choose_yes then yes else no) rest
   | _ => False
   end
 end.

Theorem selected_expression_sound width path : forall e leaf s,
 expression_path width e path = Some leaf -> PathHolds s e path ->
 norm width (eval_expr s e) = norm width (eval_expr s leaf).
Proof.
 induction path as [|choose rest IH]; intros e leaf s HE HP.
 - cbn [expression_path] in HE. injection HE as HE. subst leaf. reflexivity.
 - destruct e; cbn [expression_path] in HE; try discriminate.
   destruct (Nat.eqb width0 width) eqn:HW; [|discriminate].
   apply Nat.eqb_eq in HW. subst width0.
   cbn [PathHolds] in HP. destruct HP as [HG HP].
   cbn [eval_expr]. rewrite norm_idempotent, HG.
   destruct choose; cbn [negb] in *; exact (IH _ leaf s HE HP).
Qed.

Print Assumptions selected_expression_sound.
End ExtendedSVExpressionPath.
