(** Resolution of expressions through known wire bindings (template route, 2026-11-04; additive, nothing existing is changed).
    A binding list [m] holds triples (x, W, ex): at the state [s], the W-bit value of signal [x] equals the W-bit value of the
    expression [ex] ([Binds s m]).  [esub m e] replaces every read [EVar w x] with [w <= W] of a bound signal by
    [ESel w ex 0] (the low w bits of ex); [esub_sound]: the value of every expression is unchanged.  A generator resolves a
    next-state or wire expression through all single-assignment combinational wires in topological order (each binding is the
    [checked_assignment_binding] of the wire, already resolved), so the result reads only registers and outputs of the
    multi-statement processes.  Generic, design independent.
    proof_author: LLM-generated: Claude Code (claude-opus-5-5); external_llm_api_calls=0. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVSymExecSym Lang.ExtendedSVSymAlias Lang.ExtendedSVExprAgreement.
Import ListNotations ExtendedSV ExtendedSVExprAgreement.
Local Open Scope Z_scope.
Module ExtendedSVExprResolve.

Definition Bind := (signal * nat * Expr)%type.
Definition Binds (s:State) (m:list Bind) : Prop :=
 forall x W ex, In (x, W, ex) m -> norm W (read_signal s x) = norm W (eval_expr s ex).

Fixpoint blookup (m:list Bind) (x:signal) : option (nat * Expr) :=
 match m with
 | [] => None
 | (y, W, ex) :: r => if Nat.eqb x y then Some (W, ex) else blookup r x
 end.

Lemma blookup_in m x W ex : blookup m x = Some (W, ex) -> In (x, W, ex) m.
Proof. induction m as [|[[y V] ey] r IH]; cbn; [discriminate|].
 destruct (Nat.eqb x y) eqn:E.
 - intro H. injection H as <- <-. apply Nat.eqb_eq in E. subst. left. reflexivity.
 - intro H. right. exact (IH H). Qed.

Fixpoint esub (m:list Bind) (e:Expr) : Expr :=
 match e with
 | EConst _ _ => e
 | EVar w x => match blookup m x with
               | Some (W, ex) => if Nat.leb w W then (if Nat.eqb w W && Nat.eqb (expr_width ex) W then ex else ESel w ex (EConst 1 0)) else e
               | None => e end
 | ESel w b l => ESel w (esub m b) (esub m l)
 | EConcat w h l => EConcat w (esub m h) (esub m l)
 | EReplicate w c b => EReplicate w c (esub m b)
 | EExtend w sg b => EExtend w sg (esub m b)
 | EUnary w o b => EUnary w o (esub m b)
 | EBinary w o l r => EBinary w o (esub m l) (esub m r)
 | ECond w g t f => ECond w (esub m g) (esub m t) (esub m f)
 end.

Lemma esub_width m e : expr_width (esub m e) = expr_width e.
Proof. destruct e; cbn; try reflexivity.
 destruct (blookup m id) as [[W ex]|]; [|reflexivity]. destruct (Nat.leb width W); [|reflexivity].
 destruct (Nat.eqb width W && Nat.eqb (expr_width ex) W) eqn:E; [|reflexivity].
 apply andb_true_iff in E as [E1 E2]. apply Nat.eqb_eq in E1, E2. subst. reflexivity. Qed.

Theorem esub_sound s m : Binds s m -> forall e, eval_expr s (esub m e) = eval_expr s e.
Proof. intro HB. induction e; cbn [esub eval_expr]; try rewrite ?esub_width; try rewrite ?IHe; try rewrite ?IHe1; try rewrite ?IHe2; try rewrite ?IHe3; try reflexivity.
 destruct (blookup m id) as [[W ex]|] eqn:E; [|reflexivity].
 destruct (Nat.leb width W) eqn:L; [|reflexivity].
 apply Nat.leb_le in L. pose proof (HB id W ex (blookup_in m id W ex E)) as H.
 destruct (Nat.eqb width W && Nat.eqb (expr_width ex) W) eqn:E3.
 { apply andb_true_iff in E3 as [E1 E2]. apply Nat.eqb_eq in E1, E2. subst W. cbn [eval_expr]. rewrite H.
   rewrite <- E2. symmetry. exact (ExtendedSVSymAlias.value_norm s ex). }
 cbn [eval_expr]. change (norm 1 0) with 0. rewrite Z.shiftr_0_r.
 rewrite <- (ExtendedSVSymExecSym.norm_low width W (eval_expr s ex) L).
 rewrite <- H. rewrite (ExtendedSVSymExecSym.norm_low width W _ L). reflexivity.
Qed.

Lemma binds_nil s : Binds s []. Proof. intros x W ex H. destruct H. Qed.
Lemma binds_cons s x W ex m : norm W (read_signal s x) = norm W (eval_expr s ex) -> Binds s m -> Binds s ((x, W, ex) :: m).
Proof. intros H1 H2 y V ey [E|E]; [injection E as <- <- <-; exact H1|exact (H2 y V ey E)]. Qed.

(** the step a generated binding lemma uses: a wire bound to [e] is also bound to the resolved [esub m e] *)
Theorem resolve_bind s m x W e : Binds s m -> norm W (read_signal s x) = norm W (eval_expr s e) ->
 norm W (read_signal s x) = norm W (eval_expr s (esub m e)).
Proof. intros HB H. rewrite (esub_sound s m HB e). exact H. Qed.

(** ---- cross-state substitution: the value of an expression over the registers of a NEXT state [t], computed in the
    driven state [s] of the previous one, when every register it reads has a binding (its next-state expression) ---- *)
Definition Binds2 (s t:State) (m:list Bind) : Prop :=
 forall x W ex, In (x, W, ex) m -> norm W (read_signal t x) = norm W (eval_expr s ex).
Definition covers (m:list Bind) (e:Expr) : bool :=
 forallb (fun wx => match blookup m (snd wx) with Some (W, _) => Nat.leb (fst wx) W | None => false end) (expr_inputs e).

Theorem esub_sound2 s t m : Binds2 s t m -> forall e, covers m e = true -> eval_expr s (esub m e) = eval_expr t e.
Proof. intro HB. unfold covers. induction e; cbn [esub eval_expr expr_inputs]; intro HC; rewrite ?forallb_app in HC; rewrite ?andb_true_iff in HC;
 try rewrite ?esub_width.
 - reflexivity.
 - cbn [forallb fst snd] in HC. rewrite andb_true_r in HC.
   destruct (blookup m id) as [[W ex]|] eqn:E; [|discriminate]. rewrite HC.
   apply Nat.leb_le in HC. pose proof (HB id W ex (blookup_in m id W ex E)) as H.
   destruct (Nat.eqb width W && Nat.eqb (expr_width ex) W) eqn:E3.
   + apply andb_true_iff in E3 as [E1 E2]. apply Nat.eqb_eq in E1, E2. subst W. rewrite H.
     rewrite <- E2. symmetry. exact (ExtendedSVSymAlias.value_norm s ex).
   + cbn [eval_expr]. change (norm 1 0) with 0. rewrite Z.shiftr_0_r.
     rewrite <- (ExtendedSVSymExecSym.norm_low width W (read_signal t id) HC).
     rewrite H. rewrite (ExtendedSVSymExecSym.norm_low width W _ HC). reflexivity.
 - destruct HC as [H1 H2]. rewrite (IHe1 H1), (IHe2 H2). reflexivity.
 - destruct HC as [H1 H2]. rewrite (IHe1 H1), (IHe2 H2). reflexivity.
 - rewrite (IHe HC). reflexivity.
 - rewrite (IHe HC). reflexivity.
 - rewrite (IHe HC). reflexivity.
 - destruct HC as [H1 H2]. rewrite (IHe1 H1), (IHe2 H2). reflexivity.
 - destruct HC as [H1 [H2 H3]]. rewrite (IHe1 H1), (IHe2 H2), (IHe3 H3). reflexivity.
Qed.
Lemma binds2_nil s t : Binds2 s t []. Proof. intros x W ex H. destruct H. Qed.
Lemma binds2_cons s t x W ex m : norm W (read_signal t x) = norm W (eval_expr s ex) -> Binds2 s t m -> Binds2 s t ((x, W, ex) :: m).
Proof. intros H1 H2 y V ey [E|E]; [injection E as <- <- <-; exact H1|exact (H2 y V ey E)]. Qed.

End ExtendedSVExprResolve.
