(** Partial evaluation of expressions under known register values (template route, 2026-11-04; additive, nothing existing is changed).
    A fact list [F] holds triples (x, W, z): at the state [s] the W-bit value of signal [x] is [z] ([FHold s F]).  [pe F e]
    replaces every read [EVar w x] with [w <= W] of a known signal by the constant [norm w z], folds every operator whose
    operands are constants, short-circuits [0 & e] / [e & 0] and the one-bit [1 | e] / [e | 1], and selects the branch of a
    conditional whose guard folds to a constant.  [pe_sound]: the value is unchanged.  The result is computed by [vm_compute]
    on closed syntax (the facts are concrete control values; data registers stay variables), so a large resolved next-state
    expression collapses to its data path before any symbolic evaluation.  Generic, design independent.
    proof_author: LLM-generated: Claude Code (claude-opus-5-5); external_llm_api_calls=0. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVSymExecSym Lang.ExtendedSVSymAlias Lang.ExtendedSVBankAlignment Lang.ExtendedSVWordInvariant.
Import ListNotations ExtendedSV.
Local Open Scope Z_scope.
Module ExtendedSVPartialEval.

Definition Fact := (signal * nat * Z)%type.
Definition FHold (s:State) (F:list Fact) : Prop := forall x W z, In (x, W, z) F -> norm W (read_signal s x) = z.

Fixpoint flookup (F:list Fact) (x:signal) : option (nat * Z) :=
 match F with
 | [] => None
 | (y, W, z) :: r => if Nat.eqb x y then Some (W, z) else flookup r x
 end.
Lemma flookup_in F x W z : flookup F x = Some (W, z) -> In (x, W, z) F.
Proof. induction F as [|[[y V] zy] r IH]; cbn; [discriminate|].
 destruct (Nat.eqb x y) eqn:E.
 - intro H. injection H as <- <-. apply Nat.eqb_eq in E. subst. left. reflexivity.
 - intro H. right. exact (IH H). Qed.

(** single-bit facts: bit k of signal x is b *)
Definition BFact := (signal * Z * Z)%type.
Definition BHold (s:State) (B:list BFact) : Prop := forall x k b, In (x, k, b) B -> norm 1 (Z.shiftr (read_signal s x) k) = b.
Fixpoint blook (B:list BFact) (x:signal) (k:Z) : option Z :=
 match B with
 | [] => None
 | (y, j, b) :: r => if Nat.eqb x y && Z.eqb k j then Some b else blook r x k
 end.
Lemma blook_in B x k b : blook B x k = Some b -> In (x, k, b) B.
Proof. induction B as [|[[y j] c] r IH]; cbn; [discriminate|].
 destruct (Nat.eqb x y && Z.eqb k j) eqn:E.
 - intro H. injection H as <-. apply andb_true_iff in E as [E1 E2]. apply Nat.eqb_eq in E1. apply Z.eqb_eq in E2. subst. left. reflexivity.
 - intro H. right. exact (IH H). Qed.
Lemma norm_ones' w x : norm w x = Z.land x (Z.ones (Z.of_nat w)).
Proof. unfold norm, mask. rewrite Z.ones_equiv. reflexivity. Qed.
Lemma bit_norm W v k : 0 <= k < Z.of_nat W -> norm 1 (Z.shiftr (norm W v) k) = norm 1 (Z.shiftr v k).
Proof. intro Hk. rewrite !norm_ones'. apply Z.bits_inj'. intros n Hn.
 rewrite !Z.land_spec, !Z.shiftr_spec by lia. change (Z.of_nat 1) with 1.
 destruct (Z.eq_dec n 0) as [->|N].
 - rewrite Z.land_spec. rewrite (Z.testbit_ones_nonneg (Z.of_nat W)) by lia.
   replace (0 + k <? Z.of_nat W) with true by (symmetry; apply Z.ltb_lt; lia). rewrite andb_true_r. reflexivity.
 - rewrite (Z.testbit_ones_nonneg 1 n) by lia. replace (n <? 1) with false by (symmetry; apply Z.ltb_ge; lia). rewrite !andb_false_r. reflexivity.
Qed.

Definition cv (e:Expr) : option Z := match e with EConst w v => Some (norm w v) | _ => None end.
Lemma cv_sound s e z : cv e = Some z -> eval_expr s e = z.
Proof. destruct e; cbn; try discriminate. intro H. injection H as <-. reflexivity. Qed.

(** width-preserving wrapper: [eval (wid w e) = norm w (eval e)] *)
Definition wid (w:nat) (e:Expr) : Expr := if Nat.eqb (expr_width e) w then e else ESel w e (EConst 1 0).
Lemma wid_sound s w e : eval_expr s (wid w e) = norm w (eval_expr s e).
Proof. unfold wid. destruct (Nat.eqb (expr_width e) w) eqn:E.
 - apply Nat.eqb_eq in E. subst w. symmetry. apply ExtendedSVSymAlias.value_norm.
 - cbn [eval_expr]. change (norm 1 0) with 0. rewrite Z.shiftr_0_r. reflexivity. Qed.
Lemma wid_width w e : expr_width (wid w e) = w.
Proof. unfold wid. destruct (Nat.eqb (expr_width e) w) eqn:E; [apply Nat.eqb_eq in E; exact E|reflexivity]. Qed.

Definition binop (op:BinaryOp) (wl wr:nat) (l r:Z) : Z :=
 match op with
 | BAnd => Z.land l r | BOr => Z.lor l r | BXor => Z.lxor l r
 | BAdd => l + r | BSub => l - r | BMul => l * r
 | BEq => boolz (Z.eqb l r) | BNeq => boolz (negb (Z.eqb l r))
 | BLtU => boolz (Z.ltb l r) | BGtU => boolz (Z.gtb l r)
 | BGtS => boolz (Z.gtb (signed_value wl l) (signed_value wr r))
 | BShiftL => Z.shiftl l r | BShiftR => Z.shiftr l r
 | BShiftRS => Z.shiftr (signed_value wl l) r
 end.
Lemma eval_bin s w op l r : eval_expr s (EBinary w op l r) = norm w (binop op (expr_width l) (expr_width r) (eval_expr s l) (eval_expr s r)).
Proof. destruct op; reflexivity. Qed.

Definition mk_bin (w:nat) (op:BinaryOp) (l r:Expr) : Expr :=
 match cv l, cv r with
 | Some a, Some b => EConst w (binop op (expr_width l) (expr_width r) a b)
 | Some a, None => match op with
                   | BAnd => if Z.eqb a 0 then EConst w 0 else EBinary w op l r
                   | BOr => if Nat.eqb w 1 && Z.eqb (norm 1 a) 1 then EConst w 1 else EBinary w op l r
                   | _ => EBinary w op l r end
 | None, Some b => match op with
                   | BAnd => if Z.eqb b 0 then EConst w 0 else EBinary w op l r
                   | BOr => if Nat.eqb w 1 && Z.eqb (norm 1 b) 1 then EConst w 1 else EBinary w op l r
                   | _ => EBinary w op l r end
 | None, None => EBinary w op l r
 end.

Lemma tb0_norm1 a : norm 1 a = Z.b2z (Z.testbit a 0).
Proof. rewrite ExtendedSVBankAlignment.norm_mod. change (2 ^ Z.of_nat 1) with 2.
 rewrite <- Z.bit0_mod. reflexivity. Qed.
Lemma norm1_lor_l a b : norm 1 a = 1 -> norm 1 (Z.lor a b) = 1.
Proof. rewrite !tb0_norm1, Z.lor_spec. destruct (Z.testbit a 0); cbn; [reflexivity|discriminate]. Qed.
Lemma norm1_lor_r a b : norm 1 b = 1 -> norm 1 (Z.lor a b) = 1.
Proof. rewrite !tb0_norm1, Z.lor_spec. destruct (Z.testbit b 0); cbn; [rewrite orb_true_r; reflexivity|discriminate]. Qed.

Lemma mk_bin_sound s w op l r : eval_expr s (mk_bin w op l r) = eval_expr s (EBinary w op l r).
Proof. unfold mk_bin. rewrite eval_bin.
 destruct (cv l) as [a|] eqn:El, (cv r) as [b|] eqn:Er.
 - rewrite (cv_sound s l a El), (cv_sound s r b Er). reflexivity.
 - rewrite (cv_sound s l a El). destruct op; try (rewrite eval_bin, (cv_sound s l a El); reflexivity).
   + destruct (Z.eqb a 0) eqn:E; [|rewrite eval_bin, (cv_sound s l a El); reflexivity].
     apply Z.eqb_eq in E. subst a. cbn [eval_expr binop]. rewrite Z.land_0_l. reflexivity.
   + destruct (Nat.eqb w 1 && Z.eqb (norm 1 a) 1) eqn:E; [|rewrite eval_bin, (cv_sound s l a El); reflexivity].
     apply andb_true_iff in E as [E1 E2]. apply Nat.eqb_eq in E1. apply Z.eqb_eq in E2. subst w.
     cbn [eval_expr binop]. rewrite (norm1_lor_l _ _ E2). reflexivity.
 - rewrite (cv_sound s r b Er). destruct op; try (rewrite eval_bin, (cv_sound s r b Er); reflexivity).
   + destruct (Z.eqb b 0) eqn:E; [|rewrite eval_bin, (cv_sound s r b Er); reflexivity].
     apply Z.eqb_eq in E. subst b. cbn [eval_expr binop]. rewrite Z.land_0_r. reflexivity.
   + destruct (Nat.eqb w 1 && Z.eqb (norm 1 b) 1) eqn:E; [|rewrite eval_bin, (cv_sound s r b Er); reflexivity].
     apply andb_true_iff in E as [E1 E2]. apply Nat.eqb_eq in E1. apply Z.eqb_eq in E2. subst w.
     cbn [eval_expr binop]. rewrite (norm1_lor_r _ _ E2). reflexivity.
 - rewrite eval_bin. reflexivity.
Qed.
Lemma mk_bin_width w op l r : expr_width (mk_bin w op l r) = w.
Proof. unfold mk_bin. destruct (cv l), (cv r); try destruct op; try reflexivity;
 repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity. Qed.

(** the other operators fold only when all operands are constant *)
Definition mk_sel (w:nat) (b l:Expr) : Expr := match cv b, cv l with Some vb, Some vl => EConst w (Z.shiftr vb vl) | _, _ => ESel w b l end.
Definition mk_cat (w:nat) (h l:Expr) : Expr := match cv h, cv l with Some vh, Some vl => EConst w (Z.lor (Z.shiftl vh (Z.of_nat (expr_width l))) vl) | _, _ => EConcat w h l end.
Definition mk_rep (w c:nat) (b:Expr) : Expr := match cv b with Some v => EConst w (replicate_bits c (expr_width b) v) | None => EReplicate w c b end.
Definition mk_ext (w:nat) (sg:bool) (b:Expr) : Expr := match cv b with Some v => EConst w (if sg then signed_value (expr_width b) v else v) | None => EExtend w sg b end.
Definition mk_un (w:nat) (op:UnaryOp) (b:Expr) : Expr := match cv b with
 | Some v => EConst w (match op with UNot => Z.lnot v | UNegate => - v | URedOr => boolz (negb (Z.eqb v 0)) end)
 | None => EUnary w op b end.

Section PE.
Variable B : list BFact.
Definition pesel (F:list Fact) (w:nat) (b' l':Expr) : Expr :=
 match b', cv l' with
 | EVar W x, Some k =>
     match flookup F x with
     | Some (V, z) => if Z.leb 0 k && Z.leb (Z.of_nat w + k) (Z.of_nat W) && Z.leb (Z.of_nat w + k) (Z.of_nat V)
                      then EConst w (Z.shiftr z k)
                      else match blook B x k with
                           | Some c => if Nat.eqb w 1 && Z.ltb k (Z.of_nat W) && Z.leb 0 k then EConst 1 c else mk_sel w b' l'
                           | None => mk_sel w b' l' end
     | None => match blook B x k with
               | Some c => if Nat.eqb w 1 && Z.ltb k (Z.of_nat W) && Z.leb 0 k then EConst 1 c else mk_sel w b' l'
               | None => mk_sel w b' l' end
     end
 | _, _ => mk_sel w b' l' end.
Lemma mk_sel_width w b l : expr_width (mk_sel w b l) = w.
Proof. unfold mk_sel. destruct (cv b), (cv l); reflexivity. Qed.
Lemma pesel_width F w b l : expr_width (pesel F w b l) = w.
Proof. unfold pesel. destruct b; try apply mk_sel_width. destruct (cv l) as [k|]; [|apply mk_sel_width].
 destruct (flookup F id) as [[V z]|].
 - destruct (Z.leb 0 k && Z.leb (Z.of_nat w + k) (Z.of_nat width) && Z.leb (Z.of_nat w + k) (Z.of_nat V)); [reflexivity|].
   destruct (blook B id k) as [c|]; [|apply mk_sel_width]. destruct (Nat.eqb w 1 && Z.ltb k (Z.of_nat width) && Z.leb 0 k) eqn:E; [|apply mk_sel_width].
   apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E _]. apply Nat.eqb_eq in E. subst. reflexivity.
 - destruct (blook B id k) as [c|]; [|apply mk_sel_width]. destruct (Nat.eqb w 1 && Z.ltb k (Z.of_nat width) && Z.leb 0 k) eqn:E; [|apply mk_sel_width].
   apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E _]. apply Nat.eqb_eq in E. subst. reflexivity.
Qed.
Lemma mk_sel_sound s w b l : eval_expr s (mk_sel w b l) = eval_expr s (ESel w b l).
Proof. unfold mk_sel. destruct (cv b) as [a|] eqn:E1, (cv l) as [c|] eqn:E2; cbn [eval_expr]; try reflexivity.
 rewrite (cv_sound s _ a E1), (cv_sound s _ c E2). reflexivity. Qed.
Lemma sel_norm w W v k : 0 <= k -> Z.of_nat w + k <= Z.of_nat W -> norm w (Z.shiftr (norm W v) k) = norm w (Z.shiftr v k).
Proof. intros H0 H1. rewrite !norm_ones'. apply Z.bits_inj'. intros n Hn.
 rewrite !Z.land_spec, !Z.shiftr_spec by lia. rewrite Z.land_spec.
 destruct (Z.ltb_spec0 n (Z.of_nat w)) as [L|L].
 - rewrite (Z.testbit_ones_nonneg (Z.of_nat W)) by lia. replace (n + k <? Z.of_nat W) with true by (symmetry; apply Z.ltb_lt; lia). rewrite andb_true_r. reflexivity.
 - rewrite (Z.testbit_ones_nonneg (Z.of_nat w) n) by lia. replace (n <? Z.of_nat w) with false by (symmetry; apply Z.ltb_ge; lia). rewrite !andb_false_r. reflexivity.
Qed.
Lemma pesel_sound s F (HF:FHold s F) (HB:BHold s B) w b l : eval_expr s (pesel F w b l) = eval_expr s (ESel w b l).
Proof. unfold pesel. destruct b; try apply mk_sel_sound. destruct (cv l) as [k|] eqn:El; [|apply mk_sel_sound].
 pose proof (cv_sound s l k El) as Hl.
 assert (Gb : eval_expr s (match blook B id k with Some c => if Nat.eqb w 1 && Z.ltb k (Z.of_nat width) && Z.leb 0 k then EConst 1 c else mk_sel w (EVar width id) l
              | None => mk_sel w (EVar width id) l end) = eval_expr s (ESel w (EVar width id) l)).
 { destruct (blook B id k) as [c|] eqn:Eb; [|apply mk_sel_sound].
   destruct (Nat.eqb w 1 && Z.ltb k (Z.of_nat width) && Z.leb 0 k) eqn:Hc; [|apply mk_sel_sound].
   apply andb_true_iff in Hc as [Hc H3]. apply andb_true_iff in Hc as [H1 H2]. apply Nat.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. subst w.
   pose proof (HB id k c (blook_in B id k c Eb)) as H. cbn [eval_expr]. rewrite Hl. rewrite (bit_norm width _ k) by lia. rewrite H.
   rewrite <- H. apply ExtendedSVWordInvariant.norm_idempotent. }
 destruct (flookup F id) as [[V z]|] eqn:Ef; [|exact Gb].
 destruct (Z.leb 0 k && Z.leb (Z.of_nat w + k) (Z.of_nat width) && Z.leb (Z.of_nat w + k) (Z.of_nat V)) eqn:L; [|exact Gb].
 apply andb_true_iff in L as [L L2]. apply andb_true_iff in L as [L0 L1]. apply Z.leb_le in L0, L1, L2.
 pose proof (HF id V z (flookup_in F id V z Ef)) as H.
 cbn [eval_expr]. rewrite Hl. rewrite (sel_norm w width _ k L0 L1). rewrite <- H. rewrite (sel_norm w V _ k L0 L2). reflexivity.
Qed.
Fixpoint pe (F:list Fact) (e:Expr) : Expr :=
 match e with
 | EConst _ _ => e
 | EVar w x => match flookup F x with
               | Some (W, z) => if Nat.leb w W then EConst w z else e
               | None => e end
 | ESel w b l => pesel F w (pe F b) (pe F l)
 | EConcat w h l => mk_cat w (pe F h) (pe F l)
 | EReplicate w c b => mk_rep w c (pe F b)
 | EExtend w sg b => mk_ext w sg (pe F b)
 | EUnary w op b => mk_un w op (pe F b)
 | EBinary w op l r => mk_bin w op (pe F l) (pe F r)
 | ECond w g y n => let g' := pe F g in
     match cv g' with
     | Some z => wid w (if Z.eqb z 0 then pe F n else pe F y)
     | None => let y' := pe F y in let n' := pe F n in
               match cv y', cv n' with
               | Some a, Some b => if Z.eqb (norm w a) (norm w b) then EConst w a else ECond w g' y' n'
               | _, _ => ECond w g' y' n' end
     end
 end.

Lemma pe_width F e : expr_width (pe F e) = expr_width e.
Proof. induction e; cbn [pe expr_width]; try reflexivity.
 - destruct (flookup F id) as [[W z]|]; [destruct (Nat.leb width W)|]; reflexivity.
 - apply pesel_width.
 - unfold mk_cat. destruct (cv (pe F e1)), (cv (pe F e2)); reflexivity.
 - unfold mk_rep. destruct (cv (pe F e)); reflexivity.
 - unfold mk_ext. destruct (cv (pe F e)); reflexivity.
 - unfold mk_un. destruct (cv (pe F e)); reflexivity.
 - apply mk_bin_width.
 - destruct (cv (pe F e1)); [apply wid_width|].
   destruct (cv (pe F e2)), (cv (pe F e3)); try reflexivity. destruct (Z.eqb _ _); reflexivity.
Qed.

Theorem pe_sound s F : FHold s F -> BHold s B -> forall e, eval_expr s (pe F e) = eval_expr s e.
Proof. intros HF HB. induction e; cbn [pe].
 - reflexivity.
 - destruct (flookup F id) as [[W z]|] eqn:E; [|reflexivity].
   destruct (Nat.leb width W) eqn:L; [|reflexivity]. apply Nat.leb_le in L.
   pose proof (HF id W z (flookup_in F id W z E)) as H. cbn [eval_expr]. rewrite <- H.
   rewrite (ExtendedSVSymExecSym.norm_low width W _ L). reflexivity.
 - rewrite (pesel_sound s F HF HB). cbn [eval_expr]. rewrite IHe1, IHe2. reflexivity.
 - unfold mk_cat. cbn [eval_expr]. rewrite <- IHe1, <- IHe2, <- (pe_width F e2).
   destruct (cv (pe F e1)) as [a|] eqn:E1, (cv (pe F e2)) as [b|] eqn:E2; cbn [eval_expr]; try reflexivity.
   rewrite (cv_sound s _ a E1), (cv_sound s _ b E2). reflexivity.
 - unfold mk_rep. cbn [eval_expr]. rewrite <- IHe, <- (pe_width F e).
   destruct (cv (pe F e)) as [a|] eqn:E1; cbn [eval_expr]; try reflexivity.
   rewrite (cv_sound s _ a E1). reflexivity.
 - unfold mk_ext. cbn [eval_expr]. rewrite <- IHe, <- (pe_width F e).
   destruct (cv (pe F e)) as [a|] eqn:E1; cbn [eval_expr]; try reflexivity.
   rewrite (cv_sound s _ a E1). reflexivity.
 - unfold mk_un. cbn [eval_expr]. rewrite <- IHe.
   destruct (cv (pe F e)) as [a|] eqn:E1; cbn [eval_expr]; try reflexivity.
   rewrite (cv_sound s _ a E1). reflexivity.
 - rewrite mk_bin_sound. rewrite !eval_bin, IHe1, IHe2, !pe_width. reflexivity.
 - destruct (cv (pe F e1)) as [z|] eqn:E1.
   + rewrite wid_sound. cbn [eval_expr]. rewrite <- IHe1, (cv_sound s _ z E1).
     destruct (Z.eqb z 0); [rewrite IHe3|rewrite IHe2]; reflexivity.
   + destruct (cv (pe F e2)) as [a|] eqn:E2, (cv (pe F e3)) as [b|] eqn:E3; try (cbn [eval_expr]; rewrite IHe1, IHe2, IHe3; reflexivity).
     destruct (Z.eqb (norm width a) (norm width b)) eqn:Eab; [|cbn [eval_expr]; rewrite IHe1, IHe2, IHe3; reflexivity].
     apply Z.eqb_eq in Eab. cbn [eval_expr]. rewrite <- IHe2, <- IHe3, (cv_sound s _ a E2), (cv_sound s _ b E3).
     destruct (Z.eqb (eval_expr s e1) 0); [exact Eab|reflexivity].
Qed.

End PE.
Lemma fhold_nil s : FHold s []. Proof. intros x W z H. destruct H. Qed.
Lemma fhold_cons s x W z F : norm W (read_signal s x) = z -> FHold s F -> FHold s ((x, W, z) :: F).
Proof. intros H1 H2 y V zy [E|E]; [injection E as <- <- <-; exact H1|exact (H2 y V zy E)]. Qed.

Lemma bhold_nil s : BHold s []. Proof. intros x k b H. destruct H. Qed.
Lemma bhold_cons s x k b B : norm 1 (Z.shiftr (read_signal s x) k) = b -> BHold s B -> BHold s ((x, k, b) :: B).
Proof. intros H1 H2 y j c [E|E]; [injection E as <- <- <-; exact H1|exact (H2 y j c E)]. Qed.

(** ---- mask normal form of and/or chains with constants (a register rewritten bit by bit through part selects) ----
    [mform w e = (x, M, C)]: the w-bit value of e is the w-bit value of [(x & M) | C]; [mfold] rebuilds every width-w and/or node
    with a constant right operand in that form, and drops [x] when the mask has no bit below w. *)
Fixpoint mform (w:nat) (e:Expr) : Expr * Z * Z :=
 match e with
 | EBinary w' BAnd l (EConst wm m) => if Nat.eqb w' w then let '(x, M, C) := mform w l in (x, Z.land M (norm wm m), Z.land C (norm wm m)) else (e, -1, 0)
 | EBinary w' BOr l (EConst wc c) => if Nat.eqb w' w then let '(x, M, C) := mform w l in (x, M, Z.lor C (norm wc c)) else (e, -1, 0)
 | _ => (e, -1, 0)
 end.
Lemma norm_land_l w a b : norm w (Z.land (norm w a) b) = norm w (Z.land a b).
Proof. unfold norm. rewrite <- !Z.land_assoc, (Z.land_comm (mask w) (Z.land b (mask w))), <- Z.land_assoc, Z.land_diag. reflexivity. Qed.
Lemma norm_lor_l w a b : norm w (Z.lor (norm w a) b) = norm w (Z.lor a b).
Proof. unfold norm. rewrite !Z.land_lor_distr_l, <- Z.land_assoc, Z.land_diag. reflexivity. Qed.
Lemma mform_sound s w : forall e x M C, mform w e = (x, M, C) -> norm w (eval_expr s e) = norm w (Z.lor (Z.land (eval_expr s x) M) C).
Proof. induction e; intros x M C H; cbn [mform] in H;
 try (injection H as <- <- <-; rewrite Z.land_m1_r, Z.lor_0_r; reflexivity).
 destruct op; try (injection H as <- <- <-; rewrite Z.land_m1_r, Z.lor_0_r; reflexivity);
 (destruct e2; try (injection H as <- <- <-; rewrite Z.land_m1_r, Z.lor_0_r; reflexivity));
 (destruct (Nat.eqb width w) eqn:Ew; [|injection H as <- <- <-; rewrite Z.land_m1_r, Z.lor_0_r; reflexivity]);
 apply Nat.eqb_eq in Ew; subst width;
 destruct (mform w e1) as [[x1 M1] C1] eqn:E1; injection H as <- <- <-;
 pose proof (IHe1 x1 M1 C1 eq_refl) as IH; cbn [eval_expr].
 - rewrite ExtendedSVWordInvariant.norm_idempotent. rewrite <- norm_land_l, IH, norm_land_l. f_equal.
   rewrite Z.land_lor_distr_l, <- Z.land_assoc. reflexivity.
 - rewrite ExtendedSVWordInvariant.norm_idempotent. rewrite <- norm_lor_l, IH, norm_lor_l. f_equal. rewrite Z.lor_assoc. reflexivity.
Qed.
Definition mrebuild (w:nat) (x:Expr) (M C:Z) : Expr :=
 if Z.eqb (norm w M) 0 then EConst w C else EBinary w BOr (EBinary w BAnd x (EConst w M)) (EConst w C).
Fixpoint mfold (e:Expr) : Expr :=
 match e with
 | EConst _ _ | EVar _ _ => e
 | ESel w b l => ESel w (mfold b) (mfold l)
 | EConcat w h l => EConcat w (mfold h) (mfold l)
 | EReplicate w c b => EReplicate w c (mfold b)
 | EExtend w sg b => EExtend w sg (mfold b)
 | EUnary w op b => EUnary w op (mfold b)
 | EBinary w op l r =>
     let e' := EBinary w op (mfold l) (mfold r) in
     match op, mfold r with
     | BAnd, EConst _ _ | BOr, EConst _ _ => let '(x, M, C) := mform w e' in mrebuild w x M C
     | _, _ => e' end
 | ECond w g y n => ECond w (mfold g) (mfold y) (mfold n)
 end.
Lemma mfold_width e : expr_width (mfold e) = expr_width e.
Proof. destruct e; cbn [mfold]; try reflexivity.
 destruct op; try reflexivity; destruct (mfold e2); try reflexivity;
 match goal with |- context [mform ?w ?e] => destruct (mform w e) as [[x M] C] end; unfold mrebuild; destruct (Z.eqb _ 0); reflexivity. Qed.
Lemma lor_low_zero w a c : norm w a = 0 -> norm w (Z.lor a c) = norm w c.
Proof. intro H. rewrite <- norm_lor_l, H, Z.lor_0_l. reflexivity. Qed.
Lemma land_mask_zero w a M : norm w M = 0 -> norm w (Z.land a M) = 0.
Proof. intro H. unfold norm in *. rewrite <- Z.land_assoc, H. apply Z.land_0_r. Qed.
Lemma rebuild_eq w a M C : norm w (Z.lor (norm w (Z.land a (norm w M))) (norm w C)) = norm w (Z.lor (Z.land a M) C).
Proof. unfold norm. rewrite !Z.land_lor_distr_l, <- !Z.land_assoc, !Z.land_diag. reflexivity. Qed.
Theorem mfold_sound s : forall e, eval_expr s (mfold e) = eval_expr s e.
Proof. induction e; cbn [mfold]; try reflexivity.
 - cbn [eval_expr]. rewrite IHe1, IHe2. reflexivity.
 - cbn [eval_expr]. rewrite IHe1, IHe2, mfold_width. reflexivity.
 - cbn [eval_expr]. rewrite IHe, mfold_width. reflexivity.
 - cbn [eval_expr]. rewrite IHe, mfold_width. reflexivity.
 - cbn [eval_expr]. rewrite IHe. reflexivity.
 - assert (G : eval_expr s (EBinary width op (mfold e1) (mfold e2)) = eval_expr s (EBinary width op e1 e2))
     by (rewrite !eval_bin, IHe1, IHe2, !mfold_width; reflexivity).
   destruct op; try exact G; destruct (mfold e2) eqn:E2; try exact G;
   (destruct (mform width (EBinary width _ (mfold e1) (EConst width0 value))) as [[x M] C] eqn:Em;
    pose proof (mform_sound s width _ x M C Em) as HM; rewrite <- G;
    rewrite <- (ExtendedSVSymAlias.value_norm s (EBinary width _ (mfold e1) (EConst width0 value))); cbn [expr_width]; rewrite HM;
    unfold mrebuild; destruct (Z.eqb (norm width M) 0) eqn:EZ;
    [apply Z.eqb_eq in EZ; cbn [eval_expr]; rewrite (lor_low_zero width _ C (land_mask_zero width _ M EZ)); reflexivity
    |cbn [eval_expr]; apply rebuild_eq]).
 - cbn [eval_expr]. rewrite IHe1, IHe2, IHe3. reflexivity.
Qed.

End ExtendedSVPartialEval.
