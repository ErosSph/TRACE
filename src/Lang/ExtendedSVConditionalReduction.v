(** Proof-producing, condition-directed expression reduction.
    Facts are caller-proved equalities at ONE sampled state. No RTL transition,
    instruction decoder, history update, or environment is changed here. *)
From Coq Require Import List ZArith Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVExprAgreement
 Lang.ExtendedSVWordInvariant.
Import ListNotations ExtendedSV ExtendedSVExprAgreement ExtendedSVWordInvariant.
Module ExtendedSVConditionalReduction.

Definition Fact := (nat * signal * Z)%type.
Definition Holds (facts : list Fact) (s : State) : Prop :=
 Forall (fun f => let '(width, root, value) := f in
   norm width (read_signal s root) = norm width value) facts.

Record Reduction (facts : list Fact) (original reduced : Expr) : Prop := {
 reduction_width : expr_width reduced = expr_width original;
 reduction_value : forall s, Holds facts s ->
   eval_expr s original = eval_expr s reduced
}.

Lemma identity facts e : Reduction facts e e.
Proof. constructor; [reflexivity|intros; reflexivity]. Qed.

Lemma value_normalized s e : norm (expr_width e) (eval_expr s e) = eval_expr s e.
Proof. destruct e; cbn [expr_width eval_expr]; apply norm_idempotent. Qed.

Lemma known facts width root value : In (width, root, value) facts ->
 Reduction facts (EVar width root) (EConst width value).
Proof.
 intro HI; constructor; [reflexivity|].
 intros s HH; unfold Holds in HH; rewrite Forall_forall in HH.
 exact (HH _ HI).
Qed.

Lemma ground facts e value : expr_inputs e = [] ->
 eval_expr [] e = norm (expr_width e) value ->
 Reduction facts e (EConst (expr_width e) value).
Proof.
 intros HI HV; constructor; [reflexivity|].
 intros s _; change (eval_expr s e = norm (expr_width e) value).
 transitivity (eval_expr [] e); [|exact HV].
 apply eval_expr_agree; intros w x HX; rewrite HI in HX; contradiction.
Qed.

Lemma select facts width a a' b b' :
 Reduction facts a a' -> Reduction facts b b' ->
 Reduction facts (ESel width a b) (ESel width a' b').
Proof.
 intros [WA HA] [WB HB]; constructor; [reflexivity|].
 intros s HH; cbn [eval_expr]; now rewrite (HA s HH), (HB s HH).
Qed.

Lemma concatenate facts width a a' b b' :
 Reduction facts a a' -> Reduction facts b b' ->
 Reduction facts (EConcat width a b) (EConcat width a' b').
Proof.
 intros [WA HA] [WB HB]; constructor; [reflexivity|].
 intros s HH; cbn [eval_expr]; now rewrite (HA s HH), (HB s HH), WB.
Qed.

Lemma replicate facts width count a a' : Reduction facts a a' ->
 Reduction facts (EReplicate width count a) (EReplicate width count a').
Proof.
 intros [WA HA]; constructor; [reflexivity|].
 intros s HH; cbn [eval_expr]; now rewrite (HA s HH), WA.
Qed.

Lemma extend facts width signed a a' : Reduction facts a a' ->
 Reduction facts (EExtend width signed a) (EExtend width signed a').
Proof.
 intros [WA HA]; constructor; [reflexivity|].
 intros s HH; cbn [eval_expr]; now rewrite (HA s HH), WA.
Qed.

Lemma unary facts width op a a' : Reduction facts a a' ->
 Reduction facts (EUnary width op a) (EUnary width op a').
Proof.
 intros [WA HA]; constructor; [reflexivity|].
 intros s HH; cbn [eval_expr]; now rewrite (HA s HH).
Qed.

Lemma binary facts width op a a' b b' :
 Reduction facts a a' -> Reduction facts b b' ->
 Reduction facts (EBinary width op a b) (EBinary width op a' b').
Proof.
 intros [WA HA] [WB HB]; constructor; [reflexivity|].
 intros s HH; cbn [eval_expr]; now rewrite (HA s HH), (HB s HH), WA, WB.
Qed.

Lemma conditional facts width g g' a a' b b' :
 Reduction facts g g' -> Reduction facts a a' -> Reduction facts b b' ->
 Reduction facts (ECond width g a b) (ECond width g' a' b').
Proof.
 intros [WG HG] [WA HA] [WB HB]; constructor; [reflexivity|].
 intros s HH; cbn [eval_expr]; now rewrite (HG s HH), (HA s HH), (HB s HH).
Qed.

Lemma conditional_true facts width g gw value a a' b :
 Reduction facts g (EConst gw value) -> norm gw value <> 0%Z ->
 Reduction facts a a' ->
 Reduction facts (ECond width g a b) (EExtend width false a').
Proof.
 intros [_ HG] HNZ [_ HA]; constructor; [reflexivity|].
 intros s HH; cbn [eval_expr]; rewrite (HG s HH); cbn [eval_expr].
 destruct (Z.eqb (norm gw value) 0) eqn:HZ.
 - apply Z.eqb_eq in HZ; contradiction.
 - now rewrite (HA s HH).
Qed.

Lemma conditional_false facts width g gw value a b b' :
 Reduction facts g (EConst gw value) -> norm gw value = 0%Z ->
 Reduction facts b b' ->
 Reduction facts (ECond width g a b) (EExtend width false b').
Proof.
 intros [_ HG] HZ [_ HB]; constructor; [reflexivity|].
 intros s HH; cbn [eval_expr]; rewrite (HG s HH); cbn [eval_expr].
 rewrite HZ; cbn [Z.eqb]; now rewrite (HB s HH).
Qed.

(** If both reduced arms agree, the guard need not be evaluated or split. *)
Lemma conditional_same facts width g a b result :
 Reduction facts a result -> Reduction facts b result ->
 Reduction facts (ECond width g a b) (EExtend width false result).
Proof.
 intros [_ HA] [_ HB]; constructor; [reflexivity|].
 intros s HH; cbn [eval_expr]; rewrite (HA s HH), (HB s HH).
 destruct (Z.eqb (eval_expr s g) 0); reflexivity.
Qed.

Lemma unsigned_same_width facts width e : expr_width e = width ->
 Reduction facts (EExtend width false e) e.
Proof.
 intro HW; constructor; [exact HW|].
 intros s _; cbn [eval_expr]; rewrite <- HW; apply value_normalized.
Qed.

Lemma transitive facts a b c :
 Reduction facts a b -> Reduction facts b c -> Reduction facts a c.
Proof.
 intros [WAB HAB] [WBC HBC]; constructor; [now rewrite WBC|].
 intros s HH; exact (eq_trans (HAB s HH) (HBC s HH)).
Qed.

Theorem checked_value facts original reduced s :
 Reduction facts original reduced -> Holds facts s ->
 eval_expr s original = eval_expr s reduced.
Proof. intros HR HH; exact (reduction_value _ _ _ HR s HH). Qed.

End ExtendedSVConditionalReduction.
Print Assumptions ExtendedSVConditionalReduction.checked_value.
