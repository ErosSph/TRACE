(**
  A normalized, elaboration-independent SystemVerilog runtime language.

  Real SystemVerilog front-ends eliminate packages, typedefs, enums and
  generate constructs before producing this language.  Unlike an unchecked
  behavioural summary, every remaining expression, statement and event is
  represented here and has an executable Rocq meaning.  The language is
  deliberately name-agnostic: front-ends allocate natural-number signal
  identifiers and supply a separately checked provenance table.

  This file is an opt-in conservative extension.  It does not alter the
  OOPSLA'25 [Syntax]/[Semantics] definitions.
 *)
From Coq Require Import ZArith List Bool Lia Sorting.Permutation btauto.Btauto.
Import ListNotations.
Local Open Scope Z_scope.

Module ExtendedSV.

  Definition signal := nat.
  Definition State := list Z.

  Fixpoint read_signal (s : State) (x : signal) : Z :=
    match s, x with
    | [], _ => 0
    | v :: _, O => v
    | _ :: s', S x' => read_signal s' x'
    end.

  Fixpoint write_signal (s : State) (x : signal) (v : Z) : State :=
    match s, x with
    | [], O => [v]
    | [], S x' => 0 :: write_signal [] x' v
    | _ :: s', O => v :: s'
    | h :: s', S x' => h :: write_signal s' x' v
    end.

  Definition mask (width : nat) : Z := 2 ^ Z.of_nat width - 1.
  Definition norm (width : nat) (v : Z) : Z := Z.land v (mask width).

  Definition write_slice (old lsb width value : Z) : Z :=
    let field_mask := Z.shiftl (2 ^ width - 1) lsb in
    Z.lor (Z.land old (Z.lnot field_mask))
      (Z.land (Z.shiftl value lsb) field_mask).

  Inductive UnaryOp := UNot | UNegate | URedOr.
  Inductive BinaryOp :=
  | BAnd | BOr | BXor | BAdd | BSub | BMul
  | BEq | BNeq | BLtU | BGtU | BGtS
  | BShiftL | BShiftR | BShiftRS.

  Inductive Expr : Type :=
  | EConst (width : nat) (value : Z)
  | EVar (width : nat) (id : signal)
  | ESel (width : nat) (base lsb : Expr)
  | EConcat (width : nat) (high low : Expr)
  | EReplicate (width count : nat) (body : Expr)
  | EExtend (width : nat) (signed : bool) (body : Expr)
  | EUnary (width : nat) (op : UnaryOp) (body : Expr)
  | EBinary (width : nat) (op : BinaryOp) (lhs rhs : Expr)
  | ECond (width : nat) (guard yes no : Expr).

  Definition expr_width (e : Expr) : nat :=
    match e with
    | EConst w _ | EVar w _ | ESel w _ _ | EConcat w _ _
    | EReplicate w _ _ | EExtend w _ _ | EUnary w _ _
    | EBinary w _ _ _ | ECond w _ _ _ => w
    end.

  Definition boolz (b : bool) : Z := if b then 1 else 0.
  Definition signed_value (width : nat) (v : Z) : Z :=
    let v' := norm width v in
    if (width =? 0)%nat then 0
    else if Z.testbit v' (Z.of_nat (Nat.pred width))
         then v' - 2 ^ Z.of_nat width else v'.

  Fixpoint replicate_bits (count body_width : nat) (v : Z) : Z :=
    match count with
    | O => 0
    | S n => Z.lor (Z.shiftl (replicate_bits n body_width v)
                      (Z.of_nat body_width)) (norm body_width v)
    end.

  Fixpoint eval_expr (s : State) (e : Expr) : Z :=
    match e with
    | EConst w v => norm w v
    | EVar w x => norm w (read_signal s x)
    | ESel w base lsb =>
        norm w (Z.shiftr (eval_expr s base) (eval_expr s lsb))
    | EConcat w high low =>
        norm w (Z.lor (Z.shiftl (eval_expr s high)
                          (Z.of_nat (expr_width low))) (eval_expr s low))
    | EReplicate w count body =>
        norm w (replicate_bits count (expr_width body) (eval_expr s body))
    | EExtend w signed body =>
        norm w (if signed then signed_value (expr_width body) (eval_expr s body)
                else eval_expr s body)
    | EUnary w op body =>
        let v := eval_expr s body in
        norm w (match op with
                | UNot => Z.lnot v
                | UNegate => - v
                | URedOr => boolz (negb (Z.eqb v 0))
                end)
    | EBinary w op lhs rhs =>
        let l := eval_expr s lhs in
        let r := eval_expr s rhs in
        norm w
          (match op with
           | BAnd => Z.land l r | BOr => Z.lor l r | BXor => Z.lxor l r
           | BAdd => l + r | BSub => l - r | BMul => l * r
           | BEq => boolz (Z.eqb l r) | BNeq => boolz (negb (Z.eqb l r))
           | BLtU => boolz (Z.ltb l r) | BGtU => boolz (Z.gtb l r)
           | BGtS => boolz (Z.gtb (signed_value (expr_width lhs) l)
                                   (signed_value (expr_width rhs) r))
           | BShiftL => Z.shiftl l r | BShiftR => Z.shiftr l r
           | BShiftRS => Z.shiftr (signed_value (expr_width lhs) l) r
           end)
    | ECond w guard yes no =>
        norm w (if Z.eqb (eval_expr s guard) 0
                then eval_expr s no else eval_expr s yes)
    end.

  Inductive LValue : Type :=
  | LVar (width : nat) (id : signal)
  | LSel (width : nat) (base : LValue) (lsb : Expr).

  Fixpoint lvalue_root (lv : LValue) : signal :=
    match lv with LVar _ x => x | LSel _ base _ => lvalue_root base end.

  Fixpoint lvalue_width (lv : LValue) : nat :=
    match lv with LVar w _ | LSel w _ _ => w end.

  Fixpoint assign_lvalue (s : State) (lv : LValue) (v : Z) : State :=
    match lv with
    | LVar w x => write_signal s x (norm w v)
    | LSel w base lsb =>
        let root := lvalue_root base in
        let old := read_signal s root in
        let shifted := write_slice old (eval_expr s lsb) (Z.of_nat w) v in
        assign_lvalue s base shifted
    end.

  Record Update := {
    update_signal : signal;
    update_offset : Z;
    update_width : nat;
    update_value : Z
  }.

  Fixpoint resolve_lvalue (s : State) (lv : LValue) : signal * Z * nat :=
    match lv with
    | LVar width id => (id, 0, width)
    | LSel width base lsb =>
        let '(id, base_offset, _) := resolve_lvalue s base in
        (id, base_offset + eval_expr s lsb, width)
    end.

  Definition resolve_update (s : State) (lv : LValue) (value : Z) : Update :=
    let '(id, offset, width) := resolve_lvalue s lv in
    {| update_signal := id; update_offset := offset;
       update_width := width; update_value := norm width value |}.

  Definition apply_update (s : State) (update : Update) : State :=
    let id := update.(update_signal) in
    write_signal s id
      (write_slice (read_signal s id) update.(update_offset)
        (Z.of_nat update.(update_width)) update.(update_value)).

  Definition update_mask (update : Update) : Z :=
    Z.shiftl (2 ^ Z.of_nat update.(update_width) - 1) update.(update_offset).

  Definition updates_compatibleb (first second : Update) : bool :=
    orb (negb (Nat.eqb first.(update_signal) second.(update_signal)))
      (orb (Z.eqb (Z.land (update_mask first) (update_mask second)) 0)
           (andb (Nat.eqb first.(update_signal) second.(update_signal))
             (andb (Z.eqb first.(update_offset) second.(update_offset))
               (andb (Nat.eqb first.(update_width) second.(update_width))
                     (Z.eqb first.(update_value) second.(update_value)))))).

  Fixpoint all_updates_commuteb (updates : list Update) : bool :=
    match updates with
    | [] => true
    | update :: rest =>
        andb (forallb (updates_compatibleb update) rest)
          (all_updates_commuteb rest)
    end.

  Definition update_roots (updates : list Update) : list signal :=
    nodup Nat.eq_dec (map update_signal updates).

  Definition updates_for_root (root : signal) (updates : list Update) : list Update :=
    filter (fun update => Nat.eqb update.(update_signal) root) updates.

  Definition grouped_updates_commuteb (updates : list Update) : bool :=
    forallb (fun root => all_updates_commuteb (updates_for_root root updates))
      (update_roots updates).

  Inductive Stmt : Type :=
  | SSkip
  | SAssign (nonblocking : bool) (rhs : Expr) (lhs : LValue)
  | SSeq (statements : list Stmt)
  | SIf (guard : Expr) (yes no : Stmt)
  | SCase (scrutinee : Expr) (arms : list (option Expr * Stmt)).

  Record ExecState := {
    blocking_state : State;
    pending_nba : list Update;
    emitted_updates : list Update
  }.

  (** The case selector is exposed separately from [exec_stmt] so clients can
      prove structural properties (for example, writer-set and projection
      preservation) without unfolding the whole statement interpreter.  It
      is exactly the local recursive selector previously embedded in the
      [SCase] branch of [exec_stmt]. *)
  Fixpoint select_case_stmt (s : State) (value : Z)
      (arms : list (option Expr * Stmt)) (default : Stmt) : Stmt :=
    match arms with
    | [] => default
    | (None, body) :: rest => select_case_stmt s value rest body
    | (Some key, body) :: rest =>
        if Z.eqb value (eval_expr s key)
        then body else select_case_stmt s value rest default
    end.

  Fixpoint exec_stmt (fuel : nat) (st : Stmt) (es : ExecState) : ExecState :=
    match fuel with
    | O => es
    | S fuel' =>
      match st with
      | SSkip => es
      | SAssign nba rhs lhs =>
          let value := eval_expr es.(blocking_state) rhs in
          let update := resolve_update es.(blocking_state) lhs value in
          if nba
          then {| blocking_state := es.(blocking_state);
                  pending_nba := es.(pending_nba) ++ [update];
                  emitted_updates := es.(emitted_updates) ++ [update] |}
          else {| blocking_state := apply_update es.(blocking_state) update;
                  pending_nba := es.(pending_nba);
                  emitted_updates := es.(emitted_updates) ++ [update] |}
      | SSeq statements =>
          fold_left (fun es' st' => exec_stmt fuel' st' es') statements es
      | SIf guard yes no =>
          exec_stmt fuel' (if Z.eqb (eval_expr es.(blocking_state) guard) 0
                           then no else yes) es
      | SCase scrutinee arms =>
          let value := eval_expr es.(blocking_state) scrutinee in
          exec_stmt fuel'
            (select_case_stmt es.(blocking_state) value arms SSkip) es
      end
    end.

  Fixpoint apply_nba (s : State) (updates : list Update) : State :=
    match updates with
    | [] => s
    | update :: rest => apply_nba (apply_update s update) rest
    end.

  Inductive Edge := AnyChange | Posedge | Negedge.
  Record EventSpec := { event_edge : Edge; event_signal : signal }.
  Record Event := { changed_signal : signal; old_value : Z; new_value : Z }.

  Definition edge_fires (edge : Edge) (old new : Z) : bool :=
    match edge with
    | AnyChange => negb (Z.eqb old new)
    | Posedge => andb (Z.eqb old 0) (negb (Z.eqb new 0))
    | Negedge => andb (negb (Z.eqb old 0)) (Z.eqb new 0)
    end.

  Definition event_spec_matches (ev : Event) (spec : EventSpec) : bool :=
    andb (Nat.eqb ev.(changed_signal) spec.(event_signal))
      (edge_fires spec.(event_edge) ev.(old_value) ev.(new_value)).

  Inductive ProcessKind := Initial | Combinational | Sequential.
  Record Process := {
    process_kind : ProcessKind;
    process_events : list EventSpec;
    process_body : Stmt;
    process_source_line : nat
  }.

  Definition process_matches (ev : Event) (p : Process) : bool :=
    match p.(process_kind) with
    | Sequential => existsb (event_spec_matches ev) p.(process_events)
    | _ => false
    end.

  Fixpoint stmt_writers (st : Stmt) : list signal :=
    match st with
    | SSkip => []
    | SAssign _ _ lhs => [lvalue_root lhs]
    | SSeq statements => flat_map stmt_writers statements
    | SIf _ yes no => stmt_writers yes ++ stmt_writers no
    | SCase _ arms => flat_map (fun arm => stmt_writers (snd arm)) arms
    end.

  Definition process_writers (p : Process) := stmt_writers p.(process_body).

  Record Program := {
    signal_count : nat;
    processes : list Process;
    statement_fuel : nat;
    lfp_fuel : nat
  }.

  Definition run_process (p : Program) (s : State) (proc : Process) : State :=
    let result := exec_stmt p.(statement_fuel) proc.(process_body)
      {| blocking_state := s; pending_nba := []; emitted_updates := [] |} in
    apply_nba result.(blocking_state) result.(pending_nba).

  Definition is_initial (proc : Process) : bool :=
    match proc.(process_kind) with Initial => true | _ => false end.

  Definition initialize (p : Program) (seed : State) : State :=
    fold_left (run_process p) (filter is_initial p.(processes)) seed.

  Definition process_updates (p : Program) (s : State) (proc : Process)
      : list Update :=
    let result := exec_stmt p.(statement_fuel) proc.(process_body)
      {| blocking_state := s; pending_nba := []; emitted_updates := [] |} in
    result.(emitted_updates).

  Fixpoint apply_updates (s : State) (updates : list Update) : State :=
    match updates with
    | [] => s
    | update :: rest => apply_updates (apply_update s update) rest
    end.

  Definition selected_processes (p : Program) (ev : Event) : list Process :=
    filter (process_matches ev) p.(processes).

  Definition execute_order (p : Program) (ev : Event) (pre : State)
      (order : list Process) : State :=
    apply_updates pre (flat_map (process_updates p pre) order).

  (** The standard side deliberately exposes scheduling order.  A supported
      design must prove that every legal permutation has the same result. *)
  Inductive StandardSVExecution (p : Program) (ev : Event) (pre : State)
      : State -> Prop :=
  | StandardSVExecutionOrder : forall order,
      Permutation.Permutation order (selected_processes p ev) ->
      StandardSVExecution p ev pre (execute_order p ev pre order).

  Definition ExtendedSemantics (p : Program) (ev : Event) (pre : State) : State :=
    execute_order p ev pre (selected_processes p ev).

  Definition ScheduleIndependent (p : Program) : Prop :=
    forall ev pre order,
      Permutation.Permutation order (selected_processes p ev) ->
      execute_order p ev pre order = ExtendedSemantics p ev pre.

  Definition NoScheduleConflict (p : Program) : Prop :=
    forall ev pre,
      NoDup (map update_signal
        (flat_map (process_updates p pre) (selected_processes p ev))).

  Lemma write_signal_commute : forall s x y vx vy,
      x <> y ->
      write_signal (write_signal s x vx) y vy =
      write_signal (write_signal s y vy) x vx.
  Proof.
    intros s x. revert s.
    induction x as [|x IH]; intros s [|y] vx vy Hneq;
      try contradiction; destruct s; simpl; try reflexivity.
    all: f_equal; apply IH; congruence.
  Qed.

  Lemma read_signal_write_other : forall s x y value,
      x <> y ->
      read_signal (write_signal s x value) y = read_signal s y.
  Proof.
    intros s x. revert s.
    induction x as [|x IH]; intros s [|y] value Hneq;
      try contradiction; destruct s; simpl; try reflexivity.
    all: apply IH; congruence.
  Qed.

  Lemma read_signal_write_same : forall s x value,
      read_signal (write_signal s x value) x = value.
  Proof.
    intros s x. revert s.
    induction x as [|x IH]; intros [|h s] value; simpl; auto.
  Qed.

  Lemma write_signal_write_same : forall s x first second,
      write_signal (write_signal s x first) x second =
      write_signal s x second.
  Proof.
    intros s x. revert s.
    induction x as [|x IH]; intros [|h s] first second; simpl; auto.
    all: f_equal; apply IH.
  Qed.

  Lemma write_slice_commute_disjoint : forall old o1 w1 v1 o2 w2 v2,
      Z.land (Z.shiftl (2 ^ w1 - 1) o1)
             (Z.shiftl (2 ^ w2 - 1) o2) = 0 ->
      write_slice (write_slice old o1 w1 v1) o2 w2 v2 =
      write_slice (write_slice old o2 w2 v2) o1 w1 v1.
  Proof.
    intros old o1 w1 v1 o2 w2 v2 Hdis.
    apply Z.bits_inj. intros bit.
    destruct (Z_lt_ge_dec bit 0) as [Hneg|Hnonneg].
    - repeat rewrite Z.testbit_neg_r by assumption. reflexivity.
    - unfold write_slice.
      repeat rewrite Z.lor_spec.
      repeat rewrite Z.land_spec.
      repeat rewrite Z.lor_spec.
      repeat rewrite Z.land_spec.
      repeat rewrite Z.lnot_spec by lia.
      assert (Z.testbit
        (Z.land (Z.shiftl (2 ^ w1 - 1) o1)
                (Z.shiftl (2 ^ w2 - 1) o2)) bit = false) as Hbit.
      { rewrite Hdis. apply Z.bits_0. }
      rewrite Z.land_spec in Hbit.
      apply Bool.andb_false_iff in Hbit.
      destruct Hbit as [Hbit|Hbit]; rewrite Hbit; btauto.
  Qed.

  Lemma apply_update_commute : forall s first second,
      update_signal first <> update_signal second ->
      apply_update (apply_update s first) second =
      apply_update (apply_update s second) first.
  Proof.
    intros s [x xo xw xv] [y yo yw yv] Hneq.
    unfold apply_update; simpl in *.
    rewrite read_signal_write_other by exact Hneq.
    rewrite read_signal_write_other by congruence.
    apply write_signal_commute. exact Hneq.
  Qed.

  Lemma apply_update_commute_disjoint : forall s first second,
      update_signal first = update_signal second ->
      Z.land (update_mask first) (update_mask second) = 0 ->
      apply_update (apply_update s first) second =
      apply_update (apply_update s second) first.
  Proof.
    intros s [x xo xw xv] [y yo yw yv] Hsignal Hdis.
    simpl in Hsignal; subst y.
    unfold apply_update, update_mask in *; simpl in *.
    rewrite !read_signal_write_same.
    rewrite !write_signal_write_same.
    f_equal. apply write_slice_commute_disjoint. exact Hdis.
  Qed.

  Lemma updates_compatibleb_commute : forall first second,
      updates_compatibleb first second = true ->
      forall s,
        apply_update (apply_update s first) second =
        apply_update (apply_update s second) first.
  Proof.
    intros [x xo xw xv] [y yo yw yv].
    unfold updates_compatibleb; simpl.
    repeat rewrite orb_true_iff. intros [Hdifferent | [Hdisjoint | Hequal]] s.
    - apply apply_update_commute. apply Bool.negb_true_iff in Hdifferent.
      apply Nat.eqb_neq in Hdifferent. exact Hdifferent.
    - destruct (Nat.eq_dec x y) as [Heq|Hneq].
      + apply apply_update_commute_disjoint; simpl; auto.
        apply Z.eqb_eq in Hdisjoint. exact Hdisjoint.
      + apply apply_update_commute. simpl. exact Hneq.
    - repeat rewrite andb_true_iff in Hequal.
      destruct Hequal as [Hxy [Hoff [Hw Hv]]].
      apply Nat.eqb_eq in Hxy; apply Z.eqb_eq in Hoff;
        apply Nat.eqb_eq in Hw; apply Z.eqb_eq in Hv.
      subst. reflexivity.
  Qed.

  Lemma apply_updates_swap : forall s first second rest,
      update_signal first <> update_signal second ->
      apply_updates s (first :: second :: rest) =
      apply_updates s (second :: first :: rest).
  Proof.
    simpl. intros. rewrite apply_update_commute by assumption. reflexivity.
  Qed.

  Lemma apply_updates_permutation : forall us1 us2,
      Permutation us1 us2 ->
      NoDup (map update_signal us1) ->
      forall s, apply_updates s us1 = apply_updates s us2.
  Proof.
    intros us1 us2 Hperm. induction Hperm; intros Hnd s; simpl in *.
    - reflexivity.
    - inversion Hnd; subst. simpl.
      apply IHHperm.
      exact H2.
    - inversion Hnd as [|? ? Hnotin Htail]; subst.
      inversion Htail as [|? ? Hnotin' Hrest]; subst.
      apply apply_updates_swap.
      intro Heq. apply Hnotin. left. symmetry. exact Heq.
    - rewrite (IHHperm1 Hnd s).
      apply IHHperm2.
      apply (Permutation_NoDup (Permutation_map update_signal Hperm1)). exact Hnd.
  Qed.

  Definition UpdatesCommute (first second : Update) : Prop :=
    forall s,
      apply_update (apply_update s first) second =
      apply_update (apply_update s second) first.

  Definition AllUpdatesCommute (updates : list Update) : Prop :=
    forall first second,
      In first updates -> In second updates -> UpdatesCommute first second.

  Lemma all_updates_commuteb_sound : forall updates,
      all_updates_commuteb updates = true -> AllUpdatesCommute updates.
  Proof.
    induction updates as [|head rest IH]; simpl; intros Hcheck first second Hfirst Hsecond.
    - contradiction.
    - apply andb_true_iff in Hcheck as [Hhead Hrest].
      destruct Hfirst as [<-|Hfirst]; destruct Hsecond as [<-|Hsecond].
      + unfold UpdatesCommute. intros; reflexivity.
      + apply forallb_forall with (x := second) in Hhead; auto.
        exact (updates_compatibleb_commute head second Hhead).
      + unfold UpdatesCommute. intros s. symmetry.
        apply forallb_forall with (x := first) in Hhead; auto.
        exact (updates_compatibleb_commute head first Hhead s).
      + eapply IH; eauto.
  Qed.

  Lemma grouped_updates_commuteb_sound : forall updates,
      grouped_updates_commuteb updates = true -> AllUpdatesCommute updates.
  Proof.
    intros updates Hcheck first second Hfirst Hsecond.
    destruct (Nat.eq_dec (update_signal first) (update_signal second)) as [Heq|Hneq].
    - set (root := update_signal first).
      assert (Hroot : In root (update_roots updates)).
      { unfold update_roots. apply (proj2 (nodup_In _ _ _)).
        apply in_map. exact Hfirst. }
      unfold grouped_updates_commuteb in Hcheck.
      apply forallb_forall with (x := root) in Hcheck; [|exact Hroot].
      pose proof (all_updates_commuteb_sound _ Hcheck) as Hall.
      apply Hall.
      + apply filter_In. split; [exact Hfirst|].
        apply Nat.eqb_eq. reflexivity.
      + apply filter_In. split; [exact Hsecond|].
        apply Nat.eqb_eq. symmetry. exact Heq.
    - unfold UpdatesCommute. intros s.
      apply apply_update_commute. exact Hneq.
  Qed.

  Lemma all_updates_commute_permutation : forall first second,
      Permutation first second ->
      AllUpdatesCommute first -> AllUpdatesCommute second.
  Proof.
    intros first second Hperm Hall x y Hx Hy.
    apply Hall.
    - exact (Permutation_in x (Permutation_sym Hperm) Hx).
    - exact (Permutation_in y (Permutation_sym Hperm) Hy).
  Qed.

  Lemma apply_updates_permutation_commuting : forall us1 us2,
      Permutation us1 us2 ->
      AllUpdatesCommute us1 ->
      forall s, apply_updates s us1 = apply_updates s us2.
  Proof.
    intros us1 us2 Hperm. induction Hperm; intros Hall s; simpl.
    - reflexivity.
    - apply IHHperm.
      unfold AllUpdatesCommute in *. intros.
      apply Hall; simpl; auto.
    - rewrite (Hall x y); simpl; auto.
    - rewrite (IHHperm1 Hall s).
      apply IHHperm2.
      eapply all_updates_commute_permutation; eauto.
  Qed.

  Lemma process_updates_permutation : forall p pre order selected,
      Permutation order selected ->
      Permutation (flat_map (process_updates p pre) order)
                  (flat_map (process_updates p pre) selected).
  Proof.
    intros. now apply Permutation_flat_map.
  Qed.

  Theorem no_schedule_conflict_implies_independent : forall p,
      NoScheduleConflict p -> ScheduleIndependent p.
  Proof.
    intros p Hconf ev pre order Horder.
    unfold execute_order, ExtendedSemantics.
    eapply apply_updates_permutation.
    - apply process_updates_permutation. exact Horder.
    - apply (Permutation_NoDup
        (Permutation_map update_signal
          (Permutation_sym (process_updates_permutation p pre order
            (selected_processes p ev) Horder)))).
      apply Hconf.
  Qed.

  Theorem extended_to_standard : forall p ev pre,
      StandardSVExecution p ev pre (ExtendedSemantics p ev pre).
  Proof.
    intros. constructor. apply Permutation.Permutation_refl.
  Qed.

  Theorem standard_to_extended : forall p,
      ScheduleIndependent p ->
      forall ev pre post,
        StandardSVExecution p ev pre post ->
        post = ExtendedSemantics p ev pre.
  Proof.
    intros p Hind ev pre post Hstd. inversion Hstd; subst. eauto.
  Qed.

  Theorem extended_standard_equiv : forall p,
      ScheduleIndependent p ->
      forall ev pre post,
        post = ExtendedSemantics p ev pre <->
        StandardSVExecution p ev pre post.
  Proof.
    intros p Hind ev pre post. split.
    - intros ->. apply extended_to_standard.
    - intros H. eapply standard_to_extended; eauto.
  Qed.

  Theorem extended_standard_confluence : forall p,
      ScheduleIndependent p ->
      forall ev pre post1 post2,
        StandardSVExecution p ev pre post1 ->
        StandardSVExecution p ev pre post2 ->
        post1 = post2.
  Proof.
    intros p Hind ev pre post1 post2 H1 H2.
    pose proof (standard_to_extended p Hind ev pre post1 H1) as E1.
    pose proof (standard_to_extended p Hind ev pre post2 H2) as E2.
    congruence.
  Qed.

  (** [MTrs] and LFP views used by front-end clients.  Combinational logic is
      represented by the normalized program too; [comb_round] is a total
      executable transfer and [CombLFP] is its standard least-fixed-point
      closure. *)
  Definition is_comb (proc : Process) : bool :=
    match proc.(process_kind) with Combinational => true | _ => false end.

  Definition comb_round (p : Program) (s : State) : State :=
    fold_left (run_process p) (filter is_comb p.(processes)) s.

  Fixpoint comb_iter (p : Program) (fuel : nat) (s : State) : State :=
    match fuel with O => s | S n => comb_iter p n (comb_round p s) end.

  Inductive CombLFP (p : Program) (seed : State) : State -> Prop :=
  | CombLFP_intro : forall n fixed,
      fixed = comb_iter p n seed ->
      comb_round p fixed = fixed ->
      CombLFP p seed fixed.

  Record MTrs := {
    mtrs_program : Program;
    mtrs_event_transition : Event -> State -> State
  }.

  Definition program_mtrs (p : Program) : MTrs :=
    {| mtrs_program := p; mtrs_event_transition := ExtendedSemantics p |}.

  Definition lfp_candidate (p : Program) (seed : State) : State :=
    comb_iter p p.(lfp_fuel) seed.

  Fixpoint state_eqb (xs ys : State) : bool :=
    match xs, ys with
    | [], [] => true
    | x :: xs', y :: ys' => andb (Z.eqb x y) (state_eqb xs' ys')
    | _, _ => false
    end.

  Definition lfp_checked (p : Program) (seed : State) : bool :=
    state_eqb (comb_round p (lfp_candidate p seed))
      (lfp_candidate p seed).

  Lemma state_eqb_eq : forall xs ys,
      state_eqb xs ys = true -> xs = ys.
  Proof.
    induction xs as [|x xs IH]; destruct ys as [|y ys]; simpl; intros H;
      try discriminate; auto.
    apply andb_true_iff in H as [Hxy Hrest].
    apply Z.eqb_eq in Hxy. f_equal; auto.
  Qed.

  Theorem checked_lfp_is_lfp : forall p seed,
      lfp_checked p seed = true -> CombLFP p seed (lfp_candidate p seed).
  Proof.
    intros p seed H. eapply CombLFP_intro with (n := lfp_fuel p).
    - reflexivity.
    - apply state_eqb_eq. exact H.
  Qed.

  (** A complete physical phase starts with one externally visible signal
      update.  The combinational cone settles, derived clocks are compared
      with the old stable state, every matching sequential process evaluates
      its RHS against that same settled pre-state, and the combinational cone
      settles again.  This captures gated clocks without hard-coding any CPU
      clock or reset name. *)
  Definition event_spec_matches_states (old new : State)
      (spec : EventSpec) : bool :=
    edge_fires spec.(event_edge)
      (read_signal old spec.(event_signal))
      (read_signal new spec.(event_signal)).

  Definition process_matches_states (old new : State) (proc : Process) : bool :=
    match proc.(process_kind) with
    | Sequential => existsb (event_spec_matches_states old new) proc.(process_events)
    | _ => false
    end.

  Definition selected_on_transition (p : Program) (old new : State) : list Process :=
    filter (process_matches_states old new) p.(processes).

  Definition execute_process_order (p : Program) (pre : State)
      (order : list Process) : State :=
    apply_updates pre (flat_map (process_updates p pre) order).

  Definition phase_driven_state (p : Program) (ev : Event) (pre : State) : State :=
    lfp_candidate p
      (write_signal pre ev.(changed_signal) ev.(new_value)).

  Definition phase_execute_order (p : Program) (ev : Event) (pre : State)
      (order : list Process) : State :=
    let driven := phase_driven_state p ev pre in
    lfp_candidate p (execute_process_order p driven order).

  Definition PhaseSemantics (p : Program) (ev : Event) (pre : State) : State :=
    let driven := phase_driven_state p ev pre in
    phase_execute_order p ev pre (selected_on_transition p pre driven).

  Inductive StandardSVPhaseExecution (p : Program) (ev : Event) (pre : State)
      : State -> Prop :=
  | StandardSVPhaseExecutionOrder : forall order,
      Permutation order
        (selected_on_transition p pre (phase_driven_state p ev pre)) ->
      StandardSVPhaseExecution p ev pre (phase_execute_order p ev pre order).

  Definition PhaseScheduleIndependent (p : Program) : Prop :=
    forall ev pre order,
      Permutation order
        (selected_on_transition p pre (phase_driven_state p ev pre)) ->
      phase_execute_order p ev pre order = PhaseSemantics p ev pre.

  Definition NoPhaseScheduleConflict (p : Program) : Prop :=
    forall ev pre,
      let driven := phase_driven_state p ev pre in
      NoDup (map update_signal
        (flat_map (process_updates p driven)
          (selected_on_transition p pre driven))).

  Definition NoPhaseConflictAt (p : Program) (ev : Event) (pre : State) : Prop :=
    let driven := phase_driven_state p ev pre in
    NoDup (map update_signal
      (flat_map (process_updates p driven)
        (selected_on_transition p pre driven))).

  Definition PhaseIndependentAt (p : Program) (ev : Event) (pre : State) : Prop :=
    forall order,
      Permutation order
        (selected_on_transition p pre (phase_driven_state p ev pre)) ->
      phase_execute_order p ev pre order = PhaseSemantics p ev pre.

  Definition AllPhaseUpdatesCommuteAt (p : Program) (ev : Event)
      (pre : State) : Prop :=
    let driven := phase_driven_state p ev pre in
    all_updates_commuteb
      (flat_map (process_updates p driven)
        (selected_on_transition p pre driven)) = true.

  Definition GroupedPhaseUpdatesCommuteAt (p : Program) (ev : Event)
      (pre : State) : Prop :=
    let driven := phase_driven_state p ev pre in
    grouped_updates_commuteb
      (flat_map (process_updates p driven)
        (selected_on_transition p pre driven)) = true.

  Theorem grouped_phase_updates_from_materialized_certificate :
      forall p ev pre certificate,
        let driven := phase_driven_state p ev pre in
        flat_map (process_updates p driven)
          (selected_on_transition p pre driven) = certificate ->
        grouped_updates_commuteb certificate = true ->
        GroupedPhaseUpdatesCommuteAt p ev pre.
  Proof.
    intros p ev pre certificate driven Hmaterialized Hchecked.
    unfold GroupedPhaseUpdatesCommuteAt. fold driven.
    rewrite Hmaterialized. exact Hchecked.
  Qed.

  Theorem grouped_phase_updates_commute_implies_independent : forall p ev pre,
      GroupedPhaseUpdatesCommuteAt p ev pre -> PhaseIndependentAt p ev pre.
  Proof.
    intros p ev pre Hcheck order Horder.
    unfold PhaseSemantics.
    set (driven := phase_driven_state p ev pre) in *.
    unfold phase_execute_order. fold driven. f_equal.
    unfold execute_process_order.
    set (canonical := flat_map (process_updates p driven)
      (selected_on_transition p pre driven)) in *.
    assert (Hupdates : Permutation
      (flat_map (process_updates p driven) order) canonical).
    { apply process_updates_permutation. exact Horder. }
    eapply apply_updates_permutation_commuting; [exact Hupdates|].
    eapply all_updates_commute_permutation.
    - exact (Permutation_sym Hupdates).
    - apply grouped_updates_commuteb_sound. exact Hcheck.
  Qed.

  Theorem all_phase_updates_commute_implies_independent : forall p ev pre,
      AllPhaseUpdatesCommuteAt p ev pre -> PhaseIndependentAt p ev pre.
  Proof.
    intros p ev pre Hcheck order Horder.
    unfold PhaseSemantics.
    set (driven := phase_driven_state p ev pre) in *.
    unfold phase_execute_order. fold driven. f_equal.
    unfold execute_process_order.
    set (canonical := flat_map (process_updates p driven)
      (selected_on_transition p pre driven)) in *.
    assert (Hupdates : Permutation
      (flat_map (process_updates p driven) order) canonical).
    { apply process_updates_permutation. exact Horder. }
    eapply apply_updates_permutation_commuting; [exact Hupdates|].
    eapply all_updates_commute_permutation.
    - exact (Permutation_sym Hupdates).
    - apply all_updates_commuteb_sound. exact Hcheck.
  Qed.

  Theorem no_phase_conflict_at_implies_independent : forall p ev pre,
      NoPhaseConflictAt p ev pre -> PhaseIndependentAt p ev pre.
  Proof.
    intros p ev pre Hconf order Horder.
    unfold PhaseSemantics.
    set (driven := phase_driven_state p ev pre) in *.
    unfold phase_execute_order. fold driven. f_equal.
    unfold execute_process_order.
    eapply apply_updates_permutation.
    - apply process_updates_permutation. exact Horder.
    - apply (Permutation_NoDup
        (Permutation_map update_signal
          (Permutation_sym (process_updates_permutation p driven order
            (selected_on_transition p pre driven) Horder)))).
      exact Hconf.
  Qed.

  Theorem no_phase_conflict_implies_independent : forall p,
      NoPhaseScheduleConflict p -> PhaseScheduleIndependent p.
  Proof.
    intros p Hconf ev pre order Horder.
    unfold PhaseSemantics.
    set (driven := phase_driven_state p ev pre) in *.
    unfold phase_execute_order.
    fold driven.
    f_equal.
    unfold execute_process_order.
    eapply apply_updates_permutation.
    - apply process_updates_permutation. exact Horder.
    - apply (Permutation_NoDup
        (Permutation_map update_signal
          (Permutation_sym (process_updates_permutation p driven order
            (selected_on_transition p pre driven) Horder)))).
      apply Hconf.
  Qed.

  Theorem extended_phase_to_standard : forall p ev pre,
      StandardSVPhaseExecution p ev pre (PhaseSemantics p ev pre).
  Proof.
    intros. constructor. apply Permutation_refl.
  Qed.

  Theorem standard_phase_to_extended : forall p,
      PhaseScheduleIndependent p ->
      forall ev pre post,
        StandardSVPhaseExecution p ev pre post ->
        post = PhaseSemantics p ev pre.
  Proof.
    intros p Hind ev pre post Hstd. inversion Hstd; subst. eauto.
  Qed.

  Theorem extended_standard_phase_equiv : forall p,
      PhaseScheduleIndependent p ->
      forall ev pre post,
        post = PhaseSemantics p ev pre <->
        StandardSVPhaseExecution p ev pre post.
  Proof.
    intros p Hind ev pre post. split.
    - intros ->. apply extended_phase_to_standard.
    - intros H. eapply standard_phase_to_extended; eauto.
  Qed.

  Theorem extended_standard_phase_confluence : forall p,
      PhaseScheduleIndependent p ->
      forall ev pre post1 post2,
        StandardSVPhaseExecution p ev pre post1 ->
        StandardSVPhaseExecution p ev pre post2 ->
        post1 = post2.
  Proof.
    intros p Hind ev pre post1 post2 H1 H2.
    pose proof (standard_phase_to_extended p Hind ev pre post1 H1) as E1.
    pose proof (standard_phase_to_extended p Hind ev pre post2 H2) as E2.
    congruence.
  Qed.

  Theorem extended_standard_phase_equiv_at : forall p ev pre,
      PhaseIndependentAt p ev pre ->
      forall post,
        post = PhaseSemantics p ev pre <->
        StandardSVPhaseExecution p ev pre post.
  Proof.
    intros p ev pre Hind post. split.
    - intros ->. apply extended_phase_to_standard.
    - intros Hstd. inversion Hstd; subst. apply Hind. assumption.
  Qed.

  Theorem extended_standard_phase_confluence_at : forall p ev pre,
      PhaseIndependentAt p ev pre ->
      forall post1 post2,
        StandardSVPhaseExecution p ev pre post1 ->
        StandardSVPhaseExecution p ev pre post2 ->
        post1 = post2.
  Proof.
    intros p ev pre Hind post1 post2 H1 H2.
    apply (proj2 (extended_standard_phase_equiv_at p ev pre Hind post1)) in H1.
    apply (proj2 (extended_standard_phase_equiv_at p ev pre Hind post2)) in H2.
    congruence.
  Qed.

  (** Explicit state alignment, corresponding to the [stateOf]/[TrsF]
      bridge in the original Chapter-4 development.  The normalized runtime
      has no hidden scheduler state, so alignment is equality of the signal
      vector; the standard side still retains nondeterministic process order
      through [StandardSVPhaseExecution]. *)
  Record StandardState := {
    standard_signal_values : State
  }.

  Definition stateOf (standard : StandardState) : State :=
    standard.(standard_signal_values).

  Definition TrsF (p : Program) (ev : Event)
      (before after : StandardState) : Prop :=
    StandardSVPhaseExecution p ev (stateOf before) (stateOf after).

  Definition StateAligned (standard : StandardState) (extended : State) : Prop :=
    stateOf standard = extended.

  Theorem phase_to_trsF_aligned : forall p ev standard pre,
      StateAligned standard pre ->
      exists standard_post,
        TrsF p ev standard standard_post /\
        StateAligned standard_post (PhaseSemantics p ev pre).
  Proof.
    intros p ev [standard] pre Halign. unfold StateAligned, stateOf in Halign.
    simpl in Halign. subst pre.
    exists {| standard_signal_values := PhaseSemantics p ev standard |}.
    split; [apply extended_phase_to_standard|reflexivity].
  Qed.

  Theorem trsF_to_phase_aligned : forall p,
      PhaseScheduleIndependent p ->
      forall ev standard_pre extended_pre standard_post,
        StateAligned standard_pre extended_pre ->
        TrsF p ev standard_pre standard_post ->
        StateAligned standard_post (PhaseSemantics p ev extended_pre).
  Proof.
    intros p Hind ev [standard_pre] extended_pre [standard_post] Halign Htrs.
    unfold StateAligned, stateOf, TrsF in *; simpl in *; subst extended_pre.
    eapply standard_phase_to_extended; eauto.
  Qed.

  (** The externally visible MTrs uses the complete phase scheduler, not the
      direct-event helper above. *)
  Definition phase_program_mtrs (p : Program) : MTrs :=
    {| mtrs_program := p; mtrs_event_transition := PhaseSemantics p |}.

End ExtendedSV.
