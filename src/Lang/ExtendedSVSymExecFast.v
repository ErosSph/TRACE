(** Fast fact store for the overlay executor (template route, additive; 2026-11-03).
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.
    The list-based chain scans ALL facts at every step (filter + fact_find, each comparison on unary nat signal ids). Here the derived
    constants live in a store [FS]: EVar facts in a positive-keyed map (root -> (width,value) list) plus a short list of expression
    facts.  A step builds the LOCAL fact list of the process (facts of the roots the process reads/writes, filtered by [tail_okb]) and
    runs the already proved [oxexec] / [ox_new_facts] / [oback_wire] on it; soundness is the old soundness plus "store facts hold =>
    local facts hold".  Missing a root only loses precision, never soundness. *)
From Coq Require Import ZArith List Bool Lia PArith FMapPositive.
Require Import Lang.ExtendedSV Lang.ExtendedSVSymExec Lang.ExtendedSVFactChain Lang.ExtendedSVSymExecSym Lang.ExtendedSVSymExecOverlay
 Lang.ExtendedSVBackOverlay Lang.ExtendedSVExprAgreement Lang.ExtendedSVEval3 Lang.ExtendedSVBackward Lang.ExtendedSVExpressionFold.
Import ListNotations ExtendedSV ExtendedSVSymExec ExtendedSVFactChain ExtendedSVSymExecSym ExtendedSVSymExecOverlay ExtendedSVBackOverlay ExtendedSVExprAgreement ExtendedSVEval3 ExtendedSVBackward ExtendedSVExpressionFold.
Local Open Scope Z_scope.
Module ExtendedSVSymExecFast.
Module PM := PositiveMap.

Definition pkey (r:nat) : positive := Pos.of_succ_nat r.
Definition mget {A:Type} (m:PM.t (list A)) (r:nat) : list A := match PM.find (pkey r) m with Some l => l | None => [] end.
Definition madd {A:Type} (m:PM.t (list A)) (r:nat) (x:A) : PM.t (list A) := PM.add (pkey r) (x :: mget m r) m.
Lemma mget_madd {A:Type} (m:PM.t (list A)) r x r' : mget (madd m r x) r' = if Nat.eqb r r' then x :: mget m r else mget m r'.
Proof.
  unfold mget, madd. destruct (Nat.eqb r r') eqn:E.
  - apply Nat.eqb_eq in E. subst r'. rewrite PM.gss. reflexivity.
  - apply Nat.eqb_neq in E. rewrite PM.gso. reflexivity.
    intro H. apply E. exact (SuccNat2Pos.inj _ _ (eq_sym H)).
Qed.

(** EVar facts keyed by root, composite expression facts keyed by their first input root, input-less ones in [fx] *)
Record FS := mkFS { fe : PM.t (list (nat * Z)); fc : PM.t Facts; fx : Facts; fn : nat }.
Definition fs_empty : FS := mkFS (PM.empty _) (PM.empty _) [] 0%nat.
Definition fe_get (fs:FS) (r:nat) : list (nat*Z) := mget (fe fs) r.
Definition fc_get (fs:FS) (r:nat) : Facts := mget (fc fs) r.
Definition has_comp (l:Facts) (e:Expr) (z:Z) : bool :=
  existsb (fun ez => if expr_eq_dec e (fst ez) then Z.eqb z (snd ez) else false) l.
Definition add_comp (fs:FS) (e:Expr) (z:Z) : FS :=
  match expr_inputs e with
  | (_, r) :: _ => if has_comp (fc_get fs r) e z then fs else mkFS (fe fs) (madd (fc fs) r (e,z)) (fx fs) (S (fn fs))
  | [] => if has_comp (fx fs) e z then fs else mkFS (fe fs) (fc fs) ((e,z) :: fx fs) (S (fn fs))
  end.
Definition has_ev (l:list (nat*Z)) (w:nat) (z:Z) : bool := existsb (fun wz => Nat.eqb (fst wz) w && Z.eqb (snd wz) z) l.
Definition add_fact (fs:FS) (ez:Expr*Z) : FS :=
  match fst ez with
  | EVar w r => if has_ev (fe_get fs r) w (snd ez) then fs else mkFS (madd (fe fs) r (w, snd ez)) (fc fs) (fx fs) (S (fn fs))
  | e => add_comp fs e (snd ez)
  end.
Definition add_facts (fs:FS) (L:Facts) : FS := fold_left add_fact L fs.

Definition SHold (s:State) (fs:FS) : Prop :=
  (forall r w z, In (w,z) (fe_get fs r) -> norm w (read_signal s r) = z) /\
  (forall r, FactsHold s (fc_get fs r)) /\ FactsHold s (fx fs).

Definition SHold_def := SHold.
Lemma add_comp_hold s fs e z : SHold s fs -> eval_expr s e = z -> SHold s (add_comp fs e z).
Proof.
  intros HS H. pose proof HS as [H1 [H3 H2]]. unfold add_comp. destruct (expr_inputs e) as [|[wi ri] rest].
  - destruct (has_comp (fx fs) e z); [exact HS|]. cbn. split; [exact H1|split; [exact H3|]]. intros e0 z0 HI. destruct HI as [HI|HI]; [injection HI as <- <-; exact H | exact (H2 _ _ HI)].
  - destruct (has_comp (fc_get fs ri) e z); [exact HS|]. cbn [fe fc fx]. split; [exact H1|split; [|exact H2]]. intro r'. unfold fc_get. cbn [fc]. rewrite mget_madd. destruct (Nat.eqb ri r') eqn:E.
    + intros e0 z0 HI. destruct HI as [HI|HI]; [injection HI as <- <-; exact H | exact (H3 ri e0 z0 HI)].
    + exact (H3 r').
Qed.
Lemma add_fact_hold s fs ez : SHold s fs -> eval_expr s (fst ez) = snd ez -> SHold s (add_fact fs ez).
Proof.
  intros HS H. destruct ez as [e z]. cbn [fst snd] in H. unfold add_fact. cbn [fst snd].
  destruct e as [w0 v0|w r|w0 a b|w0 a b|w0 c a|w0 sg a|w0 o a|w0 o a b|w0 g a b]; try exact (add_comp_hold s fs _ z HS H).
  destruct (has_ev (fe_get fs r) w z); [exact HS|]. destruct HS as [H1 [H3 H2]]. cbn [fe fc fx]. split; [|split; [exact H3|exact H2]].
  intros r' w' z' HI. unfold fe_get in HI. cbn [fe] in HI. rewrite mget_madd in HI. destruct (Nat.eqb r r') eqn:E.
  - apply Nat.eqb_eq in E. subst r'. destruct HI as [HI|HI]; [injection HI as <- <-; exact H | exact (H1 _ _ _ HI)].
  - exact (H1 _ _ _ HI).
Qed.

Lemma add_facts_hold s L : forall fs, SHold s fs -> FactsHold s L -> SHold s (add_facts fs L).
Proof.
  induction L as [|ez t IH]; intros fs HS HF; cbn [add_facts fold_left]; [exact HS|].
  apply IH; [|intros e z HI; apply HF; right; exact HI].
  apply add_fact_hold; [exact HS|]. exact (HF (fst ez) (snd ez) (or_introl (surjective_pairing ez))).
Qed.

Lemma shold_init s F : FactsHold s F -> SHold s (add_facts fs_empty F).
Proof.
  intro HF. apply add_facts_hold; [|exact HF]. split; [|split].
  - intros r w z HI. unfold fe_get, mget in HI. cbn [fe fs_empty] in HI. rewrite PM.gempty in HI. contradiction.
  - intros r e z HI. unfold fc_get, mget in HI. cbn [fc fs_empty] in HI. rewrite PM.gempty in HI. contradiction.
  - intros e z HI. cbn in HI. contradiction.
Qed.

(** local facts: store facts of the given roots plus the input-less ones, filtered like the chain does *)
Definition roots_facts (fs:FS) (rs:list nat) : Facts :=
  flat_map (fun r => map (fun wz => (EVar (fst wz) r, snd wz)) (fe_get fs r) ++ fc_get fs r) rs.
Definition loc_facts (T:list (list nat)) (fs:FS) (k:nat) (rs:list nat) : Facts :=
  filter (tail_okb T k) (roots_facts fs rs ++ fx fs).
Definition plain_facts (fs:FS) (rs:list nat) : Facts := roots_facts fs rs ++ fx fs.

Lemma plain_hold s fs rs : SHold s fs -> FactsHold s (plain_facts fs rs).
Proof.
  intros [H1 [H3 H2]] e z HI. unfold plain_facts in HI. apply in_app_or in HI as [HI|HI]; [|exact (H2 _ _ HI)].
  unfold roots_facts in HI. apply in_flat_map in HI as [r [_ HI]]. apply in_app_or in HI as [HI|HI].
  - apply in_map_iff in HI as [[w z0] [E HI]]. cbn [fst snd] in E. injection E as <- <-. cbn [eval_expr]. exact (H1 _ _ _ HI).
  - exact (H3 r _ _ HI).
Qed.
Lemma loc_hold s T fs k rs : SHold s fs -> FactsHold s (loc_facts T fs k rs).
Proof. intros H e z HI. unfold loc_facts in HI. apply filter_In in HI as [HI _]. exact (plain_hold s fs rs H e z HI). Qed.
Lemma loc_okb T fs k rs : facts_inputs_okb (loc_facts T fs k rs) T k = true.
Proof.
  unfold facts_inputs_okb. apply forallb_forall. intros ez HI. unfold loc_facts in HI. apply filter_In in HI as [_ HT'].
  exact HT'.
Qed.

(** roots read or written by a statement (only completeness depends on it) *)
Fixpoint lv_roots (l:LValue) : list nat :=
  match l with LVar _ x => [x] | LSel _ b off => lv_roots b ++ map snd (expr_inputs off) end.
Fixpoint stmt_roots (s:Stmt) : list nat :=
  match s with
  | SSkip => []
  | SAssign _ rhs lhs => map snd (expr_inputs rhs) ++ lv_roots lhs
  | SSeq l => (fix go (l:list Stmt) : list nat := match l with [] => [] | x::t => stmt_roots x ++ go t end) l
  | SIf g y n => map snd (expr_inputs g) ++ stmt_roots y ++ stmt_roots n
  | SCase scr arms => map snd (expr_inputs scr) ++
      (fix goa (a:list (option Expr * Stmt)) : list nat := match a with
        | [] => []
        | (ko,b)::t => (match ko with Some k => map snd (expr_inputs k) | None => [] end) ++ stmt_roots b ++ goa t end) arms
  end.

Definition proc_roots (proc:Process) : list nat := stmt_roots (nbfix (process_body proc)) ++ process_writers proc.

Definition fstep (ps:list Process) (T:list (list nat)) (fuel:nat) (fs:FS) (k:nat) : FS :=
  match nth_error ps k with
  | None => fs
  | Some proc =>
    let F0 := loc_facts T fs k (proc_roots proc) in
    match oxexec F0 fuel (nbfix (process_body proc)) [] with
    | None => fs
    | Some ov => add_facts fs (ox_new_facts F0 T k ov)
    end
  end.

Lemma fstep_sound p ps T fs k seed fixed :
  filter is_comb (processes p) = ps -> TabC ps T -> CombLFP p seed fixed -> SHold fixed fs ->
  SHold fixed (fstep ps T (statement_fuel p) fs k).
Proof.
  intros HP HT HL HS. unfold fstep. destruct (nth_error ps k) as [proc|] eqn:HN; [|exact HS].
  destruct (oxexec (loc_facts T fs k (proc_roots proc)) (statement_fuel p) (nbfix (process_body proc)) []) as [ov|] eqn:Hx; [|exact HS].
  apply add_facts_hold; [exact HS|].
  exact (ox_new_facts_sound p ps T k proc _ ov seed fixed HP HT HN (loc_okb T fs k _) (loc_hold fixed T fs k _ HS) HL Hx).
Qed.

(** checking a case against the store *)
Definition fs_find (fs:FS) (w r:nat) : option Z :=
  (fix go (l:list (nat*Z)) : option Z := match l with [] => None | (w',z)::t => if Nat.eqb w w' then Some z else go t end) (fe_get fs r).
Lemma find_in (fs:FS) w r z : fs_find fs w r = Some z -> In (w,z) (fe_get fs r).
Proof.
  unfold fs_find. induction (fe_get fs r) as [|[w' z'] rest IH]; intro Hh; cbn in Hh; [discriminate|].
  destruct (Nat.eqb w w') eqn:E; [injection Hh as <-; apply Nat.eqb_eq in E; subst; left; reflexivity | right; exact (IH Hh)].
Qed.
(** backward step: ONE oxexec of the process, then the decomposition for every written root with a known value *)
Definition back_one (T:list (list nat)) (k:nat) (fs:FS) (ov:SOv) (r:signal) : Facts :=
  match fs_find fs 1%nat r with
  | None => []
  | Some v =>
    match (if wr_lt T r (S k) then sov_lookup ov r else None) with
    | Some (1%nat, e) => if Nat.eqb (expr_width e) 1 && inputs_okb T k e then decomp v e else []
    | _ => []
    end
  end.

Lemma back_one_sound p ps T k proc F0u fs ov seed fixed r :
  filter is_comb (processes p) = ps -> TabC ps T -> nth_error ps k = Some proc -> CombLFP p seed fixed -> FactsHold fixed F0u -> SHold fixed fs ->
  oxexec (filter (tail_okb T k) F0u) (statement_fuel p) (nbfix (process_body proc)) [] = Some ov ->
  FactsHold fixed (back_one T k fs ov r).
Proof.
  intros HP HT HN HL HF HS Hx. unfold back_one.
  destruct (fs_find fs 1%nat r) as [v|] eqn:Hf; [|intros e z HI; destruct HI].
  destruct (wr_lt T r (S k)) eqn:Hr; [|intros e z HI; destruct HI].
  destruct (sov_lookup ov r) as [[w e]|] eqn:Hl; [|intros e0 z HI; destruct HI].
  destruct w as [|[|w]]; try (intros e0 z HI; destruct HI).
  destruct (Nat.eqb (expr_width e) 1 && inputs_okb T k e) eqn:C; [|intros e0 z HI; destruct HI].
  apply andb_true_iff in C as [W Hi]. apply Nat.eqb_eq in W.
  assert (Hv : eval_expr fixed (EVar 1%nat r) = v).
  { cbn [eval_expr]. destruct HS as [H1 _]. exact (H1 _ _ _ (find_in fs 1%nat r v Hf)). }
  pose proof (ox_sym_wire p ps T k proc F0u ov seed fixed r 1%nat e HP HT HN HL HF Hx Hl Hr Hi) as Hw.
  pose proof (eval_normalized fixed e) as En. rewrite W in En. rewrite En in Hw.
  apply (decomp_sound fixed e v). rewrite <- Hw. cbn [eval_expr] in Hv. exact Hv.
Qed.

Definition fback (ps:list Process) (T:list (list nat)) (fuel:nat) (fs:FS) (k:nat) : FS :=
  match nth_error ps k with
  | None => fs
  | Some proc =>
    let F0 := loc_facts T fs k (proc_roots proc) in
    match oxexec F0 fuel (nbfix (process_body proc)) [] with
    | None => fs
    | Some ov => add_facts fs (flat_map (back_one T k fs ov) (process_writers proc))
    end
  end.

Lemma fback_sound p ps T fs k seed fixed :
  filter is_comb (processes p) = ps -> TabC ps T -> CombLFP p seed fixed -> SHold fixed fs ->
  SHold fixed (fback ps T (statement_fuel p) fs k).
Proof.
  intros HP HT HL HS. unfold fback. destruct (nth_error ps k) as [proc|] eqn:HN; [|exact HS].
  destruct (oxexec (loc_facts T fs k (proc_roots proc)) (statement_fuel p) (nbfix (process_body proc)) []) as [ov|] eqn:Hx; [|exact HS].
  apply add_facts_hold; [exact HS|].
  intros e z HI. apply in_flat_map in HI as [r [_ HI]].
  exact (back_one_sound p ps T k proc (plain_facts fs (proc_roots proc)) fs ov seed fixed r HP HT HN HL (plain_hold fixed fs _ HS) HS Hx e z HI).
Qed.

Definition frun (ps:list Process) (T:list (list nat)) (fuel:nat) (fs:FS) (sc:Script) : FS :=
  fold_left (fun (fs:FS) (st:bool*nat) => if fst st then fback ps T fuel fs (snd st) else fstep ps T fuel fs (snd st)) sc fs.

Lemma frun_sound p ps T seed fixed :
  filter is_comb (processes p) = ps -> TabC ps T -> CombLFP p seed fixed ->
  forall sc fs, SHold fixed fs -> SHold fixed (frun ps T (statement_fuel p) fs sc).
Proof.
  intros HP HT HL. induction sc as [|[b k] t IH]; intros fs HS; cbn [frun fold_left]; [exact HS|].
  apply IH. destruct b; cbn [fst snd].
  - exact (fback_sound p ps T fs k seed fixed HP HT HL HS).
  - exact (fstep_sound p ps T fs k seed fixed HP HT HL HS).
Qed.

Definition outs_ok (fs:FS) (outs:list ((signal*nat)*Z)) : bool :=
  forallb (fun t => match fs_find fs (snd (fst t)) (fst (fst t)) with Some z => Z.eqb z (snd t) | None => false end) outs.
Lemma outs_ok_sound s fs outs : SHold s fs -> outs_ok fs outs = true -> DecOut s outs.
Proof.
  intros [H1 _] H t Ht. unfold outs_ok in H. rewrite forallb_forall in H. specialize (H t Ht). cbv beta in H.
  destruct t as [[r w] z]. cbn [fst snd] in *.
  destruct (fs_find fs w r) as [z0|] eqn:Hf; [|discriminate]. apply Z.eqb_eq in H. subst z0.
  exact (H1 _ _ _ (find_in fs w r z Hf)).
Qed.

Definition exprs_ok (fs:FS) (L:Facts) : bool :=
  forallb (fun ez => expr_fact_ok3 (plain_facts fs (map snd (expr_inputs (fst ez)))) ez) L.
Lemma exprs_ok_sound s fs L : SHold s fs -> exprs_ok fs L = true -> FactsHold s L.
Proof.
  intros HS H e z HI. unfold exprs_ok in H. rewrite forallb_forall in H. specialize (H _ HI).
  exact (exprs_hold3 _ s [(e,z)] (plain_hold s fs _ HS) (eq_trans (andb_true_r _) H) e z (or_introl eq_refl)).
Qed.

(** scripted cases over the fast store: one checker, one soundness theorem *)
Record CaseF := mkCaseF {
  cf_facts : Facts;
  cf_script : Script;
  cf_outs : list ((signal*nat)*Z);
  cf_exprs : Facts }.
Definition cf_store ps T fuel (c:CaseF) : FS := frun ps T fuel (add_facts fs_empty (cf_facts c)) (cf_script c).
Definition check_casef ps T fuel (c:CaseF) : bool :=
  let fs := cf_store ps T fuel c in outs_ok fs (cf_outs c) && exprs_ok fs (cf_exprs c).
Definition check_casesf ps T fuel (cs:list CaseF) : bool := forallb (check_casef ps T fuel) cs.

Theorem casesf_sound p ps T cases seed fixed c :
  filter is_comb (processes p) = ps -> tab_okb ps T = true -> CombLFP p seed fixed ->
  check_casesf ps T (statement_fuel p) cases = true -> In c cases -> FactsHold fixed (cf_facts c) ->
  SHold fixed (cf_store ps T (statement_fuel p) c) /\ DecOut fixed (cf_outs c) /\ FactsHold fixed (cf_exprs c).
Proof.
  intros HP HT HL Hc Hin HF. unfold check_casesf in Hc. rewrite forallb_forall in Hc. specialize (Hc c Hin).
  unfold check_casef in Hc. apply andb_true_iff in Hc as [H1 H2].
  pose proof (frun_sound p ps T seed fixed HP (tab_okb_sound ps T HT) HL (cf_script c) _ (shold_init fixed _ HF)) as HS.
  fold (cf_store ps T (statement_fuel p) c) in HS, H1, H2.
  exact (conj HS (conj (outs_ok_sound fixed _ _ HS H1) (exprs_ok_sound fixed _ _ HS H2))).
Qed.

(** cases with a SHARED class-independent prefix: the prefix store is computed once and every case continues from it *)
Record Shared := mkShared { sh_facts : Facts; sh_script : Script }.
Definition sh_store ps T fuel (sh:Shared) : FS := frun ps T fuel (add_facts fs_empty (sh_facts sh)) (sh_script sh).
Definition cs_store ps T fuel (s0:FS) (c:CaseF) : FS := frun ps T fuel (add_facts s0 (cf_facts c)) (cf_script c).
Definition check_shared ps T fuel (sh:Shared) (cs:list CaseF) : bool :=
  let s0 := sh_store ps T fuel sh in
  forallb (fun c => let fs := cs_store ps T fuel s0 c in outs_ok fs (cf_outs c) && exprs_ok fs (cf_exprs c)) cs.

Theorem shared_sound p ps T sh cases seed fixed c :
  filter is_comb (processes p) = ps -> tab_okb ps T = true -> CombLFP p seed fixed ->
  check_shared ps T (statement_fuel p) sh cases = true -> In c cases -> FactsHold fixed (sh_facts sh) -> FactsHold fixed (cf_facts c) ->
  SHold fixed (cs_store ps T (statement_fuel p) (sh_store ps T (statement_fuel p) sh) c) /\ DecOut fixed (cf_outs c) /\ FactsHold fixed (cf_exprs c).
Proof.
  intros HP HT HL Hc Hin Hsh HF. unfold check_shared in Hc. fold (sh_store ps T (statement_fuel p) sh) in Hc.
  rewrite forallb_forall in Hc. specialize (Hc c Hin). apply andb_true_iff in Hc as [H1 H2].
  pose proof (frun_sound p ps T seed fixed HP (tab_okb_sound ps T HT) HL (sh_script sh) _ (shold_init fixed _ Hsh)) as H0.
  fold (sh_store ps T (statement_fuel p) sh) in H0.
  pose proof (frun_sound p ps T seed fixed HP (tab_okb_sound ps T HT) HL (cf_script c) _ (add_facts_hold fixed _ _ H0 HF)) as HS.
  fold (cs_store ps T (statement_fuel p) (sh_store ps T (statement_fuel p) sh) c) in HS, H1, H2.
  exact (conj HS (conj (outs_ok_sound fixed _ _ HS H1) (exprs_ok_sound fixed _ _ HS H2))).
Qed.
End ExtendedSVSymExecFast.
Print Assumptions ExtendedSVSymExecFast.frun_sound.
Print Assumptions ExtendedSVSymExecFast.casesf_sound.
Print Assumptions ExtendedSVSymExecFast.shared_sound.
