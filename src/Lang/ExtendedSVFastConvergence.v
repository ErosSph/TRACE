(** proof_author='LLM-generated: Claude Code (claude-sonnet-5-5)', external_llm_api_calls=0.
    Additive fast evaluation of catalog_convergesb. Wires are encoded as pairs of
    binary naturals (injective), so membership tests no longer pay unary Nat.eqb.
    The exported implication leaves every existing statement unchanged. *)
From Coq Require Import List Bool PeanoNat NArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVKnownInputs Lang.ExtendedSVDependencyPropagation
 Lang.ExtendedSVDependencyCatalog Lang.ExtendedSVRootProjection Lang.ExtendedSVBoundedCatalogPhase.
Import ExtendedSVRootProjection.
Import ListNotations ExtendedSV ExtendedSVKnownInputs ExtendedSVDependencyPropagation ExtendedSVDependencyCatalog.
Module ExtendedSVFastConvergence.
Definition encW (wr:Wire) : N*N := (N.of_nat (fst wr),N.of_nat (snd wr)).
Definition eqbN (a b:N*N) := N.eqb (fst a)(fst b) && N.eqb (snd a)(snd b).
Definition containsbN (known requested:list (N*N)) := forallb (fun wr=>existsb (eqbN wr) known) requested.
Definition stepN (writers:list N)(rows:list (list (N*N)*list (N*N)))(known:list (N*N)) :=
 filter (fun wr=>negb (existsb (N.eqb (snd wr)) writers)) known ++
 flat_map (fun row=>if containsbN known (fst row) then snd row else []) rows.
Definition propagateN (cat:list (list N*list (list (N*N)*list (N*N)))) known :=
 fold_left (fun k e=>stepN (fst e)(snd e) k) cat known.
Fixpoint roundsN n cat known := match n with O=>known | S k=>roundsN k cat (propagateN cat known) end.
Definition encRow (row:DependencyRow) := (map encW (dependency_inputs row), map encW (dependency_outputs row)).
Definition encCat (catalog:Catalog) := map (fun e=>(map N.of_nat (process_writers (fst e)), map encRow (snd e))) catalog.
Definition fast_convergesb fuel catalog init :=
 containsbN (roundsN fuel (encCat catalog) (map encW init)) (map encW (catalog_outputs catalog)).

Lemma nat_N_eqb a b : N.eqb (N.of_nat a)(N.of_nat b) = Nat.eqb a b.
Proof.
 destruct (Nat.eqb a b) eqn:E.
 - apply Nat.eqb_eq in E. subst. apply N.eqb_refl.
 - apply Nat.eqb_neq in E. destruct (N.eqb (N.of_nat a)(N.of_nat b)) eqn:E2;[|reflexivity].
   apply N.eqb_eq in E2. apply Nat2N.inj in E2. contradiction.
Qed.
Lemma eqbN_enc a b : eqbN (encW a)(encW b) = wire_eqb a b.
Proof. unfold eqbN,wire_eqb,encW. cbn. now rewrite !nat_N_eqb. Qed.
Lemma existsb_enc a l : existsb (eqbN (encW a)) (map encW l) = existsb (wire_eqb a) l.
Proof. induction l;cbn;[reflexivity|]. now rewrite eqbN_enc,IHl. Qed.
Lemma contains_enc k r : containsbN (map encW k)(map encW r) = containsb k r.
Proof. unfold containsbN,containsb. induction r;cbn;[reflexivity|]. now rewrite existsb_enc,IHr. Qed.
Lemma writers_enc root ws : existsb (N.eqb (N.of_nat root)) (map N.of_nat ws) = existsb (Nat.eqb root) ws.
Proof. induction ws;cbn;[reflexivity|]. now rewrite nat_N_eqb,IHws. Qed.
Lemma filter_enc ws k : filter (fun wr=>negb (existsb (N.eqb (snd wr)) (map N.of_nat ws))) (map encW k)
 = map encW (filter (fun wr=>negb (existsb (Nat.eqb (snd wr)) ws)) k).
Proof. induction k as [|a k IH];cbn;[reflexivity|]. unfold encW at 1;cbn. rewrite writers_enc. destruct (negb _);cbn;[now rewrite IH|exact IH]. Qed.
Lemma flat_enc known rows : flat_map (fun row=>if containsbN (map encW known) (fst row) then snd row else []) (map encRow rows)
 = map encW (flat_map (fun row=>if containsb known (dependency_inputs row) then dependency_outputs row else []) rows).
Proof.
 induction rows as [|r rows IH];[reflexivity|]. cbn [map flat_map]. unfold encRow at 1. cbn [fst snd]. rewrite contains_enc.
 rewrite map_app,IH. destruct (containsb _ _);cbn [map];reflexivity.
Qed.
Lemma step_enc proc rows known : stepN (map N.of_nat (process_writers proc)) (map encRow rows) (map encW known) = map encW (dependency_step proc rows known).
Proof. unfold stepN,dependency_step. rewrite filter_enc,flat_enc,map_app. reflexivity. Qed.
Lemma prop_enc catalog known : propagateN (encCat catalog)(map encW known) = map encW (propagate catalog known).
Proof.
 unfold propagateN,propagate,encCat. revert known. induction catalog as [|[proc rows] rest IH];intro known;cbn;[reflexivity|].
 rewrite step_enc. apply IH.
Qed.
Lemma rounds_enc n catalog known : roundsN n (encCat catalog)(map encW known) = map encW (propagate_rounds n catalog known).
Proof. revert known. induction n;intro known;cbn;[reflexivity|]. rewrite prop_enc. apply IHn. Qed.
Theorem fast_convergesb_sound p catalog : fast_convergesb (lfp_fuel p) catalog (catalog_initial_known p catalog) = true ->
 catalog_convergesb p catalog = true.
Proof.
 unfold fast_convergesb,catalog_convergesb. rewrite rounds_enc. rewrite contains_enc. exact (fun H=>H).
Qed.
Print Assumptions fast_convergesb_sound.

(** Second stage: the initial known set is built with one precomputed writer list instead of
    rescanning every process body per input. Only set membership matters to the check. *)
Definition SS (a b:list (N*N)) := forall x, In x a <-> In x b.
Lemma existsb_ss f a b : SS a b -> existsb f a = existsb f b.
Proof.
 intro H. apply Bool.eq_iff_eq_true. rewrite !existsb_exists. split;intros [x [H1 H2]];exists x;split;try assumption; apply H; assumption.
Qed.
Lemma contains_ss k1 k2 r : SS k1 k2 -> containsbN k1 r = containsbN k2 r.
Proof. intro H. unfold containsbN. induction r;cbn;[reflexivity|]. rewrite IHr, (existsb_ss _ _ _ H). reflexivity. Qed.
Lemma step_ss ws rows k1 k2 : SS k1 k2 -> SS (stepN ws rows k1)(stepN ws rows k2).
Proof.
 unfold SS in *. intro H. unfold stepN.
 assert (HL: flat_map (fun row=>if containsbN k1 (fst row) then snd row else []) rows = flat_map (fun row=>if containsbN k2 (fst row) then snd row else []) rows).
 { apply flat_map_ext. intros row. rewrite (contains_ss k1 k2 _ H). reflexivity. }
 rewrite HL. intro x. rewrite !in_app_iff, !filter_In. rewrite (H x). tauto.
Qed.
Lemma prop_ss cat k1 k2 : SS k1 k2 -> SS (propagateN cat k1)(propagateN cat k2).
Proof. unfold propagateN. revert k1 k2. induction cat as [|e cat IH];intros k1 k2 H;cbn;[exact H|]. apply IH. apply step_ss. exact H. Qed.
Lemma rounds_ss n cat k1 k2 : SS k1 k2 -> SS (roundsN n cat k1)(roundsN n cat k2).
Proof. revert k1 k2. induction n;intros k1 k2 H;cbn;[exact H|]. apply IHn. apply prop_ss. exact H. Qed.
Definition cwriters p := flat_map process_writers (filter is_comb (processes p)).
Lemma unwritten_eq p root : comb_root_unwrittenb p root = negb (existsb (Nat.eqb root) (cwriters p)).
Proof.
 unfold comb_root_unwrittenb,cwriters. induction (filter is_comb (processes p)) as [|q l IH];cbn;[reflexivity|].
 rewrite IH, existsb_app. now rewrite Bool.negb_orb.
Qed.
Definition fast_init p (catalog:Catalog) :=
 let ws := map N.of_nat (cwriters p) in
 filter (fun wr=>negb (existsb (N.eqb (snd wr)) ws))
  (map encW (flat_map (fun entry=>flat_map dependency_inputs (snd entry)) catalog)).
Lemma init_ss p catalog : SS (map encW (catalog_initial_known p catalog)) (fast_init p catalog).
Proof.
 unfold SS. intro x. unfold catalog_initial_known,fast_init. cbv zeta. rewrite in_map_iff, filter_In, in_map_iff.
 split.
 - intros [wr [<- Hin]]. apply nodup_In in Hin. apply filter_In in Hin as [Hin Hu].
   split;[exists wr;split;[reflexivity|exact Hin]|].
   unfold encW. cbn. rewrite writers_enc. rewrite unwritten_eq in Hu. exact Hu.
 - intros [[wr [<- Hin]] Hu]. exists wr. split;[reflexivity|]. apply nodup_In. apply filter_In. split;[exact Hin|].
   unfold encW in Hu. cbn in Hu. rewrite writers_enc in Hu. rewrite unwritten_eq. exact Hu.
Qed.
Definition fast2_convergesb p catalog :=
 containsbN (roundsN (lfp_fuel p) (encCat catalog) (fast_init p catalog)) (map encW (catalog_outputs catalog)).
Theorem fast2_convergesb_sound p catalog : fast2_convergesb p catalog = true -> catalog_convergesb p catalog = true.
Proof.
 intro H. apply (fast_convergesb_sound p catalog). unfold fast_convergesb. rewrite <- H. unfold fast2_convergesb.
 apply contains_ss. apply rounds_ss. apply init_ss.
Qed.
Print Assumptions fast2_convergesb_sound.

(** Third stage: writer coverage. The library definition recomputes catalog_outputs (a quadratic
    nodup) for every writer root under strict evaluation; here it is computed once, on N roots. *)
Definition covers_fastb p catalog :=
 let outs := map (fun wr=>N.of_nat (snd wr)) (catalog_outputs catalog) in
 forallb (fun root=>existsb (N.eqb (N.of_nat root)) outs) (cwriters p).
Theorem covers_fast_sound p catalog : covers_fastb p catalog = true ->
 ExtendedSVBoundedCatalogPhase.catalog_covers_writersb p catalog = true.
Proof.
 unfold covers_fastb,ExtendedSVBoundedCatalogPhase.catalog_covers_writersb,ExtendedSVBoundedCatalogPhase.catalog_writers,cwriters. cbv zeta.
 intro H. rewrite forallb_forall in H |- *. intros root Hr. specialize (H root Hr).
 apply existsb_exists in H as [x [Hx He]]. apply in_map_iff in Hx as [wr [<- Hwr]].
 apply existsb_exists. exists wr. split;[exact Hwr|]. rewrite nat_N_eqb in He. exact (eq_sym (eq_trans (eq_sym He) (Nat.eqb_sym _ _))) .
Qed.
Print Assumptions covers_fast_sound.
End ExtendedSVFastConvergence.
