(** Sideband instruction origins follow actual selected full-word copies.
    None means UNKNOWN, not an invalid or empty pipeline slot. The label may
    contain an admission ID and source PC; this file never guesses either.
    Architectural admission and commit correspondence remain separate goals. *)
From Coq Require Import List ZArith Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVScalarHistory.
Import ExtendedSV ExtendedSVWordInvariant ExtendedSVScalarHistory.
Module ExtendedSVInstructionOrigin.

Fixpoint copy_source (s : State) (e : Expr) : option signal :=
 match e with
 | EVar w root => if Nat.eqb w 32 then Some root else None
 | ECond w guard yes no =>
   if Nat.eqb w 32 then
     if Z.eqb (eval_expr s guard) 0 then copy_source s no else copy_source s yes
   else None
 | _ => None
 end.

Theorem copy_source_sound e : forall s root,
 copy_source s e = Some root ->
 eval_expr s e = norm 32 (read_signal s root).
Proof.
 induction e; intros s root H; cbn [copy_source] in H; try discriminate.
 - destruct (Nat.eqb width 32) eqn:HW; [|discriminate].
   apply Nat.eqb_eq in HW. subst width. inversion H; reflexivity.
 - destruct (Nat.eqb width 32) eqn:HW; [|discriminate].
   apply Nat.eqb_eq in HW. subst width. cbn [eval_expr].
   destruct (Z.eqb (eval_expr s e1) 0).
   + rewrite (IHe3 s root H). apply norm_idempotent.
   + rewrite (IHe2 s root H). apply norm_idempotent.
Qed.

Section Origins.
Context {Label : Type}.
Variable instruction_word : Label -> Z.
Definition OriginMap := signal -> option Label.
Definition OriginsAgree (s : State) (origins : OriginMap) : Prop :=
 forall root label, origins root = Some label ->
 norm 32 (read_signal s root) = norm 32 (instruction_word label).

Definition copy_origin s (origins : OriginMap) e :=
 match copy_source s e with Some source => origins source | None => None end.

Theorem copy_origin_sound e s origins label :
 OriginsAgree s origins -> copy_origin s origins e = Some label ->
 eval_expr s e = norm 32 (instruction_word label).
Proof.
 intros HA HC. unfold copy_origin in HC.
 destruct (copy_source s e) as [source|] eqn:HS; [|discriminate].
 rewrite (copy_source_sound e s source HS). now apply HA.
Qed.

Definition origin_write (origins : OriginMap) root label : OriginMap :=
 fun r => if Nat.eqb r root then label else origins r.

Theorem single_capture_preserves_relation e pre post origins root :
 OriginsAgree pre origins ->
 norm 32 (read_signal post root) = norm 32 (eval_expr pre e) ->
 (forall other, other <> root ->
   norm 32 (read_signal post other) = norm 32 (read_signal pre other)) ->
 OriginsAgree post (origin_write origins root (copy_origin pre origins e)).
Proof.
 intros HA HU HF other label Htag. unfold origin_write in Htag.
 destruct (Nat.eqb other root) eqn:HE.
 - apply Nat.eqb_eq in HE. subst other. rewrite HU.
   rewrite (copy_origin_sound e pre origins label HA Htag). apply norm_idempotent.
 - apply Nat.eqb_neq in HE. rewrite HF by exact HE. now apply HA.
Qed.

Definition phase_origin p proc e ev pre old (sampled : OriginMap) :=
 if process_matches_states pre (phase_driven_state p ev pre) proc
 then copy_origin (phase_driven_state p ev pre) sampled e
 else old.

Theorem actual_phase_origin p root proc e
 (certificate : ScalarCertificate p root 32 proc e) ev pre old sampled label :
 changed_signal ev <> root ->
 (forall l, old = Some l ->
   norm 32 (read_signal pre root) = norm 32 (instruction_word l)) ->
 OriginsAgree (phase_driven_state p ev pre) sampled ->
 phase_origin p proc e ev pre old sampled = Some label ->
 norm 32 (read_signal (PhaseSemantics p ev pre) root) =
 norm 32 (instruction_word label).
Proof.
 intros HE Hold Hsample Horigin.
 rewrite (history_phase_projection _ _ _ _ _ certificate ev pre HE).
 unfold phase_origin in Horigin.
 destruct (process_matches_states pre (phase_driven_state p ev pre) proc).
 - rewrite (copy_origin_sound e (phase_driven_state p ev pre) sampled label Hsample Horigin).
   apply norm_idempotent.
 - now apply Hold.
Qed.

Theorem unknown_is_not_a_vacancy (valid : signal -> bool) (origins : OriginMap) root :
 origins root = None ->
 (forall r, valid r = true -> exists label, origins r = Some label) ->
 valid root = false.
Proof.
 intros Hunknown Hcoverage. destruct (valid root) eqn:HV; [|reflexivity].
 destruct (Hcoverage root HV) as [label HL]. congruence.
Qed.
End Origins.
Print Assumptions copy_source_sound.
Print Assumptions copy_origin_sound.
Print Assumptions single_capture_preserves_relation.
Print Assumptions actual_phase_origin.
Print Assumptions unknown_is_not_a_vacancy.
End ExtendedSVInstructionOrigin.
