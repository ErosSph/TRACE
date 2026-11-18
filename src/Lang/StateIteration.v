(** Narrow LLM-authored extraction: OpenAI Codex, from the accepted
    TinyInputPhase.fold_events_preserves proof. Keep induction abstract so
    concrete circuit definitions do not expand during proof checking. *)
From Coq Require Import List PeanoNat.
Module StateIteration.
Lemma fold_events_preserves {A B : Type} (step : B -> A -> B)
 (Good : B -> Prop) (Allowed : A -> Prop)
 (preserves : forall ev s, Allowed ev -> Good s -> Good (step s ev))
 events s :
 Forall Allowed events -> Good s -> Good (fold_left step events s).
Proof.
 intro H. induction H in s |- *; cbn; [auto|].
 intro HS. apply IHForall. now apply preserves.
Qed.
Lemma iterate_preserves {A : Type} (step : A -> A) (Good : A -> Prop)
 (preserves : forall s, Good s -> Good (step s)) n s :
 Good s -> Good (Nat.iter n step s).
Proof. induction n; cbn; auto. Qed.
End StateIteration.
