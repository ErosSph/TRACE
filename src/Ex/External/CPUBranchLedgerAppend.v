(** Appending tokens whose keys differ from t does not change t's reference
    lookup. Generic over the effect and the interpretation; no RTL. *)
From Coq Require Import List Arith.
Require Import Ex.External.CPUReferenceValues.
Import ListNotations.
Module CPUBranchLedgerAppend.
Section Append.
Context {Architecture Token Value:Type}.
Variable effect:Token->Architecture->option Architecture.
Variable key:Token->nat.
Variable interpret:Token->Architecture->option Value.

Lemma lookup_absent initial extra t:
 (forall x,In x extra ->key x<>key t) ->
 CPUReferenceValues.lookup effect key interpret initial extra t=None.
Proof. revert initial;induction extra as[|x rest IH];intros initial HK;cbn[CPUReferenceValues.lookup];[reflexivity|].
 destruct(Nat.eqb_spec(key x)(key t))as[HE|HE];[exfalso;exact(HK x(or_introl eq_refl)HE)|].
 destruct(effect x initial);[|reflexivity].
 apply IH;intros y HY;exact(HK y(or_intror HY)). Qed.

Theorem lookup_append_absent initial ledger extra t:
 (forall x,In x extra ->key x<>key t) ->
 CPUReferenceValues.lookup effect key interpret initial(ledger++extra)t=
 CPUReferenceValues.lookup effect key interpret initial ledger t.
Proof. intro HK;revert initial;induction ledger as[|x rest IH];intro initial;cbn[app CPUReferenceValues.lookup].
 - exact(lookup_absent initial extra t HK).
 - destruct(Nat.eqb(key x)(key t));[reflexivity|].
   destruct(effect x initial);[apply IH|reflexivity]. Qed.
End Append.
End CPUBranchLedgerAppend.
Print Assumptions CPUBranchLedgerAppend.lookup_absent.
Print Assumptions CPUBranchLedgerAppend.lookup_append_absent.
