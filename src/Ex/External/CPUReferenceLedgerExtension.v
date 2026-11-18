(** Extend a reference ledger without recomputing or changing existing values.
    Range is a present-state ghost invariant, not future CPU correctness. *)
From Coq Require Import List Arith.
Require Import Ex.External.CPUReferenceValues Lang.ExtendedSVCaptureBirth
 Lang.ExtendedSVCapturedPending.
Import ListNotations ExtendedSVCaptureBirth ExtendedSVCapturedPending.
Module CPUReferenceLedgerExtension.
Section Lookup.
Context {Architecture Token Value:Type}.
Variable effect:Token->Architecture->option Architecture.
Variable key:Token->nat.
Variable interpret:Token->Architecture->option Value.
Theorem successful_lookup_has_key initial ledger token value:
 CPUReferenceValues.lookup effect key interpret initial ledger token=Some value ->
 In(key token)(map key ledger).
Proof.
 revert initial;induction ledger as[|head rest IH];intros initial HL;[discriminate|].
 cbn[CPUReferenceValues.lookup]in HL.
 destruct(Nat.eqb(key head)(key token))eqn:HK.
 - apply Nat.eqb_eq in HK;cbn;left;exact HK.
 - destruct(effect head initial)as[next|];[|discriminate].
   cbn;right;exact(IH next HL).
Qed.
Theorem successful_lookup_extends initial ledger extra token value:
 CPUReferenceValues.lookup effect key interpret initial ledger token=Some value ->
 CPUReferenceValues.lookup effect key interpret initial(ledger++extra)token=Some value.
Proof.
 intro HL;rewrite(CPUReferenceValues.append_keeps_existing effect key interpret initial ledger extra token
 (successful_lookup_has_key initial ledger token value HL));exact HL.
Qed.
End Lookup.

Theorem actual_births_preserve_unique_ledger decision serial sampled pc ledger:
 HistoryRange serial ledger ->NoDup(map token_id ledger) ->
 NoDup(map token_id(ledger++NewTokens decision serial sampled pc)).
Proof.
 intros HR HN.
 pose proof(extend_pending decision serial sampled pc ledger ledger HR)as HP.
 assert(HMembers:Forall(fun token=>In token ledger)ledger).
 { apply Forall_forall;intros token HI;exact HI. }
 exact(proj2(HP(conj HMembers HN))).
Qed.

Theorem actual_births_preserve_ledger_range decision serial sampled pc ledger:
 HistoryRange serial ledger ->
 HistoryRange(next_serial decision serial)(ledger++NewTokens decision serial sampled pc).
Proof.
 intro HR;rewrite<-(history_app_birth decision serial sampled pc ledger).
 exact(next_history_range decision serial sampled pc ledger HR).
Qed.
End CPUReferenceLedgerExtension.
Print Assumptions CPUReferenceLedgerExtension.successful_lookup_has_key.
Print Assumptions CPUReferenceLedgerExtension.successful_lookup_extends.
Print Assumptions CPUReferenceLedgerExtension.actual_births_preserve_unique_ledger.
Print Assumptions CPUReferenceLedgerExtension.actual_births_preserve_ledger_range.
