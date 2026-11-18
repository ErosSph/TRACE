(** Capture order is derived from serial allocation and real queue prefix
    consumption. It is not yet ISA address order or an ISA refinement. *)
From Coq Require Import List Arith Lia Sorting.Sorted Sorting.Permutation ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVCaptureBirth Lang.ExtendedSVCapturedPending
 Lang.ExtendedSVCaptureAccounting Lib.CheckedPendingQueue.
Import ListNotations ExtendedSV ExtendedSVCaptureBirth ExtendedSVCapturedPending.
Module ExtendedSVCaptureAge.
Module A:=ExtendedSVCaptureAccounting.
Definition Before(x y:Token):=(token_id x<token_id y)%nat.
Definition AgeOrdered:=StronglySorted Before.
Definition Live(a:A.Accounts):=A.retired a++A.waiting a.

Theorem append_later queue serial token:
 AgeOrdered queue ->Forall(fun t=>(token_id t<serial)%nat)queue ->
 token_id token=serial ->AgeOrdered(queue++[token]).
Proof.
 intros HS;induction HS as[|head rest HS IH Hhead];intros HR HT;cbn.
 - constructor;constructor.
 - pose proof(Forall_inv HR)as HX;pose proof(Forall_inv_tail HR)as Hrest;constructor.
   + exact(IH Hrest HT).
   + apply Forall_app;split;[exact Hhead|]. constructor;[unfold Before;rewrite HT;exact HX|constructor].
Qed.

Theorem ordered_separation retired waiting:
 AgeOrdered(retired++waiting) ->Forall(fun old=>Forall(Before old)waiting)retired.
Proof.
 induction retired as[|head rest IH];cbn;intro HS;[constructor|].
 apply StronglySorted_inv in HS as[HT HH];apply Forall_app in HH as[HX HY].
 constructor;[exact HY|exact(IH HT)].
Qed.

Theorem live_range serial ledger a:
 HistoryRange serial ledger ->A.AccountsFor ledger a ->
 Forall(fun t=>(token_id t<serial)%nat)(Live a).
Proof.
 intros HR HA;apply Forall_forall;intros token HI;unfold HistoryRange in HR.
 apply Forall_forall with(x:=token)in HR;[exact HR|].
 apply(Permutation_in token(Permutation_sym HA));unfold Live in HI.
 apply in_app_or in HI as[HI|HI];apply in_or_app;[now left|].
 right;apply in_or_app;now left.
Qed.

Theorem advance_live_equality a admitted retiring next:
 A.advance a admitted retiring 0=Some next ->Live next=Live a++admitted.
Proof.
 unfold A.advance;destruct(CheckedPendingQueue.step token_eq_dec(A.waiting a)admitted retiring 0)
 as[[kept killed]|]eqn:HC;[|discriminate].
 intro HS;inversion HS;subst next;unfold Live;cbn[A.retired A.waiting].
 pose proof(CheckedPendingQueue.step_no_cancel_streaming token_eq_dec _ _ _ _ _ HC)as[HK HP].
 repeat rewrite <-app_assoc;now rewrite <-HP.
Qed.

Theorem actual_normal_advance_age p proc root word valid pc ev pre g a retiring next:
 HistoryRange(serial g)(history g) ->A.AccountsFor(history g)a ->AgeOrdered(Live a) ->
 A.advance a(observed_births p proc root word valid pc ev pre g)retiring 0=Some next ->
 AgeOrdered(Live next).
Proof.
 intros HR HA HS Hstep;rewrite(advance_live_equality a _ retiring next Hstep).
 unfold observed_births;destruct(phase_decision p proc root word valid ev pre);
 cbn[NewTokens birth];try(now rewrite app_nil_r).
 eapply append_later;[exact HS|exact(live_range(serial g)(history g)a HR HA)|reflexivity].
Qed.

Example same_word_distinct_captures_are_ordered:
 AgeOrdered[Build_Token 1 17 None;Build_Token 2 17 None].
Proof. repeat constructor;unfold Before;cbn[token_id];lia. Qed.
Example reversed_capture_order_is_rejected:
 ~AgeOrdered[Build_Token 2 17 None;Build_Token 1 17 None].
Proof.
 intro HS;apply StronglySorted_inv in HS as[HT HH].
 apply Forall_inv in HH;unfold Before in HH;cbn[token_id]in HH;lia.
Qed.
Print Assumptions append_later.
Print Assumptions ordered_separation.
Print Assumptions live_range.
Print Assumptions advance_live_equality.
Print Assumptions actual_normal_advance_age.
Print Assumptions same_word_distinct_captures_are_ordered.
Print Assumptions reversed_capture_order_is_rejected.
End ExtendedSVCaptureAge.
