(** One-entry event selection without unfolding a concrete CPU in clients. *)
From Coq Require Import List.
Require Import Lang.ExtendedSV Lang.ExtendedSVBankPlan.
Import ListNotations ExtendedSV ExtendedSVBankPlan.
Module ExtendedSVSingleBankEvent.
Theorem not_triggered total proc nb bp pre driven:
 process_matches_states pre driven proc=false ->
 bank_phase_operations total pre driven[Build_BankEntry proc nb bp]=[].
Proof. intro H;cbn[bank_phase_operations flat_map bank_process];now rewrite H. Qed.

Theorem selected_empty total proc nb bp pre driven:
 process_matches_states pre driven proc=true ->eval_bank_plan total driven bp=[] ->
 bank_phase_operations total pre driven[Build_BankEntry proc nb bp]=[].
Proof. intros HP HE;cbn[bank_phase_operations flat_map bank_process bank_plan];now rewrite HP,HE. Qed.
End ExtendedSVSingleBankEvent.
Print Assumptions ExtendedSVSingleBankEvent.not_triggered.
Print Assumptions ExtendedSVSingleBankEvent.selected_empty.
