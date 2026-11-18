(** Clock boundary consequences, separate from a particular large Program. *)
From Coq Require Import ZArith Bool List.
Require Import Lang.ExtendedSV Lang.ExtendedSVOppositeClock.
Import ListNotations ExtendedSV ExtendedSVOppositeClock.
Module ExtendedSVClockBoundary.
Lemma opposite_boundary (old new oldreset newreset:Z):
 newreset<>0%Z ->
 (edge_fires Posedge(opposite old)(opposite new)||
  (edge_fires Negedge oldreset newreset||false))%bool=true ->
 old<>0%Z /\ new=0%Z.
Proof.
 intros HR HF;unfold edge_fires in HF.
 assert(HReset:Z.eqb newreset 0=false)by(now apply Z.eqb_neq).
 rewrite HReset,andb_false_r,!orb_false_r in HF.
 unfold opposite in HF;destruct(Z.eqb old 0)eqn:HO;
 destruct(Z.eqb new 0)eqn:HN;cbn in HF;try discriminate.
 split;[now apply Z.eqb_neq|now apply Z.eqb_eq].
Qed.
Theorem opposite_process_boundary rf rfclock rfreset pipeclock pre sampled:
 process_kind rf=Sequential ->process_events rf=clock_reset_events rfclock rfreset ->
 read_signal pre rfclock=opposite(read_signal pre pipeclock) ->
 read_signal sampled rfclock=opposite(read_signal sampled pipeclock) ->
 read_signal sampled rfreset<>0%Z ->process_matches_states pre sampled rf=true ->
 read_signal pre pipeclock<>0%Z /\ read_signal sampled pipeclock=0%Z.
Proof.
 intros HK HE HO HN HR HF;unfold process_matches_states in HF;rewrite HK,HE in HF.
 change((edge_fires Posedge(read_signal pre rfclock)(read_signal sampled rfclock)||
 (edge_fires Negedge(read_signal pre rfreset)(read_signal sampled rfreset)||false))%bool=true)in HF.
 rewrite HO,HN in HF;exact(opposite_boundary _ _ _ _ HR HF).
Qed.
End ExtendedSVClockBoundary.
Print Assumptions ExtendedSVClockBoundary.opposite_boundary.
Print Assumptions ExtendedSVClockBoundary.opposite_process_boundary.
