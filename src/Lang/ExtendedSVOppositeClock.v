(** An active-low asynchronous reset must be inactive before opposite clock
    edges can exclude one another. No CPU execution property is assumed. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV.
Import ListNotations ExtendedSV.
Module ExtendedSVOppositeClock.
Definition opposite(value:Z):Z:=if Z.eqb value 0 then 1 else 0.
Definition clock_reset_events clock reset:list EventSpec:=
 [{|event_edge:=Posedge;event_signal:=clock|};{|event_edge:=Negedge;event_signal:=reset|}].
Theorem inactive_reset_opposite_edges rf pipeline rfclock rfreset pipeclock pipereset pre sampled:
 process_kind rf=Sequential ->process_events rf=clock_reset_events rfclock rfreset ->
 process_kind pipeline=Sequential ->process_events pipeline=clock_reset_events pipeclock pipereset ->
 read_signal pre rfclock=opposite(read_signal pre pipeclock) ->
 read_signal sampled rfclock=opposite(read_signal sampled pipeclock) ->
 read_signal sampled rfreset<>0%Z ->read_signal sampled pipereset<>0%Z ->
 process_matches_states pre sampled rf=true ->process_matches_states pre sampled pipeline=false.
Proof.
 intros HKR HER HKP HEP HOld HNew HR HP HF.
 unfold process_matches_states in HF|-*;rewrite HKR,HER in HF;rewrite HKP,HEP.
 change((edge_fires Posedge(read_signal pre rfclock)(read_signal sampled rfclock)||
   (edge_fires Negedge(read_signal pre rfreset)(read_signal sampled rfreset)||false))%bool=true)in HF.
 change((edge_fires Posedge(read_signal pre pipeclock)(read_signal sampled pipeclock)||
   (edge_fires Negedge(read_signal pre pipereset)(read_signal sampled pipereset)||false))%bool=false).
 unfold edge_fires in HF|-*;rewrite HOld,HNew in HF.
 assert(HR0:Z.eqb(read_signal sampled rfreset)0=false)by(now apply Z.eqb_neq).
 assert(HP0:Z.eqb(read_signal sampled pipereset)0=false)by(now apply Z.eqb_neq).
 rewrite HR0,andb_false_r,!orb_false_r in HF;rewrite HP0,andb_false_r,!orb_false_r.
 unfold opposite in HF;destruct(Z.eqb(read_signal pre pipeclock)0);
 destruct(Z.eqb(read_signal sampled pipeclock)0);cbn in HF|-*;try discriminate;reflexivity.
Qed.
End ExtendedSVOppositeClock.
Print Assumptions ExtendedSVOppositeClock.inactive_reset_opposite_edges.
