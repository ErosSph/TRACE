(** A checked bridge from blocking control logic to sampled update plans.
    The read/write-disjointness check is essential: blocking temporaries must
    not silently be interpreted as old-state NBA reads. Case support remains
    a residual of this first backend, not an assumed equivalence. *)
From Coq Require Import List Bool ZArith PeanoNat.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection
 Lang.ExtendedSVExprAgreement Lang.ExtendedSVAutoAdapterPlan
 Lang.ExtendedSVAutoAdapterEffects Lang.ExtendedSVBlockingReplay Lang.ExtendedSVBlocking.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVExprAgreement
 ExtendedSVAutoAdapterPlan ExtendedSVAutoAdapterEffects ExtendedSVBlockingReplay ExtendedSVBlocking.
Module ExtendedSVBlockingSnapshot.

Definition memberb root roots := existsb (Nat.eqb root) roots.
Definition reads_fromb roots expression :=
 forallb (fun wr=>memberb (snd wr) roots) (expr_inputs expression).
Definition SnapshotAgree roots seed live :=
 forall root,In root roots ->read_signal live root=read_signal seed root.

Lemma memberb_sound root roots : memberb root roots=true ->In root roots.
Proof.
 unfold memberb. rewrite existsb_exists. intros [r [HI HE]].
 apply Nat.eqb_eq in HE. now subst r.
Qed.
Lemma memberb_complete root roots : In root roots ->memberb root roots=true.
Proof. intro HI. unfold memberb. apply existsb_exists. exists root.
 split;[exact HI|apply Nat.eqb_refl]. Qed.
Lemma snapshot_expression roots seed live expression :
 reads_fromb roots expression=true ->SnapshotAgree roots seed live ->
 eval_expr live expression=eval_expr seed expression.
Proof.
 intros HC HA. apply eval_expr_agree. intros w root HI.
 pose proof(proj1(forallb_forall _ _)HC(w,root)HI)as HM.
 cbn [snd] in HM. rewrite(HA root(memberb_sound root roots HM)). reflexivity.
Qed.
Lemma snapshot_write_other roots seed live update :
 memberb(update_signal update)roots=false ->SnapshotAgree roots seed live ->
 SnapshotAgree roots seed(apply_update live update).
Proof.
 intros HN HA root HI. rewrite read_signal_apply_update_other.
 - exact(HA root HI).
 - intro HE. rewrite HE,(memberb_complete root roots HI)in HN. discriminate.
Qed.

Fixpoint snapshot_safe fuel roots plan : bool :=
 match fuel with O=>false|S f=>match plan with
 |NEmpty=>true
 |NAssign rhs(LVar _ root)=>negb(memberb root roots)&&reads_fromb roots rhs
 |NAssign _ _=>false
 |NSeq plans=>forallb(snapshot_safe f roots)plans
 |NIf guard yes no=>reads_fromb roots guard&&snapshot_safe f roots yes&&snapshot_safe f roots no
 |NCase _ _=>false
 end end.

Fixpoint snapshot_effect fuel plan : EffectPlan :=
 match fuel with O=>FEmpty|S f=>match plan with
 |NEmpty=>FEmpty
 |NAssign rhs lhs=>FAssign false rhs lhs
 |NSeq plans=>FSeq(map(snapshot_effect f)plans)
 |NIf guard yes no=>FIf guard(snapshot_effect f yes)(snapshot_effect f no)
 |NCase scr arms=>FCase scr(map(fun arm=>(fst arm,snapshot_effect f(snd arm)))arms)
 end end.

Theorem snapshot_effect_sound fuel : forall roots plan seed es,
 snapshot_safe fuel roots plan=true ->SnapshotAgree roots seed(blocking_state es) ->
 emitted_updates(eval_effect(snapshot_effect fuel plan)es)=
  emitted_updates es++eval_plan seed plan /\
 SnapshotAgree roots seed(blocking_state(eval_effect(snapshot_effect fuel plan)es)).
Proof.
 induction fuel as[|fuel IH];intros roots plan seed es HC HA;[discriminate|].
 destruct plan as[|rhs lhs|plans|guard yes no|scr arms].
 - cbn [snapshot_effect eval_effect eval_plan]. rewrite app_nil_r. now split.
 - destruct lhs as[width root|];[|discriminate].
   cbn [snapshot_safe]in HC. apply andb_true_iff in HC as[HN HE].
   apply negb_true_iff in HN.
   pose proof(snapshot_expression roots seed(blocking_state es)rhs HE HA)as HV.
   cbn [snapshot_effect eval_effect eval_plan emitted_updates blocking_state].
   split.
   + rewrite HV. reflexivity.
   + apply snapshot_write_other;[|exact HA]. rewrite resolve_update_root. exact HN.
 - cbn [snapshot_safe]in HC.
   cbn [snapshot_effect eval_effect eval_plan].
   induction plans as[|p rest IHr]in es,HC,HA|-*.
   + cbn. rewrite app_nil_r. now split.
   + cbn [forallb]in HC. apply andb_true_iff in HC as[HP HR].
     cbn [map fold_left flat_map].
     destruct(IH roots p seed es HP HA)as[HE Hnext].
     destruct(IHr(eval_effect(snapshot_effect fuel p)es)HR Hnext)as[HT HApost].
     rewrite HT,HE,app_assoc. now split.
 - cbn [snapshot_safe]in HC. apply andb_true_iff in HC as[Hboth HN].
   apply andb_true_iff in Hboth as[HG HY].
   cbn [snapshot_effect eval_effect eval_plan].
   rewrite(snapshot_expression roots seed(blocking_state es)guard HG HA).
   destruct(Z.eqb(eval_expr seed guard)0);apply IH;assumption.
 - discriminate.
Qed.

Theorem actual_snapshot_updates p proc fuel roots plan :
 compile_effect(statement_fuel p)(process_body proc)=Some(snapshot_effect fuel plan) ->
 snapshot_safe fuel roots plan=true ->forall s,
 process_updates p s proc=eval_plan s plan.
Proof.
 intros HC HS s. unfold process_updates.
 rewrite(compile_effect_sound _ _ _ _ HC).
 pose proof(snapshot_effect_sound fuel roots plan s
  {|blocking_state:=s;pending_nba:=[];emitted_updates:=[]|}HS
  (fun _ _=>eq_refl))as[HE _]. exact HE.
Qed.
Theorem actual_snapshot_process p proc fuel roots plan :
 blocking_onlyb(process_body proc)=true ->
 compile_effect(statement_fuel p)(process_body proc)=Some(snapshot_effect fuel plan) ->
 snapshot_safe fuel roots plan=true ->forall s,
 run_process p s proc=apply_updates s(eval_plan s plan).
Proof.
 intros HB HC HS s. rewrite actual_blocking_process_replays by exact HB.
 rewrite(actual_snapshot_updates p proc fuel roots plan HC HS s). reflexivity.
Qed.
End ExtendedSVBlockingSnapshot.
Print Assumptions ExtendedSVBlockingSnapshot.snapshot_effect_sound.
Print Assumptions ExtendedSVBlockingSnapshot.actual_snapshot_updates.
Print Assumptions ExtendedSVBlockingSnapshot.actual_snapshot_process.
