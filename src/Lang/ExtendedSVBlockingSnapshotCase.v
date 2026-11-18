(** Case-aware snapshot compilation. Branch keys are read at the original
    blocking state, and default arms retain their original priority. *)
From Coq Require Import List Bool ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection
 Lang.ExtendedSVAutoAdapterPlan Lang.ExtendedSVAutoAdapterEffects
 Lang.ExtendedSVBlockingSnapshot Lang.ExtendedSVBlockingReplay
 Lang.ExtendedSVBlocking Lang.ExtendedSVScalarExpression Lang.ExtendedSVWordInvariant.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVAutoAdapterPlan
 ExtendedSVAutoAdapterEffects ExtendedSVBlockingSnapshot ExtendedSVBlockingReplay
 ExtendedSVBlocking ExtendedSVScalarExpression ExtendedSVWordInvariant.
Module ExtendedSVBlockingSnapshotCase.

Definition key_safe roots key:=match key with None=>true|Some e=>reads_fromb roots e end.
Fixpoint safe fuel roots plan:=match fuel with O=>false|S f=>match plan with
 |NEmpty=>true
 |NAssign rhs(LVar _ root)=>negb(memberb root roots)&&reads_fromb roots rhs
 |NAssign _ _=>false
 |NSeq plans=>forallb(safe f roots)plans
 |NIf g y n=>reads_fromb roots g&&safe f roots y&&safe f roots n
 |NCase e arms=>reads_fromb roots e&&forallb(fun a=>key_safe roots(fst a)&&safe f roots(snd a))arms
 end end.

Theorem effect_sound fuel:forall roots plan seed es,
 safe fuel roots plan=true->SnapshotAgree roots seed(blocking_state es)->
 emitted_updates(eval_effect(snapshot_effect fuel plan)es)=emitted_updates es++eval_plan seed plan /\
 SnapshotAgree roots seed(blocking_state(eval_effect(snapshot_effect fuel plan)es)).
Proof.
 induction fuel as[|fuel IH];intros roots plan seed es HC HA;[discriminate|].
 destruct plan as[|rhs lhs|plans|g y n|scr arms].
 - cbn [snapshot_effect eval_effect eval_plan]. rewrite app_nil_r. now split.
 - destruct lhs as[w r|];[|discriminate]. cbn [safe]in HC.
   apply andb_true_iff in HC as[HN HE]. apply negb_true_iff in HN.
   pose proof(snapshot_expression roots seed(blocking_state es)rhs HE HA)as HV.
   cbn [snapshot_effect eval_effect eval_plan emitted_updates blocking_state]. split.
   + rewrite HV. reflexivity.
   + apply snapshot_write_other;[|exact HA]. rewrite resolve_update_root. exact HN.
 - cbn [safe]in HC. cbn [snapshot_effect eval_effect eval_plan].
   induction plans as[|p rest IHr]in es,HC,HA|-*.
   + cbn. rewrite app_nil_r. now split.
   + cbn [forallb]in HC. apply andb_true_iff in HC as[HP HR].
     cbn [map fold_left flat_map].
     destruct(IH roots p seed es HP HA)as[HE Hnext].
     destruct(IHr(eval_effect(snapshot_effect fuel p)es)HR Hnext)as[HT Hpost].
     rewrite HT,HE,app_assoc. now split.
 - cbn [safe]in HC. apply andb_true_iff in HC as[HG HN].
   apply andb_true_iff in HG as[HG HY]. cbn [snapshot_effect eval_effect eval_plan].
   rewrite(snapshot_expression roots seed(blocking_state es)g HG HA).
   destruct(Z.eqb(eval_expr seed g)0);apply IH;assumption.
 - cbn [safe]in HC. apply andb_true_iff in HC as[HS HARMS].
   cbn [snapshot_effect eval_effect eval_plan].
   rewrite(snapshot_expression roots seed(blocking_state es)scr HS HA).
   assert(Hcases:forall default updates,
     emitted_updates default=emitted_updates es++updates ->
     SnapshotAgree roots seed(blocking_state default)->
     emitted_updates
       ((fix select xs d:=match xs with
         |[]=>d
         |(None,p)::rest=>select rest(eval_effect p es)
         |(Some key,p)::rest=>if Z.eqb(eval_expr seed scr)(eval_expr(blocking_state es)key)
            then eval_effect p es else select rest d end)
        (map(fun a=>(fst a,snapshot_effect fuel(snd a)))arms)default)=
     emitted_updates es++
       ((fix select xs d:=match xs with
         |[]=>d
         |(None,p)::rest=>select rest(eval_plan seed p)
         |(Some key,p)::rest=>if Z.eqb(eval_expr seed scr)(eval_expr seed key)
            then eval_plan seed p else select rest d end)arms updates) /\
     SnapshotAgree roots seed(blocking_state
       ((fix select xs d:=match xs with
         |[]=>d
         |(None,p)::rest=>select rest(eval_effect p es)
         |(Some key,p)::rest=>if Z.eqb(eval_expr seed scr)(eval_expr(blocking_state es)key)
            then eval_effect p es else select rest d end)
        (map(fun a=>(fst a,snapshot_effect fuel(snd a)))arms)default))).
   { induction arms as[|[key body]rest IHr];intros default updates HD HDA.
     - cbn. now split.
     - cbn [forallb fst snd]in HARMS. apply andb_true_iff in HARMS as[HB HR].
       apply andb_true_iff in HB as[HK HB]. cbn [map fst snd].
       destruct key as[key|].
       + rewrite(snapshot_expression roots seed(blocking_state es)key HK HA).
         destruct(Z.eqb(eval_expr seed scr)(eval_expr seed key)).
         * exact(IH roots body seed es HB HA).
         * apply IHr;assumption.
       + destruct(IH roots body seed es HB HA)as[HE Hpost].
         apply IHr;assumption.
   }
   apply Hcases;[now rewrite app_nil_r|exact HA].
Qed.

Theorem scalar_process p proc plan roots root width fuel ef expression:
 blocking_onlyb(process_body proc)=true ->
 compile_effect(statement_fuel p)(process_body proc)=Some(snapshot_effect fuel plan)->
 safe fuel roots plan=true ->
 compile_scalar ef root width plan(EVar width root)=Some expression ->
 forall s,norm width(read_signal(run_process p s proc)root)=norm width(eval_expr s expression).
Proof.
 intros HB HC HS HE s. rewrite actual_blocking_process_replays by exact HB.
 unfold process_updates. rewrite(compile_effect_sound _ _ _ _ HC).
 pose proof(effect_sound fuel roots plan s
 {|blocking_state:=s;pending_nba:=[];emitted_updates:=[]|}HS(fun _ _=>eq_refl))as[HU _].
 rewrite HU. cbn [emitted_updates app]. rewrite read_signal_apply_updates.
 eapply compile_scalar_sound;[exact HE|]. cbn [eval_expr]. now rewrite norm_idempotent.
Qed.
End ExtendedSVBlockingSnapshotCase.
Print Assumptions ExtendedSVBlockingSnapshotCase.scalar_process.
