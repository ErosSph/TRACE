(** Complete branch-selected scalar producers, including the actual NBA case.
    Every execution selects exactly one scalar assignment; no latch assumption. *)
From Coq Require Import List Bool PeanoNat ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVExprAgreement Lang.ExtendedSVAssignment
 Lang.ExtendedSVInferredDependencies.
Import ExtendedSV ExtendedSVExprAgreement ExtendedSVAssignment ExtendedSVInferredDependencies ListNotations.
Module ExtendedSVSingleLeafDependency.
Definition has_defaultb(arms:list(option Expr*Stmt)):=existsb(fun arm=>match fst arm with None=>true|Some _=>false end)arms.
Fixpoint single_leafb fuel width root st:=match fuel with
 |O=>false|S n=>match st with
 |SAssign _ _(LVar w r)=>Nat.eqb w width&&Nat.eqb r root
 |SSeq[x]=>single_leafb n width root x
 |SIf _ a b=>single_leafb n width root a&&single_leafb n width root b
 |SCase _ arms=>has_defaultb arms&&forallb(fun arm=>single_leafb n width root(snd arm))arms
 |_=>false end end.
Lemma selected_leaf fuel width root s value arms default :
 forallb(fun arm=>single_leafb fuel width root(snd arm))arms=true->
 (single_leafb fuel width root default=true\/has_defaultb arms=true)->
 single_leafb fuel width root(select_case_stmt s value arms default)=true.
Proof.
 induction arms as[|[key body]rest IH]in default|-*;cbn;intros HC HD.
 - destruct HD;[assumption|discriminate].
 - apply andb_true_iff in HC as[HB HR]. destruct key as[e|].
   + destruct(Z.eqb value(eval_expr s e));[exact HB|apply IH;[exact HR|exact HD]].
   + apply IH;[exact HR|now left].
Qed.
Lemma selected_inputs s value arms default wr : In wr(statement_inputs(select_case_stmt s value arms default))->
 In wr(statement_inputs default++flat_map(fun arm=>(match fst arm with None=>[]|Some e=>expr_inputs e end)++statement_inputs(snd arm))arms).
Proof.
 induction arms as[|[key body]rest IH]in default|-*;cbn;intro HI.
 - now apply in_or_app;left.
 - destruct key as[e|].
   + destruct(Z.eqb value(eval_expr s e)).
     * apply in_or_app;right. apply in_or_app;left. apply in_or_app;now right.
     * apply IH in HI. apply in_app_or in HI as[HD|HR].
       -- apply in_or_app;now left.
       -- apply in_or_app;right. apply in_or_app;now right.
   + apply IH in HI. apply in_app_or in HI as[HB|HR].
     * apply in_or_app;right. apply in_or_app;now left.
     * apply in_or_app;right. apply in_or_app;now right.
Qed.
Lemma selected_keys_agree s t value arms default :
 (forall key body,In(Some key,body)arms->eval_expr s key=eval_expr t key)->
 select_case_stmt s value arms default=select_case_stmt t value arms default.
Proof.
 induction arms as[|[key body]rest IH]in default|-*;cbn;intro H;[reflexivity|].
 destruct key as[e|].
 - rewrite(H e body(or_introl eq_refl)). destruct(Z.eqb value(eval_expr t e));[reflexivity|apply IH;intros k b HI;apply(H k b);now right].
 - apply IH;intros k b HI;apply(H k b);now right.
Qed.
Definition body_run fuel st s:=let es:=exec_stmt fuel st{|blocking_state:=s;pending_nba:=[];emitted_updates:=[]|}in
 apply_nba(blocking_state es)(pending_nba es).
Theorem actual_single_leaf_dependency fuel width root st s t :
 single_leafb fuel width root st=true->InputsAgree s t(statement_inputs st)->
 norm width(read_signal(body_run fuel st s)root)=norm width(read_signal(body_run fuel st t)root).
Proof.
 induction fuel as[|fuel IH]in st,s,t|-*;[discriminate|].
 destruct st as[|nba e l|xs|g a b|scr arms];cbn[single_leafb];intros HC HA;try discriminate.
 - destruct l as[w r|];[|discriminate]. apply andb_true_iff in HC as[HW HR].
   apply Nat.eqb_eq in HW,HR. subst w r.
   assert(HE:eval_expr s e=eval_expr t e)by(now apply eval_expr_agree).
   assert(Hrun:forall ss,body_run(S fuel)(SAssign nba e(LVar width root))ss=
     apply_update ss(resolve_update ss(LVar width root)(eval_expr ss e)))by(intro ss;destruct nba;reflexivity).
   rewrite !Hrun. unfold apply_update,resolve_update.
   cbn[resolve_lvalue update_signal update_offset update_width update_value].
   rewrite !read_signal_write_same,!norm_full_low_write,HE;reflexivity.
 - destruct xs as[|x[|y rest]];try discriminate.
   change(norm width(read_signal(body_run fuel x s)root)=norm width(read_signal(body_run fuel x t)root)).
   apply IH;[exact HC|]. cbn[statement_inputs flat_map]in HA. now rewrite app_nil_r in HA.
 - apply andb_true_iff in HC as[HY HN].
   assert(HG:eval_expr s g=eval_expr t g).
   { apply eval_expr_agree. exact(agree_app_left _ _ _ _ HA). }
   unfold body_run at 1 2. cbn[exec_stmt blocking_state]. rewrite HG.
   destruct(Z.eqb(eval_expr t g)0).
   + apply IH;[exact HN|exact(agree_app_right _ _ _ _(agree_app_right _ _ _ _ HA))].
   + apply IH;[exact HY|exact(agree_app_left _ _ _ _(agree_app_right _ _ _ _ HA))].
 - apply andb_true_iff in HC as[HD HB].
   assert(HG:eval_expr s scr=eval_expr t scr).
   { apply eval_expr_agree. exact(agree_app_left _ _ _ _ HA). }
   assert(Hkeys:forall key body,In(Some key,body)arms->eval_expr s key=eval_expr t key).
   { intros key body HI. apply eval_expr_agree. intros w r HR. apply HA.
     apply in_or_app;right. apply in_flat_map. exists(Some key,body). split;[exact HI|]. cbn. apply in_or_app;now left. }
   unfold body_run at 1 2. cbn[exec_stmt blocking_state]. rewrite HG,(selected_keys_agree s t(eval_expr t scr)arms SSkip Hkeys).
   apply IH;[apply selected_leaf;[exact HB|now right]|].
   intros w r HR. apply HA. apply in_or_app;right.
   exact(selected_inputs t(eval_expr t scr)arms SSkip(w,r)HR).
Qed.
Theorem actual_single_leaf_process p proc width root :
 single_leafb(statement_fuel p)width root(process_body proc)=true->forall s t,
 InputsAgree s t(statement_inputs(process_body proc))->
 norm width(read_signal(run_process p s proc)root)=norm width(read_signal(run_process p t proc)root).
Proof. intros HC s t HA. exact(actual_single_leaf_dependency _ _ _ _ _ _ HC HA). Qed.
Print Assumptions actual_single_leaf_process.
End ExtendedSVSingleLeafDependency.
