(** Forward fact propagation along the combinational order (template route).

    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.

    [chain] visits comb processes in a given index list.  At step [k] the facts named by the generator
    that only read roots not written by the prefix, or not written by [proc :: suffix] (the pivot-input
    condition of ExtendedSVCombConnection, as in checked_assignment_binding) are handed to the symbolic
    executor; every root the process writes and that no later comb process writes becomes a fact
    [EVar w r = z].  Writer sets come from a table [T] checked once ([tab_okb]).  Nothing is assumed:
    the starting facts are the hypothesis of the final statement. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVSymExec Lang.ExtendedSVConstantRoot
 Lang.ExtendedSVCombCut Lang.ExtendedSVExprAgreement.
Import ListNotations ExtendedSV ExtendedSVSymExec ExtendedSVConstantRoot ExtendedSVCombCut ExtendedSVExprAgreement.
Local Open Scope Z_scope.
Module ExtendedSVFactChain.

Definition tail_okb (T:list (list nat)) (k:nat) (ez:Expr*Z) : bool :=
 forallb (fun wr => wr_ge T (snd wr) k || wr_lt T (snd wr) k) (expr_inputs (fst ez)).

Definition new_facts (ov:Ov) (T:list (list nat)) (k:nat) : Facts :=
 flat_map (fun e => match e with (r,(w,z)) =>
   match ov_lookup ov r with
   | Some (w',z') => if Nat.eqb w w' && Z.eqb z z' && wr_lt T r k then [(EVar w r, z)] else []
   | None => []
   end end) ov.

Lemma new_facts_in ov T k e z : In (e,z) (new_facts ov T k) ->
 exists r w, e = EVar w r /\ ov_lookup ov r = Some (w,z) /\ wr_lt T r k = true.
Proof.
 unfold new_facts. intro H. apply in_flat_map in H as [[r [w0 z0]] [_ H]].
 destruct (ov_lookup ov r) as [[w' z']|] eqn:Hl; [|contradiction].
 destruct (Nat.eqb w0 w' && Z.eqb z0 z' && wr_lt T r k) eqn:Hc; [|contradiction].
 destruct H as [H|H]; [|contradiction]. inversion H; subst; clear H.
 apply andb_true_iff in Hc as [Hc Hr]. apply andb_true_iff in Hc as [Hw Hz].
 apply Nat.eqb_eq in Hw. apply Z.eqb_eq in Hz. subst w' z'.
 exists r, w0. auto.
Qed.

(** The generator names the facts a step may use (indices into the current fact list). *)
Definition pick (F:Facts) (idx:list nat) : Facts :=
 flat_map (fun i => match nth_error F i with Some f => [f] | None => [] end) idx.

Lemma pick_in F idx f : In f (pick F idx) -> In f F.
Proof.
 unfold pick. intro H. apply in_flat_map in H as [i [_ H]].
 destruct (nth_error F i) as [g|] eqn:E; [|contradiction].
 destruct H as [H|H]; [|contradiction]. subst. exact (nth_error_In _ _ E).
Qed.

Definition step_facts (ps:list Process) (T:list (list nat)) (fuel:nat) (F:Facts) (st:nat*list nat) : option Facts :=
 let k := fst st in
 match nth_error ps k with
 | None => None
 | Some proc =>
   match xexec (filter (tail_okb T k) (pick F (snd st))) fuel (nbfix (process_body proc)) [] with
   | None => None
   | Some ov => Some (F ++ new_facts ov T (S k))
   end
 end.

Fixpoint chain (ps:list Process) (T:list (list nat)) (fuel:nat) (F:Facts) (ks:list (nat*list nat)) : option Facts :=
 match ks with
 | [] => Some F
 | k::rest => match step_facts ps T fuel F k with Some F' => chain ps T fuel F' rest | None => None end
 end.

Lemma step_facts_sound p ps T fuel F st F' seed fixed :
 filter is_comb (processes p) = ps -> TabC ps T -> fuel = statement_fuel p ->
 FactsHold fixed F -> CombLFP p seed fixed -> step_facts ps T fuel F st = Some F' -> FactsHold fixed F'.
Proof.
 intros HP HT Hf HFH HL H. subst fuel. unfold step_facts in H.
 destruct (nth_error ps (fst st)) as [proc|] eqn:HN; [|discriminate].
 destruct (xexec (filter (tail_okb T (fst st)) (pick F (snd st))) (statement_fuel p) (nbfix (process_body proc)) []) as [ov|] eqn:Hx; [|discriminate].
 inversion H; subst F'; clear H.
 set (F0 := filter (tail_okb T (fst st)) (pick F (snd st))) in *.
 assert (H0: FactsHold fixed F0).
 { intros e z HI. apply filter_In in HI as [HI _]. apply HFH, (pick_in _ _ _ HI). }
 assert (Hok: facts_inputs_okb F0 T (fst st) = true).
 { unfold facts_inputs_okb. apply forallb_forall. intros ez HI. apply filter_In in HI as [_ HT'].
   exact HT'. }
 intros e z HI. apply in_app_or in HI as [HI|HI]; [apply HFH, HI|].
 destruct (new_facts_in _ _ _ _ _ HI) as [r [w [-> [Hl Hr]]]].
 pose proof (xrun_comb_lfp p ps T (fst st) proc F0 ov seed fixed HP HT HN Hok H0 HL Hx _ _ _ Hl Hr) as Hv.
 cbn [eval_expr]. exact Hv.
Qed.

Theorem chain_sound p ps T fuel (ks:list (nat*list nat)) : forall F F' seed fixed,
 filter is_comb (processes p) = ps -> TabC ps T -> fuel = statement_fuel p ->
 FactsHold fixed F -> CombLFP p seed fixed -> chain ps T fuel F ks = Some F' -> FactsHold fixed F'.
Proof.
 induction ks as [|k rest IH]; intros F F' seed fixed HP HT Hf HFH HL H; cbn [chain] in H.
 - inversion H; subst; exact HFH.
 - destruct (step_facts ps T fuel F k) as [F1|] eqn:Hs; [|discriminate].
   exact (IH F1 F' seed fixed HP HT Hf (step_facts_sound p ps T fuel F k F1 seed fixed HP HT Hf HFH HL Hs) HL H).
Qed.

Definition outs_in_facts (F:Facts) (outs:list ((signal*nat)*Z)) : bool :=
 forallb (fun t => match fact_find F (EVar (snd (fst t)) (fst (fst t))) with
   | Some z => Z.eqb z (snd t) | None => false end) outs.

Definition chain_outs_okb (ps:list Process) (T:list (list nat)) (fuel:nat) (F0:Facts) (ks:list (nat*list nat)) (outs:list ((signal*nat)*Z)) : bool :=
 tab_okb ps T && match chain ps T fuel F0 ks with Some F => outs_in_facts F outs | None => false end.

Theorem chain_outs_ok p ps T ks F0 outs seed fixed :
 filter is_comb (processes p) = ps ->
 FactsHold fixed F0 -> CombLFP p seed fixed ->
 chain_outs_okb ps T (statement_fuel p) F0 ks outs = true -> DecOut fixed outs.
Proof.
 intros HP HFH HL H. unfold chain_outs_okb in H. apply andb_true_iff in H as [Ht H].
 destruct (chain ps T (statement_fuel p) F0 ks) as [F|] eqn:Hc; [|discriminate].
 pose proof (chain_sound p ps T (statement_fuel p) ks F0 F seed fixed HP (tab_okb_sound _ _ Ht) eq_refl HFH HL Hc) as HF.
 intros t Ht'. unfold outs_in_facts in H. rewrite forallb_forall in H. specialize (H t Ht').
 destruct (fact_find F (EVar (snd (fst t)) (fst (fst t)))) as [z|] eqn:Hf; [|discriminate].
 apply Z.eqb_eq in H. subst z.
 pose proof (fact_find_sound F _ _ fixed HF Hf) as Hv. cbn [eval_expr] in Hv. exact Hv.
Qed.

Definition chain_check (ps:list Process) (T:list (list nat)) (fuel:nat) (F0:Facts) (ks:list (nat*list nat)) (outs:list ((signal*nat)*Z)) : bool :=
 match chain ps T fuel F0 ks with Some F => outs_in_facts F outs | None => false end.

(** Variant with the table checked once, outside (shared by all classes). *)
Theorem chain_outs_tab p ps T ks F0 outs seed fixed :
 filter is_comb (processes p) = ps -> TabC ps T ->
 FactsHold fixed F0 -> CombLFP p seed fixed ->
 chain_check ps T (statement_fuel p) F0 ks outs = true -> DecOut fixed outs.
Proof.
 intros HP HT HFH HL H. unfold chain_check in H.
 destruct (chain ps T (statement_fuel p) F0 ks) as [F|] eqn:Hc; [|discriminate].
 pose proof (chain_sound p ps T (statement_fuel p) ks F0 F seed fixed HP HT eq_refl HFH HL Hc) as HF.
 intros t Ht'. unfold outs_in_facts in H. rewrite forallb_forall in H. specialize (H t Ht').
 destruct (fact_find F (EVar (snd (fst t)) (fst (fst t)))) as [z|] eqn:Hf; [|discriminate].
 apply Z.eqb_eq in H. subst z.
 pose proof (fact_find_sound F _ _ fixed HF Hf) as Hv. cbn [eval_expr] in Hv. exact Hv.
Qed.
End ExtendedSVFactChain.
Print Assumptions ExtendedSVFactChain.chain_outs_tab.
Print Assumptions ExtendedSVFactChain.chain_outs_ok.
