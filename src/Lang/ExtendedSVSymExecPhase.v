(** Shared engine glue for the per-clause phase proofs (template route, additive; 2026-11-03).
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.
    [sx_pass_outs]: the control-cone theorem a generated module instantiates per case: facts hold at a comb fixed point and a
    generator-recorded step list [ks] (comb positions) re-derives, by computation, the constant values [outs].
    [sym_wire]: a (possibly symbolic) root written by the comb process at position [k] has, at the fixed point, the value of the
    expression [e] that [sxexec] returns for it (the wire expression of a datapath signal under the case facts).
    [decout_facts]: derived constants are usable as facts again (for the sequential-capture lemmas). *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVSymExec Lang.ExtendedSVFactChain Lang.ExtendedSVSymExecSym.
Import ListNotations ExtendedSV ExtendedSVSymExec ExtendedSVFactChain ExtendedSVSymExecSym.
Local Open Scope Z_scope.
Module ExtendedSVSymExecPhase.

Theorem sx_pass_outs p ps T ks F0 outs seed fixed :
 filter is_comb (processes p) = ps -> TabC ps T -> FactsHold fixed F0 -> CombLFP p seed fixed ->
 outs_in_facts (sx_pass ps T (statement_fuel p) F0 ks) outs = true -> DecOut fixed outs.
Proof.
 intros HP HT HF HL H.
 pose proof (sx_pass_sound p ps T (statement_fuel p) seed fixed HP HT eq_refl HL ks F0 HF) as HF'.
 intros t Ht'. unfold outs_in_facts in H. rewrite forallb_forall in H. specialize (H t Ht').
 destruct (fact_find (sx_pass ps T (statement_fuel p) F0 ks) (EVar (snd (fst t)) (fst (fst t)))) as [z|] eqn:Hf; [|discriminate].
 apply Z.eqb_eq in H. subst z.
 pose proof (fact_find_sound _ _ _ fixed HF' Hf) as Hv. cbn [eval_expr] in Hv. exact Hv.
Qed.

Definition outs_as_facts (outs : list ((signal*nat)*Z)) : Facts :=
 map (fun t => (EVar (snd (fst t)) (fst (fst t)), snd t)) outs.
Lemma decout_facts s outs : DecOut s outs -> FactsHold s (outs_as_facts outs).
Proof.
 intros H e z HI. unfold outs_as_facts in HI. apply in_map_iff in HI as [t [Ht Hin]]. inversion Ht; subst.
 cbn [eval_expr]. exact (H t Hin).
Qed.

(** value of a (symbolic) wire at the fixed point: the facts are filtered by [tail_okb] at the process position, as in the chain *)
Theorem sym_wire p ps T k proc F ov seed fixed r w e :
 filter is_comb (processes p) = ps -> TabC ps T -> nth_error ps k = Some proc -> CombLFP p seed fixed -> FactsHold fixed F ->
 sxexec (filter (tail_okb T k) F) (statement_fuel p) (nbfix (process_body proc)) [] = Some ov ->
 sov_lookup ov r = Some (w, e) -> wr_lt T r (S k) = true -> inputs_okb T k e = true ->
 norm w (read_signal fixed r) = norm w (eval_expr fixed e).
Proof.
 intros HP HT HN HL HF Hx Hl Hr Hie.
 assert (H0 : FactsHold fixed (filter (tail_okb T k) F)) by (intros e0 z HI; apply filter_In in HI as [HI _]; apply HF, HI).
 assert (Hok : facts_inputs_okb (filter (tail_okb T k) F) T k = true).
 { unfold facts_inputs_okb. apply forallb_forall. intros ez HI. apply filter_In in HI as [_ HT']. exact HT'. }
 exact (sxrun_comb_lfp p ps T k proc _ ov seed fixed HP HT HN Hok H0 HL Hx r w e Hl Hr Hie).
Qed.

(** closed form for generated modules: the lookup is computed, so the overlay need not be named *)
Definition sx_wire (ps:list Process) (fuel:nat) (T:list (list nat)) (F:Facts) (k:nat) (r:signal) : option (nat*Expr) :=
 match nth_error ps k with
 | None => None
 | Some proc => match sxexec (filter (tail_okb T k) F) fuel (nbfix (process_body proc)) [] with
    | Some ov => if wr_lt T r (S k) then sov_lookup ov r else None
    | None => None end
 end.

Theorem sym_wire_c p ps T k F seed fixed r w e :
 filter is_comb (processes p) = ps -> TabC ps T -> CombLFP p seed fixed -> FactsHold fixed F ->
 sx_wire ps (statement_fuel p) T F k r = Some (w, e) -> inputs_okb T k e = true ->
 norm w (read_signal fixed r) = norm w (eval_expr fixed e).
Proof.
 intros HP HT HL HF H Hie. unfold sx_wire in H.
 destruct (nth_error ps k) as [proc|] eqn:HN; [|discriminate].
 destruct (sxexec (filter (tail_okb T k) F) (statement_fuel p) (nbfix (process_body proc)) []) as [ov|] eqn:Hx; [|discriminate].
 destruct (wr_lt T r (S k)) eqn:Hr; [|discriminate].
 exact (sym_wire p ps T k proc F ov seed fixed r w e HP HT HN HL HF Hx H Hr Hie).
Qed.
End ExtendedSVSymExecPhase.
Print Assumptions ExtendedSVSymExecPhase.sx_pass_outs.
Print Assumptions ExtendedSVSymExecPhase.sym_wire.
Print Assumptions ExtendedSVSymExecPhase.sym_wire_c.
