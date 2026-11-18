(** Multi-root output extraction on top of [ExtendedSVSymExecHavoc] (template route, additive; 2026-11-04).  generalized_rule.
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.
    One closed boolean check runs the tail once and compares a LIST of (root, width, expression) triples. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVSymExec Lang.ExtendedSVFactChain Lang.ExtendedSVSymExecSym Lang.ExtendedSVEval4
 Lang.ExtendedSVSymExecOverlay4 Lang.ExtendedSVSymExecHavoc.
Import ListNotations ExtendedSV ExtendedSVSymExec ExtendedSVFactChain ExtendedSVSymExecSym ExtendedSVEval4 ExtendedSVSymExecOverlay4 ExtendedSVSymExecHavoc.
Local Open Scope Z_scope.
Module ExtendedSVSymExecHavocMulti.

Definition hx_chk_m (T:list (list nat)) (k:nat) (F:Facts) (ovP:SOv) (l2:list Stmt) (f:nat) (lst:list (signal*nat*Expr)) : bool :=
 match hxl F f l2 ovP with
 | Some ov => forallb (fun x => hx_out_chk T k F ov (fst (fst x)) (snd (fst x)) (snd x)) lst
 | None => false end.

Theorem hx2_out_m p ps T k proc l1 l2 F1 F ovP f seed fixed lst :
 filter is_comb (processes p) = ps -> TabC ps T -> nth_error ps k = Some proc ->
 facts_inputs_okb F T k = true -> facts_inputs_okb F1 T k = true ->
 FactsHold fixed F -> FactsHold fixed F1 -> CombLFP p seed fixed ->
 nbfix (process_body proc) = SSeq [SSeq (l1 ++ l2)] -> statement_fuel p = S (S f) ->
 hxl F1 f l1 [] = Some ovP -> hx_chk_m T k F ovP l2 f lst = true ->
 forall x, In x lst -> norm (snd (fst x)) (read_signal fixed (fst (fst x))) = norm (snd (fst x)) (eval_expr fixed (snd x)).
Proof.
 intros HP HT HN Hok Hok1 HFH HFH1 HL Hb Hf Hp Hc x Hin. unfold hx_chk_m in Hc.
 destruct (hxl F f l2 ovP) as [ov|] eqn:Hx; [|discriminate].
 rewrite forallb_forall in Hc. specialize (Hc x Hin).
 exact (hx2_out p ps T k proc l1 l2 F1 F ovP ov f seed fixed (fst (fst x)) (snd (fst x)) (snd x) HP HT HN Hok Hok1 HFH HFH1 HL Hb Hf Hp Hx Hc).
Qed.
End ExtendedSVSymExecHavocMulti.
Print Assumptions ExtendedSVSymExecHavocMulti.hx2_out_m.
