(** Backward propagation + scripts through the overlay executor (template route, additive; 2026-11-03).
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.
    Same as ExtendedSVBackward but over [oxexec] ([ox_wire], [ox_step]); uses [decomp]/[decomp_sound] of ExtendedSVBackward. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVSymExec Lang.ExtendedSVFactChain Lang.ExtendedSVSymExecSym Lang.ExtendedSVSymExecOverlay Lang.ExtendedSVExpressionFold Lang.ExtendedSVBackward.
Import ListNotations ExtendedSV ExtendedSVSymExec ExtendedSVFactChain ExtendedSVSymExecSym ExtendedSVSymExecOverlay ExtendedSVExpressionFold ExtendedSVBackward.
Local Open Scope Z_scope.
Module ExtendedSVBackOverlay.
(** value of a (symbolic) wire at the fixed point: the facts are filtered by [tail_okb] at the process position, as in the chain *)
Theorem ox_sym_wire p ps T k proc F ov seed fixed r w e :
 filter is_comb (processes p) = ps -> TabC ps T -> nth_error ps k = Some proc -> CombLFP p seed fixed -> FactsHold fixed F ->
 oxexec (filter (tail_okb T k) F) (statement_fuel p) (nbfix (process_body proc)) [] = Some ov ->
 sov_lookup ov r = Some (w, e) -> wr_lt T r (S k) = true -> inputs_okb T k e = true ->
 norm w (read_signal fixed r) = norm w (eval_expr fixed e).
Proof.
 intros HP HT HN HL HF Hx Hl Hr Hie.
 assert (H0 : FactsHold fixed (filter (tail_okb T k) F)) by (intros e0 z HI; apply filter_In in HI as [HI _]; apply HF, HI).
 assert (Hok : facts_inputs_okb (filter (tail_okb T k) F) T k = true).
 { unfold facts_inputs_okb. apply forallb_forall. intros ez HI. apply filter_In in HI as [_ HT']. exact HT'. }
 exact (oxrun_comb_lfp p ps T k proc _ ov seed fixed HP HT HN Hok H0 HL Hx r w e Hl Hr Hie).
Qed.

(** closed form for generated modules: the lookup is computed, so the overlay need not be named *)
Definition ox_wire (ps:list Process) (fuel:nat) (T:list (list nat)) (F:Facts) (k:nat) (r:signal) : option (nat*Expr) :=
 match nth_error ps k with
 | None => None
 | Some proc => match oxexec (filter (tail_okb T k) F) fuel (nbfix (process_body proc)) [] with
    | Some ov => if wr_lt T r (S k) then sov_lookup ov r else None
    | None => None end
 end.

Theorem ox_wire_c p ps T k F seed fixed r w e :
 filter is_comb (processes p) = ps -> TabC ps T -> CombLFP p seed fixed -> FactsHold fixed F ->
 ox_wire ps (statement_fuel p) T F k r = Some (w, e) -> inputs_okb T k e = true ->
 norm w (read_signal fixed r) = norm w (eval_expr fixed e).
Proof.
 intros HP HT HL HF H Hie. unfold ox_wire in H.
 destruct (nth_error ps k) as [proc|] eqn:HN; [|discriminate].
 destruct (oxexec (filter (tail_okb T k) F) (statement_fuel p) (nbfix (process_body proc)) []) as [ov|] eqn:Hx; [|discriminate].
 destruct (wr_lt T r (S k)) eqn:Hr; [|discriminate].
 exact (ox_sym_wire p ps T k proc F ov seed fixed r w e HP HT HN HL HF Hx H Hr Hie).
Qed.
(** one backward step at the comb position [k] for the root [r]: uses the known value of [r] *)
Definition oback_wire (ps:list Process) (T:list (list nat)) (fuel:nat) (F:Facts) (k:nat) (r:signal) : Facts :=
  match fact_find F (EVar 1%nat r) with
  | None => []
  | Some v =>
    match ox_wire ps fuel T F k r with
    | Some (1%nat, e) => if Nat.eqb (expr_width e) 1 && inputs_okb T k e then decomp v e else []
    | _ => []
    end
  end.

Lemma oback_wire_sound p ps T seed fixed F k r :
  filter is_comb (processes p) = ps -> TabC ps T -> CombLFP p seed fixed -> FactsHold fixed F ->
  FactsHold fixed (oback_wire ps T (statement_fuel p) F k r).
Proof.
  intros HP HT HL HF. unfold oback_wire.
  destruct (fact_find F (EVar 1%nat r)) as [v|] eqn:Hf; [|intros e z HI; destruct HI].
  destruct (ox_wire ps (statement_fuel p) T F k r) as [[w e]|] eqn:Hs; [|intros e0 z HI; destruct HI].
  destruct w as [|[|w]]; try (intros e0 z HI; destruct HI).
  destruct (Nat.eqb (expr_width e) 1 && inputs_okb T k e) eqn:C; [|intros e0 z HI; destruct HI].
  apply andb_true_iff in C as [W Hi]. apply Nat.eqb_eq in W.
  pose proof (fact_find_sound _ _ _ fixed HF Hf) as Hv. cbn [eval_expr] in Hv.
  pose proof (ox_wire_c p ps T k F seed fixed r 1%nat e HP HT HL HF Hs Hi) as Hw.
  pose proof (eval_normalized fixed e) as En. rewrite W in En. rewrite En in Hw.
  apply (decomp_sound fixed e v). rewrite <- Hw. exact Hv.
Qed.

Definition oback_pos (ps:list Process) (T:list (list nat)) (fuel:nat) (F:Facts) (k:nat) : Facts :=
  match nth_error ps k with
  | None => F
  | Some proc => F ++ flat_map (oback_wire ps T fuel F k) (process_writers proc)
  end.

Lemma oback_pos_sound p ps T seed fixed F k :
  filter is_comb (processes p) = ps -> TabC ps T -> CombLFP p seed fixed -> FactsHold fixed F ->
  FactsHold fixed (oback_pos ps T (statement_fuel p) F k).
Proof.
  intros HP HT HL HF. unfold oback_pos. destruct (nth_error ps k) as [proc|]; [|exact HF].
  intros e z HI. apply in_app_or in HI as [HI|HI]; [apply HF, HI|].
  apply in_flat_map in HI as [r [_ HI]].
  exact (oback_wire_sound p ps T seed fixed F k r HP HT HL HF e z HI).
Qed.

(** scripts: [(false,k)] forward step at k, [(true,k)] backward step at k *)
Fixpoint orun_script (ps:list Process) (T:list (list nat)) (fuel:nat) (F:Facts) (sc:Script) : Facts :=
  match sc with
  | [] => F
  | (b,k)::t => orun_script ps T fuel (if b then oback_pos ps T fuel F k else ox_step ps T fuel F k) t
  end.

Lemma orun_script_sound p ps T seed fixed :
  filter is_comb (processes p) = ps -> TabC ps T -> CombLFP p seed fixed ->
  forall sc F, FactsHold fixed F -> FactsHold fixed (orun_script ps T (statement_fuel p) F sc).
Proof.
  intros HP HT HL. induction sc as [|[b k] t IH]; intros F HF; cbn [orun_script]; [exact HF|].
  apply IH. destruct b.
  - exact (oback_pos_sound p ps T seed fixed F k HP HT HL HF).
  - exact (ox_step_sound p ps T (statement_fuel p) F k seed fixed HP HT eq_refl HF HL).
Qed.
End ExtendedSVBackOverlay.
Print Assumptions ExtendedSVBackOverlay.orun_script_sound.
