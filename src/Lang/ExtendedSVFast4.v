(** Fast-store chain with the 1-bit OR short-circuit (template route, additive; 2026-11-04).
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.
    [fstep4] = [ExtendedSVSymExecFast.fstep] with [ExtendedSVEval4.ox_new_facts4]; backward steps are [ExtendedSVFastCond.fback2];
    [frun4], [check_shared4], [shared4_sound] mirror the Fast/FastCond versions. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVSymExec Lang.ExtendedSVFactChain Lang.ExtendedSVSymExecSym Lang.ExtendedSVSymExecOverlay
 Lang.ExtendedSVBackward Lang.ExtendedSVEval3 Lang.ExtendedSVEval4 Lang.ExtendedSVSymExecFast Lang.ExtendedSVFastCond.
Import ListNotations ExtendedSV ExtendedSVSymExec ExtendedSVFactChain ExtendedSVSymExecSym ExtendedSVSymExecOverlay ExtendedSVBackward
 ExtendedSVEval3 ExtendedSVEval4 ExtendedSVSymExecFast ExtendedSVFastCond.
Local Open Scope Z_scope.
Module ExtendedSVFast4.

Definition fstep4 (ps:list Process) (T:list (list nat)) (fuel:nat) (fs:FS) (k:nat) : FS :=
  match nth_error ps k with
  | None => fs
  | Some proc =>
    let F0 := loc_facts T fs k (proc_roots proc) in
    match oxexec F0 fuel (nbfix (process_body proc)) [] with
    | None => fs
    | Some ov => add_facts fs (ox_new_facts4 F0 T k ov)
    end
  end.

Lemma fstep4_sound p ps T fs k seed fixed :
  filter is_comb (processes p) = ps -> TabC ps T -> CombLFP p seed fixed -> SHold fixed fs ->
  SHold fixed (fstep4 ps T (statement_fuel p) fs k).
Proof.
  intros HP HT HL HS. unfold fstep4. destruct (nth_error ps k) as [proc|] eqn:HN; [|exact HS].
  destruct (oxexec (loc_facts T fs k (proc_roots proc)) (statement_fuel p) (nbfix (process_body proc)) []) as [ov|] eqn:Hx; [|exact HS].
  apply add_facts_hold; [exact HS|].
  exact (ox_new_facts4_sound p ps T k proc _ ov seed fixed HP HT HN (loc_okb T fs k _) (loc_hold fixed T fs k _ HS) HL Hx).
Qed.

Definition frun4 (ps:list Process) (T:list (list nat)) (fuel:nat) (fs:FS) (sc:Script) : FS :=
  fold_left (fun (fs:FS) (st:bool*nat) => if fst st then fback2 ps T fuel fs (snd st) else fstep4 ps T fuel fs (snd st)) sc fs.

Lemma frun4_sound p ps T seed fixed :
  filter is_comb (processes p) = ps -> TabC ps T -> CombLFP p seed fixed ->
  forall sc fs, SHold fixed fs -> SHold fixed (frun4 ps T (statement_fuel p) fs sc).
Proof.
  intros HP HT HL. induction sc as [|[b k] t IH]; intros fs HS; cbn [frun4 fold_left]; [exact HS|].
  apply IH. destruct b; cbn [fst snd].
  - exact (fback2_sound p ps T fs k seed fixed HP HT HL HS).
  - exact (fstep4_sound p ps T fs k seed fixed HP HT HL HS).
Qed.

Definition sh_store4 ps T fuel (sh:Shared) : FS := frun4 ps T fuel (add_facts fs_empty (sh_facts sh)) (sh_script sh).
Definition cs_store4 ps T fuel (s0:FS) (c:CaseF) : FS := frun4 ps T fuel (add_facts s0 (cf_facts c)) (cf_script c).
Definition check_shared4 ps T fuel (sh:Shared) (cs:list CaseF) : bool :=
  let s0 := sh_store4 ps T fuel sh in
  forallb (fun c => let fs := cs_store4 ps T fuel s0 c in outs_ok fs (cf_outs c) && exprs_ok fs (cf_exprs c)) cs.

Theorem shared4_sound p ps T sh cases seed fixed c :
  filter is_comb (processes p) = ps -> tab_okb ps T = true -> CombLFP p seed fixed ->
  check_shared4 ps T (statement_fuel p) sh cases = true -> In c cases -> FactsHold fixed (sh_facts sh) -> FactsHold fixed (cf_facts c) ->
  SHold fixed (cs_store4 ps T (statement_fuel p) (sh_store4 ps T (statement_fuel p) sh) c) /\ DecOut fixed (cf_outs c) /\ FactsHold fixed (cf_exprs c).
Proof.
  intros HP HT HL Hc Hin Hsh HF. unfold check_shared4 in Hc. fold (sh_store4 ps T (statement_fuel p) sh) in Hc.
  rewrite forallb_forall in Hc. specialize (Hc c Hin). apply andb_true_iff in Hc as [H1 H2].
  pose proof (frun4_sound p ps T seed fixed HP (tab_okb_sound ps T HT) HL (sh_script sh) _ (shold_init fixed _ Hsh)) as H0.
  fold (sh_store4 ps T (statement_fuel p) sh) in H0.
  pose proof (frun4_sound p ps T seed fixed HP (tab_okb_sound ps T HT) HL (cf_script c) _ (add_facts_hold fixed _ _ H0 HF)) as HS.
  fold (cs_store4 ps T (statement_fuel p) (sh_store4 ps T (statement_fuel p) sh) c) in HS, H1, H2.
  exact (conj HS (conj (outs_ok_sound fixed _ _ HS H1) (exprs_ok_sound fixed _ _ HS H2))).
Qed.
End ExtendedSVFast4.
Print Assumptions ExtendedSVFast4.shared4_sound.
