(** Case reflection for the per-phase control/datapath analysis (template route, additive; 2026-11-03).
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.
    One boolean checker [check_case] and ONE soundness theorem [cases_sound]: a clause proof states its control cases as DATA
    ([CaseSpec]: literal facts about the driven state, the replay list [ks] of comb positions, the derived constants [outs] and the
    symbolic wire expressions [wires]) and discharges ALL of them with a single [vm_compute] of [forallb (check_case ..) cases].
    No per-case theorem, replay or audit is generated. Facts used for the wires are the full derived fact list of the case. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVSymExec Lang.ExtendedSVFactChain Lang.ExtendedSVSymExecSym Lang.ExtendedSVSymExecPhase.
Import ListNotations ExtendedSV ExtendedSVSymExec ExtendedSVFactChain ExtendedSVSymExecSym ExtendedSVSymExecPhase.
Local Open Scope Z_scope.
Module ExtendedSVCaseReflect.

(** a wire request: (position k of the comb process writing r, root r, width w, expected expression e) *)
Definition WireReq := (nat * signal * nat * Expr)%type.
Record CaseSpec := mkCase {
  cs_facts : Facts;                       (* literal facts about the driven state *)
  cs_ks : list nat;                       (* replay list of comb positions (topological order) *)
  cs_outs : list ((signal*nat)*Z);        (* derived constants, to be re-derived *)
  cs_wires : list WireReq }.              (* symbolic wire expressions, to be re-derived *)

Definition derived (ps:list Process) (T:list (list nat)) (fuel:nat) (c:CaseSpec) : Facts :=
  sx_pass ps T fuel (cs_facts c) (cs_ks c).

Definition wire_ok (ps:list Process) (T:list (list nat)) (fuel:nat) (F:Facts) (x:WireReq) : bool :=
  match x with (k, r, w, e) =>
    match sx_wire ps fuel T F k r with
    | Some (w', e') => Nat.eqb w w' && (if expr_eq_dec e e' then true else false) && inputs_okb T k e'
    | None => false
    end
  end.

Definition check_case (ps:list Process) (T:list (list nat)) (fuel:nat) (c:CaseSpec) : bool :=
  let F := derived ps T fuel c in
  outs_in_facts F (cs_outs c) && forallb (wire_ok ps T fuel F) (cs_wires c).

Definition check_cases ps T fuel (cases:list CaseSpec) : bool := forallb (check_case ps T fuel) cases.

Lemma wire_ok_sound p ps T seed fixed F x :
  filter is_comb (processes p) = ps -> TabC ps T -> CombLFP p seed fixed -> FactsHold fixed F ->
  wire_ok ps T (statement_fuel p) F x = true ->
  norm (snd (fst x)) (read_signal fixed (snd (fst (fst x)))) = norm (snd (fst x)) (eval_expr fixed (snd x)).
Proof.
  intros HP HT HL HF H. destruct x as [[[k r] w] e]. cbn [snd fst] in *. unfold wire_ok in H.
  destruct (sx_wire ps (statement_fuel p) T F k r) as [[w' e']|] eqn:Hs; [|discriminate].
  apply andb_true_iff in H as [H Hi]. apply andb_true_iff in H as [Hw Hx].
  apply Nat.eqb_eq in Hw. subst w'.
  destruct (expr_eq_dec e e') as [->|]; [|discriminate].
  exact (sym_wire_c p ps T k F seed fixed r w e' HP HT HL HF Hs Hi).
Qed.

(** soundness of one checked case: the facts hold at a comb fixed point => the derived constants and wire values hold *)
Theorem case_sound p ps T c seed fixed :
  filter is_comb (processes p) = ps -> TabC ps T -> CombLFP p seed fixed -> FactsHold fixed (cs_facts c) ->
  check_case ps T (statement_fuel p) c = true ->
  FactsHold fixed (derived ps T (statement_fuel p) c) /\ DecOut fixed (cs_outs c) /\
  (forall x, In x (cs_wires c) -> norm (snd (fst x)) (read_signal fixed (snd (fst (fst x)))) = norm (snd (fst x)) (eval_expr fixed (snd x))).
Proof.
  intros HP HT HL HF H. unfold check_case in H. apply andb_true_iff in H as [Ho Hw].
  pose proof (sx_pass_sound p ps T (statement_fuel p) seed fixed HP HT eq_refl HL (cs_ks c) (cs_facts c) HF) as HD.
  fold (derived ps T (statement_fuel p) c) in HD, Ho, Hw.
  refine (conj HD (conj _ _)).
  - exact (sx_pass_outs p ps T (cs_ks c) (cs_facts c) (cs_outs c) seed fixed HP HT HF HL Ho).
  - intros x Hx. rewrite forallb_forall in Hw. exact (wire_ok_sound p ps T seed fixed _ x HP HT HL HD (Hw x Hx)).
Qed.

(** the table form: one vm_compute for all cases *)
Theorem cases_sound p ps T cases seed fixed c :
  filter is_comb (processes p) = ps -> tab_okb ps T = true -> CombLFP p seed fixed ->
  check_cases ps T (statement_fuel p) cases = true -> In c cases -> FactsHold fixed (cs_facts c) ->
  FactsHold fixed (derived ps T (statement_fuel p) c) /\ DecOut fixed (cs_outs c) /\
  (forall x, In x (cs_wires c) -> norm (snd (fst x)) (read_signal fixed (snd (fst (fst x)))) = norm (snd (fst x)) (eval_expr fixed (snd x))).
Proof.
  intros HP HT HL Hc Hin HF. unfold check_cases in Hc. rewrite forallb_forall in Hc.
  exact (case_sound p ps T c seed fixed HP (tab_okb_sound ps T HT) HL HF (Hc c Hin)).
Qed.
End ExtendedSVCaseReflect.
Print Assumptions ExtendedSVCaseReflect.case_sound.
Print Assumptions ExtendedSVCaseReflect.cases_sound.
