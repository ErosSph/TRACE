(** Physical 32-bit source captures derived from real phase semantics.
    None means no supported non-self copy, NOT an empty architectural slot. *)
From Coq Require Import ZArith Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVInstructionOrigin
 Lang.ExtendedSVWordInvariant Ex.External.CPUReadyOperand
 Ex.External.CPUReadySelectionRequirements.
Import ExtendedSV ExtendedSVInstructionOrigin ExtendedSVWordInvariant
 CPUReadyOperand CPUReadySelectionRequirements.
Module CPUActualSourceCapture.
Local Open Scope Z_scope.
Definition capture_source p proc destination expression ev pre :=
 if process_matches_states pre(phase_driven_state p ev pre)proc then
 match copy_source(phase_driven_state p ev pre)expression with
 |Some source=>if Nat.eqb source destination then None else Some source
 |None=>None
 end else None.

Lemma capture_selected p proc destination expression ev pre source:
 capture_source p proc destination expression ev pre=Some source ->
 process_matches_states pre(phase_driven_state p ev pre)proc=true /\
 copy_source(phase_driven_state p ev pre)expression=Some source /\ source<>destination.
Proof.
 unfold capture_source.
 destruct(process_matches_states pre(phase_driven_state p ev pre)proc)eqn:HF;[|discriminate].
 destruct(copy_source(phase_driven_state p ev pre)expression)as[s|]eqn:HS;[|discriminate].
 destruct(Nat.eqb s destination)eqn:HD;[discriminate|].
 intro H;inversion H;subst s;split;[reflexivity|];split;[reflexivity|].
 now apply Nat.eqb_neq.
Qed.

Definition captured_source_R p proc destination expression ev pre physical address slots :=
 forall source,capture_source p proc destination expression ev pre=Some source ->
 selection_requirements 32(EVar 32 source)(phase_driven_state p ev pre)physical address slots.

Theorem actual_capture_ready p proc destination expression ev pre physical address slots source:
 norm 32(read_signal(PhaseSemantics p ev pre)destination)=
 (if process_matches_states pre(phase_driven_state p ev pre)proc
 then norm 32(eval_expr(phase_driven_state p ev pre)expression)
 else norm 32(read_signal pre destination)) ->
 captured_source_R p proc destination expression ev pre physical address slots ->
 capture_source p proc destination expression ev pre=Some source ->
 resolve 0 physical address slots=Some(norm 32(read_signal(PhaseSemantics p ev pre)destination)).
Proof.
 intros HE HR HC.
 destruct(capture_selected p proc destination expression ev pre source HC)as[HF [HS HN]].
 specialize(HR source HC);apply selection_exact in HR.
 cbn[eval_expr]in HR;rewrite norm_idempotent in HR.
 rewrite HE,HF,(copy_source_sound expression(phase_driven_state p ev pre)source HS),norm_idempotent.
 exact HR.
Qed.

Theorem unready_blocks_actual_capture p proc destination expression ev pre physical address slots source:
 address<>0%Z ->lookup address slots=Some None ->
 captured_source_R p proc destination expression ev pre physical address slots ->
 capture_source p proc destination expression ev pre<>Some source.
Proof.
 intros HZ HL HR HC;specialize(HR source HC);apply selection_exact in HR.
 unfold resolve in HR.
 assert(HB:Z.eqb address 0=false)by(now apply Z.eqb_neq).
 rewrite HB,HL in HR;discriminate.
Qed.
End CPUActualSourceCapture.
Print Assumptions CPUActualSourceCapture.actual_capture_ready.
Print Assumptions CPUActualSourceCapture.unready_blocks_actual_capture.
