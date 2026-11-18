(** Finite physical retirement observations, without an assumed post-effect.
    This is a reset-reachable regression, not the unbounded induction theorem. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV.
Require Import Ex.External.CV32E40PReq39Trace.
Require Import Ex.External.CV32E40PAddiReachability.
Import ListNotations ExtendedSV CV32E40PReq39Trace CV32E40PAddiReachability.
Local Open Scope Z_scope.

Module CV32E40PAddiCommitTrace.
  Definition image : InstructionImage := [1048723; 1081491].
  Definition Observation := (option IssueToken * bool * option IssueToken * Z * Z * Z * Z)%type.
  Definition empty_observation : Observation := (None, false, None, 0, 0, 0, 0).
  Definition token pc instruction := {| token_pc := pc; token_instruction := instruction |}.
  Definition observation (s : RetirementState) :=
    let driven := environment_state_image image (physical_state s) in
    (issue_at driven, alu_completes driven, pending_token s,
      Z.land (Z.shiftr (read_signal (trace_rtl (physical_state s)) 902%nat) 32)
        4294967295,
      trace_memory_word (physical_state s), read_signal driven 21%nat,
      architectural_cursor s).
  Fixpoint observations n s :=
    match n with
    | O => []
    | S k => observation s :: observations k (advance_retirement image s)
    end.
  Definition expected : list Observation :=
    [empty_observation; empty_observation; empty_observation; empty_observation;
     (Some (token 0 1048723), false, None, 0, 0, 0, 0);
     (Some (token 4 1081491), true, Some (token 0 1048723), 0, 0, 0, 0);
     (Some (token 8 19), true, Some (token 4 1081491), 1, 0, 0, 4);
     (Some (token 12 19), true, Some (token 8 19), 2, 0, 0, 8);
     (Some (token 16 19), true, Some (token 12 19), 2, 0, 0, 12)].
  Theorem real_reset_execution_observations : observations 9 reset_retirement = expected.
  Proof. vm_compute. reflexivity. Qed.
End CV32E40PAddiCommitTrace.
