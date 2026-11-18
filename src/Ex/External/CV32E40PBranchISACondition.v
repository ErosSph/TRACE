(** Six symbolic branch predicates agree with riscv-coq ExecuteI guards.
    Operands remain universally quantified.  Port freshness/actual decoder
    opcode hypotheses still have to be derived from the branch joint invariant. *)
From Coq Require Import ZArith Bool Lia.
Require Import Lang.ExtendedSV Ex.External.CV32E40PBranchCompareControl
  Ex.External.CV32E40PBranchFullCoreWord Ex.External.CV32E40PISAWordInterpretation
  Ex.External.CV32E40PReq41Instruction Ex.External.CV32E40PAddiAdderResult
  Ex.External.CV32E40PAddiAdderBits Ex.External.CV32E40PAddiIDEXAccept
  Ex.External.CV32E40PAddiOperandCone.
Require Import riscv.Spec.Decode riscv.Utility.Utility riscv.Utility.MkMachineWidth.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth.
Import ExtendedSV CV32E40PBranchCompareControl CV32E40PBranchFullCoreWord
  CV32E40PISAWordInterpretation CV32E40PReq41Instruction CV32E40PAddiAdderResult
  CV32E40PAddiAdderBits CV32E40PAddiIDEXAccept CV32E40PAddiOperandCone.
Local Open Scope Z_scope.
Module CV32E40PBranchISACondition.
Definition branch_alu_opcode (i : Decode.InstructionI) : Z :=
  match i with
  | Decode.Beq _ _ _ => 12 | Decode.Bne _ _ _ => 13
  | Decode.Blt _ _ _ => 0 | Decode.Bge _ _ _ => 10
  | Decode.Bltu _ _ _ => 1 | Decode.Bgeu _ _ _ => 11
  | _ => 0
  end.

Lemma branch_family_alu i : InFamily FamilyBranch i -> BranchALU (branch_alu_opcode i).
Proof.
  intros HI. destruct i; cbn [InFamily family_of] in HI; try discriminate;
    unfold BranchALU; cbn [branch_alu_opcode]; intuition congruence.
Qed.

Lemma branch_word_condition_normalized op a b :
  branch_word_condition op a b = branch_word_condition op (norm 32 a) (norm 32 b).
Proof.
  unfold branch_word_condition. rewrite !norm_twice, !signed_norm. reflexivity.
Qed.

Section Word32.
Context {word : Interface.word 32} {BW : Bitwidth 32} {word_ok : word.ok word}.

(** Exactly the six guards in ExecuteI.v:58--112, before PC target handling. *)
Definition isa_branch_guard (i : Decode.InstructionI) (a b : word) : bool :=
  match i with
  | Decode.Beq _ _ _ => Utility.reg_eqb a b
  | Decode.Bne _ _ _ => negb (Utility.reg_eqb a b)
  | Decode.Blt _ _ _ => Utility.signed_less_than a b
  | Decode.Bge _ _ _ => negb (Utility.signed_less_than a b)
  | Decode.Bltu _ _ _ => Utility.ltu a b
  | Decode.Bgeu _ _ _ => negb (Utility.ltu a b)
  | _ => false
  end.

Theorem branch_condition_is_reference i (a b : word) : InFamily FamilyBranch i ->
  branch_word_condition (branch_alu_opcode i) (word.unsigned a) (word.unsigned b) =
    isa_branch_guard i a b.
Proof.
  intros HI. destruct i; cbn [InFamily family_of] in HI; try discriminate.
  all: cbn [branch_alu_opcode branch_word_condition isa_branch_guard
    Utility.reg_eqb Utility.signed_less_than Utility.ltu MachineWidth_XLEN
    Z.eqb Pos.eqb].
  all: rewrite ?reference_signed_less, ?reference_unsigned_less.
  all: try reflexivity.
  all: rewrite !norm_small by apply word.unsigned_range.
  all: rewrite word.unsigned_eqb; reflexivity.
Qed.

Theorem fullcore_branch_is_reference s i (a b : word) :
  InFamily FamilyBranch i ->
  norm 7 (read_signal (round s) 1303%nat) = branch_alu_opcode i ->
  norm 2 (read_signal (round s) 1307%nat) = 0 ->
  norm 32 (read_signal (round s) 1304%nat) = word.unsigned a ->
  norm 32 (read_signal (round s) 1305%nat) = word.unsigned b ->
  norm 1 (read_signal (round s) 1315%nat) = boolz (isa_branch_guard i a b).
Proof.
  intros HI HO HV HA HB.
  rewrite fullcore_branch_condition with (op:=branch_alu_opcode i)
    by (try assumption; apply branch_family_alu; exact HI).
  rewrite branch_word_condition_normalized, HA, HB.
  now rewrite branch_condition_is_reference by exact HI.
Qed.
End Word32.
Print Assumptions branch_condition_is_reference.
Print Assumptions fullcore_branch_is_reference.
End CV32E40PBranchISACondition.
