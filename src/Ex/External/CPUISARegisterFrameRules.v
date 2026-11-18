(** Compositional rules for deriving the register frame from original ISA syntax.
    The target set is generated from setRegister arguments, not CPU proofs. *)
From Coq Require Import ZArith List.
Require Import Ex.External.CPUISACompositionalEffects Ex.External.CPUISARegisterUpdate
 Ex.External.CPUISAExecutionEffects Ex.External.CPURegisterEffectRelation
 Ex.RvCore.FormalSpec Ex.RvCore.Machine Lang.ExtendedSVRegisterBank
 coqutil.Map.Interface coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Byte
 riscv.Utility.Monads riscv.Utility.Utility.
Import ListNotations OStateOperations CPUISARegisterUpdate CPUISAExecutionEffects
 CPURegisterEffectRelation ExtendedSVRegisterBank.
Local Open Scope Z_scope.
Module CPUISARegisterFrameRules.
Section Rules.
Context {word:Interface.word 32}{BW:Bitwidth 32}
 {Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}{registers_ok:map.ok Registers}.

Definition WritesOnly {X:Type}(destinations:list Z)(action:OState FormalSpec.State X):Prop :=
 forall before value after,action before=(Some value,after) ->
 forall i,0<=i<32 ->~In i destinations ->ISAView after i=ISAView before i.

Lemma unchanged_only {X} ds (action:OState FormalSpec.State X):
 (forall b v a,action b=(Some v,a)->getRegs a=getRegs b)->WritesOnly ds action.
Proof. intros HF b v a H i HI HN;unfold ISAView;now rewrite(HF b v a H). Qed.
Lemma bind_only {X Y} ds (first:OState FormalSpec.State X)(next:X->OState FormalSpec.State Y):
 WritesOnly ds first ->(forall x,WritesOnly ds(next x))->WritesOnly ds(Bind first next).
Proof.
 intros HF HN b v a H i HI HD.
 destruct(bind_success first next b v a H)as[x [m [HX HY]]].
 rewrite(HN x m v a HY i HI HD);exact(HF b x m HX i HI HD).
Qed.
Lemma return_only {X} ds (x:X):WritesOnly ds(Return x).
Proof. apply unchanged_only;intros b v a H;inversion H;reflexivity. Qed.
Lemma fail_only {X} ds:WritesOnly ds(@fail_hard FormalSpec.State X).
Proof. intros b v a H;discriminate. Qed.
Lemma get_only ds:WritesOnly ds(@OStateOperations.get FormalSpec.State).
Proof. apply unchanged_only;intros b v a H;inversion H;reflexivity. Qed.
Lemma update_only ds f:(forall s,getRegs(f s)=getRegs s)->WritesOnly ds(update f).
Proof. intro HF;apply unchanged_only;intros b v a H;inversion H;subst;apply HF. Qed.
Lemma read_only ds rs:WritesOnly ds(Machine.getRegister rs).
Proof. apply unchanged_only;intros b v a H;now rewrite(original_read_preserves b a rs v H). Qed.
Lemma pc_only ds:WritesOnly ds Machine.getPC.
Proof. apply unchanged_only;intros b v a H;now rewrite(original_pc_read_preserves b a v H). Qed.
Lemma write_only ds rd value:In rd ds ->WritesOnly ds(Machine.setRegister rd value).
Proof.
 intros HD b [] a H i HI HN.
 assert(Hdiff:i<>rd)by(intro HE;subst i;contradiction).
 rewrite(original_set_register b a rd value H i HI).
 unfold register_operations,project_x0,operation_effects32.
 destruct(rd=?0);cbn[operation_effects operation_effect abstract_write];
 destruct(i=?0)eqn:HZ.
 - apply Z.eqb_eq in HZ;subst i;reflexivity.
 - reflexivity.
 - apply Z.eqb_eq in HZ;subst i;reflexivity.
 - unfold abstract_write;assert(HF:(i=?rd)=false)by(now apply Z.eqb_neq).
   now rewrite HF.
Qed.
Lemma setpc_only ds value:WritesOnly ds(Machine.setPC value).
Proof. apply update_only;intros [];reflexivity. Qed.
Lemma option_only {X} ds (o:option X):WritesOnly ds(fail_if_None o).
Proof. destruct o;[apply return_only|apply fail_only]. Qed.
Lemma aligned_only ds address:WritesOnly ds(assert_aligned address).
Proof. unfold assert_aligned;destruct(_ : bool);[apply fail_only|apply return_only]. Qed.
Lemma load_only ds n kind address:WritesOnly ds(loadN n kind address).
Proof.
 unfold loadN;apply bind_only;[apply aligned_only|intros []].
 apply bind_only;[apply get_only|intro m].
 apply bind_only;[destruct kind;first[apply return_only|apply fail_only]|].
 intro memory;apply option_only.
Qed.
Lemma store_only ds n kind address value:WritesOnly ds(storeN n kind address value).
Proof.
 unfold storeN;apply bind_only;[apply aligned_only|intros []].
 apply bind_only;[apply get_only|intro m].
 apply bind_only;[destruct kind;first[apply return_only|apply fail_only]|intro memory].
 apply bind_only;[apply option_only|intro memory'].
 apply update_only;intros [];reflexivity.
Qed.
Lemma translate_only ds access alignment address:WritesOnly ds(Machine.translate access alignment address).
Proof. apply return_only. Qed.
Lemma bind_failed_only {X Y} ds (next:X->OState FormalSpec.State Y):
 WritesOnly ds(Bind(@fail_hard FormalSpec.State X)next).
Proof. intros b v a H;discriminate. Qed.
Lemma exception_only {X} ds (interrupt code info:word):
 WritesOnly ds(Machine.raiseExceptionWithInfo(A:=X)interrupt code info).
Proof. unfold Machine.raiseExceptionWithInfo;apply bind_only;[apply pc_only|intro x;apply bind_failed_only]. Qed.
Lemma when_only ds b action:WritesOnly ds action ->WritesOnly ds(when b action).
Proof. intro H;destruct b;[exact H|apply return_only]. Qed.

End Rules.

Ltac solve_frame :=
 first[apply return_only|apply read_only|apply pc_only|
       (apply write_only;cbn;auto)|apply setpc_only|apply translate_only|
       apply load_only|apply store_only|apply exception_only|apply fail_only|
       (apply when_only;solve_frame)|
       (apply bind_only;[solve_frame|intro;solve_frame])|
       match goal with |-WritesOnly _ (if ?b then _ else _) =>destruct b;solve_frame end].
End CPUISARegisterFrameRules.
Print Assumptions CPUISARegisterFrameRules.write_only.
Print Assumptions CPUISARegisterFrameRules.bind_only.
