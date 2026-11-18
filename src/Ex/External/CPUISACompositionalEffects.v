(** Syntax-directed register effects of successful ORIGINAL ISA actions.
    This does not assert successful execution or replace memory/PC semantics. *)
From Coq Require Import ZArith List.
Require Import Ex.External.CPUISAExecutionEffects Ex.External.CPUISARegisterUpdate
 Ex.External.CPUISAInstructionExecution Ex.External.CPUISAOwnedEffects
 Ex.External.CPUOriginalISAReference Ex.External.CPUGeneratedJointTemplate
 Ex.External.CPURegisterEffectRelation Ex.RvCore.FormalSpec Ex.RvCore.Machine
 coqutil.Map.Interface coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Byte
 riscv.Utility.Monads riscv.Utility.Utility riscv.Spec.ExecuteI.
Import ListNotations OStateOperations CPUISAExecutionEffects CPUISARegisterUpdate CPURegisterEffectRelation.
Import CPUISAInstructionExecution CPUISAOwnedEffects CPUOriginalISAReference CPUGeneratedJointTemplate.
Module CPUISACompositionalEffects.
Section Rules.
Context {word:Interface.word 32}{BW:Bitwidth 32}
 {Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}{registers_ok:map.ok Registers}.

Definition Projects {X:Type}(action:OState FormalSpec.State X):Prop :=
 forall before value after, action before=(Some value,after) ->
 exists operations,ISAProjectedRegisterEffects before after operations.

Lemma frame_projects {X} (action:OState FormalSpec.State X):
 (forall before value after,action before=(Some value,after) ->getRegs after=getRegs before) ->
 Projects action.
Proof. intros HF b v a H;exists [];apply unchanged_registers;exact(HF b v a H). Qed.

Lemma bind_projects {X Y}(first:OState FormalSpec.State X)(next:X->OState FormalSpec.State Y):
 Projects first ->(forall x,Projects(next x))->Projects(Bind first next).
Proof.
 intros HF HN b v a H;destruct(bind_success first next b v a H)as[x [m [HX HY]]].
 destruct(HF b x m HX)as[ops1 H1];destruct(HN x m v a HY)as[ops2 H2].
 exists(ops1++ops2);eapply isa_projected_effects_append;eassumption.
Qed.
Lemma return_projects {X}(x:X):Projects(Return x).
Proof. apply frame_projects;intros b v a H;inversion H;reflexivity. Qed.
Lemma fail_projects {X}:Projects(@fail_hard FormalSpec.State X).
Proof. intros b v a H;discriminate. Qed.
Lemma get_projects:Projects(@OStateOperations.get FormalSpec.State).
Proof. apply frame_projects;intros b v a H;inversion H;reflexivity. Qed.
Lemma update_projects f:
 (forall s,getRegs(f s)=getRegs s)->Projects(update f).
Proof. intro HF;apply frame_projects;intros b v a H;inversion H;subst;apply HF. Qed.
Lemma read_projects rs:Projects(Machine.getRegister rs).
Proof. apply frame_projects;intros b v a H;now rewrite(original_read_preserves b a rs v H). Qed.
Lemma pc_projects:Projects Machine.getPC.
Proof. apply frame_projects;intros b v a H;now rewrite(original_pc_read_preserves b a v H). Qed.
Lemma write_projects rd value:Projects(Machine.setRegister rd value).
Proof. intros b [] a H;exists(register_operations rd value);now apply original_set_register. Qed.
Lemma setpc_projects value:Projects(Machine.setPC value).
Proof. apply update_projects;intros [];reflexivity. Qed.
Lemma option_projects {X}(o:option X):Projects(fail_if_None o).
Proof. destruct o;[apply return_projects|apply fail_projects]. Qed.
Lemma aligned_projects address:Projects(assert_aligned address).
Proof. unfold assert_aligned;destruct(_ : bool);[apply fail_projects|apply return_projects]. Qed.
Lemma load_projects n kind address:Projects(loadN n kind address).
Proof.
 unfold loadN;apply bind_projects;[apply aligned_projects|intros []].
 apply bind_projects;[apply get_projects|intro m].
 apply bind_projects;[destruct kind;first[apply return_projects|apply fail_projects]|].
 intro memory;apply option_projects.
Qed.
Lemma store_projects n kind address value:Projects(storeN n kind address value).
Proof.
 unfold storeN;apply bind_projects;[apply aligned_projects|intros []].
 apply bind_projects;[apply get_projects|intro m].
 apply bind_projects;[destruct kind;first[apply return_projects|apply fail_projects]|intro memory].
 apply bind_projects;[apply option_projects|intro memory'].
 apply update_projects;intros [];reflexivity.
Qed.
Lemma translate_projects access alignment address:
 Projects(Machine.translate access alignment address).
Proof. apply return_projects. Qed.
Lemma bind_failed_projects {X Y}(next:X->OState FormalSpec.State Y):
 Projects(Bind (@fail_hard FormalSpec.State X) next).
Proof. intros b v a H;discriminate. Qed.
Lemma exception_projects {X} (interrupt code info:word):
 Projects(Machine.raiseExceptionWithInfo (A:=X) interrupt code info).
Proof. unfold Machine.raiseExceptionWithInfo;apply bind_projects;[apply pc_projects|intro x;apply bind_failed_projects]. Qed.
Lemma when_projects b (action:OState FormalSpec.State unit):
 Projects action -> Projects(when b action).
Proof. intro H;destruct b;[exact H|apply return_projects]. Qed.

Ltac solve_effects :=
 first[apply return_projects|apply read_projects|apply pc_projects|
       apply write_projects|apply setpc_projects|apply translate_projects|
       apply load_projects|apply store_projects|apply exception_projects|apply fail_projects|
       (apply when_projects;solve_effects)|
       (apply bind_projects;[solve_effects|intro;solve_effects])|
       match goal with |-Projects(if ?b then _ else _) => destruct b;solve_effects end].

Theorem execute_register_effects i:Projects(ExecuteI.execute i).
Proof. destruct i;cbn[ExecuteI.execute];solve_effects. Qed.

Theorem token_register_effect {Token:Type}(token_pc token_word:Token->Z)
 token before after i:
 instruction_effect token_pc token_word token before=Some after ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction i ->
 exists operations,ISAProjectedRegisterEffects before after operations.
Proof.
 intros HS HD;destruct(token_execute token_pc token_word token before after i HS HD)
 as[middle [HE HEND]].
 destruct(execute_register_effects i before tt middle HE)as[operations HO].
 exists operations;intros address HA.
 unfold ISAView;rewrite(end_cycle_register_frame middle after HEND).
 exact(HO address HA).
Qed.

Theorem certify_original_chain {Token:Type}(token_pc token_word:Token->Z)
 initial tokens final:
 EffectChain(instruction_effect token_pc token_word)initial tokens final ->
 Forall(fun token=>exists i,Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction i)tokens ->
 exists batches,map fst batches=tokens /\ CertifiedBatches token_pc token_word initial batches final.
Proof.
 intro HC;induction HC;intro HD.
 - exists [];split;[reflexivity|constructor].
 - inversion HD as[|token' rest' HI HR];subst.
   destruct HI as[i HI].
   match goal with HS:instruction_effect _ _ _ _=Some _ |- _ =>
     destruct(token_register_effect _ _ _ _ _ _ HS HI)as[operations HO]
   end.
   destruct(IHHC HR)as[batches [HM HB]].
   exists((t,operations)::batches);split;[cbn;rewrite HM;reflexivity|econstructor;eassumption].
Qed.
End Rules.
End CPUISACompositionalEffects.
Print Assumptions CPUISACompositionalEffects.execute_register_effects.
Print Assumptions CPUISACompositionalEffects.token_register_effect.
Print Assumptions CPUISACompositionalEffects.certify_original_chain.
