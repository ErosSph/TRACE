(** Connect a token's original fetch/run1 to the exact ExecuteI instruction.
    No CPU invariant or replacement ISA evaluator is used. *)
From Coq Require Import ZArith Lia Bool.
Require Import Ex.RvCore.FormalSpec Ex.RvCore.Machine
 Ex.External.CPUISAExecutionEffects Ex.External.CPUOriginalISAReference
 coqutil.Word.Interface coqutil.Map.Interface coqutil.Word.Bitwidth coqutil.Byte
 riscv.Utility.Monads riscv.Spec.ExecuteI.
Import CPUISAExecutionEffects CPUOriginalISAReference.
Module CPUISAInstructionExecution.
Local Open Scope Z_scope.
Section ISA.
Context {word:Interface.word 32}{BW:Bitwidth 32}
 {Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}{registers_ok:map.ok Registers}.

Lemma read_address_bounds (before after:FormalSpec.State) address value:
 Machine.getRegister address before=(Some value,after) ->0<=address<32.
Proof.
 unfold Machine.getRegister;cbn[IsRiscvProgram].
 destruct(Z.eq_dec address 0)as[HZ|HN];[subst address;intros;lia|].
 destruct((0<?address)&&(address<?32))%bool eqn:HB;[|discriminate].
 intros _;apply andb_true_iff in HB;destruct HB as[HL HH].
 apply Z.ltb_lt in HL;apply Z.ltb_lt in HH;lia.
Qed.

Lemma alignment_frame (before after:FormalSpec.State) address value:
 Machine.assert_aligned address before=(Some value,after) ->after=before.
Proof.
 unfold Machine.assert_aligned.
 match goal with |- context[if ?b then _ else _] => destruct b end;
 intro H;inversion H;reflexivity.
Qed.

Lemma fetch_frame (before after:FormalSpec.State) bytes:
 Machine.loadWord Machine.Fetch(getPc before)before=(Some bytes,after) ->after=before.
Proof.
 unfold Machine.loadWord;cbn[IsRiscvProgram];unfold Machine.loadN.
 intro H;apply bind_success in H;destruct H as[[] [middle [HA H]]].
 pose proof(alignment_frame before middle (getPc before) tt HA);subst middle.
 cbn[Bind Return OState_Monad OStateOperations.get]in H.
 unfold Machine.fail_if_None in H.
 destruct(Memory.load_bytes 4(getInstMem before)(getPc before));inversion H;reflexivity.
Qed.

Theorem token_execute {Token:Type}(token_pc token_word:Token->Z)
 token (before after:FormalSpec.State) i:
 instruction_effect token_pc token_word token before=Some after ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction i ->
 exists middle,ExecuteI.execute i before=(Some tt,middle) /\
 Machine.endCycleNormal middle=(Some tt,after).
Proof.
 intros HS HD.
 destruct(instruction_effect_sound token_pc token_word token before after HS)
   as[_ [[original_bytes [HF HW]] HR]].
 unfold FormalSpec.run1 in HR.
 apply bind_success in HR;destruct HR as[pc [s1 [HP HR]]].
 assert(HE:s1=before)by exact(original_pc_read_preserves before s1 pc HP).
 subst s1;assert(HPC:pc=getPc before)by(inversion HP;reflexivity);subst pc.
 apply bind_success in HR;destruct HR as[bytes [s2 [HL HR]]].
 pose proof(fetch_frame before s2 bytes HL);subst s2.
 change(fst(Machine.loadWord Machine.Fetch(getPc before)before)=Some original_bytes)in HF.
 assert(HB:bytes=original_bytes).
 { pose proof(f_equal (@fst _ _) HL)as Hfirst.
   change(fst(Machine.loadWord Machine.Fetch(getPc before)before)=Some bytes)in Hfirst.
   assert(Some bytes=Some original_bytes)by exact(eq_trans(eq_sym Hfirst)HF).
   congruence. }
 subst original_bytes.
 assert(HDE:Decode.decode Decode.RV32I(LittleEndian.combine 4 bytes)=Decode.IInstruction i).
 { exact(eq_trans(f_equal(Decode.decode Decode.RV32I)(eq_sym HW))HD). }
 assert(HRI:Bind(Execute.execute(Decode.IInstruction i))
   (fun _=>Machine.endCycleNormal)before=(Some tt,after)).
 { exact(eq_trans(eq_sym(f_equal(fun decoded=>
     Bind(Execute.execute decoded)(fun _=>Machine.endCycleNormal)before)HDE))HR). }
 apply bind_success in HRI;destruct HRI as[[] [middle [HE HEND]]].
 exists middle;split;[exact HE|exact HEND].
Qed.
End ISA.
End CPUISAInstructionExecution.
Print Assumptions CPUISAInstructionExecution.alignment_frame.
Print Assumptions CPUISAInstructionExecution.read_address_bounds.
Print Assumptions CPUISAInstructionExecution.fetch_frame.
Print Assumptions CPUISAInstructionExecution.token_execute.
