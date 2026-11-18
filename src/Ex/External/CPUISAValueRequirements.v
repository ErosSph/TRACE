(** Bind generated RTL value conditions to reads of the original ISA.
    Hardware token identity, prefix validity and selection remain obligations;
    none is inferred merely from structural RF reachability. *)
From Coq Require Import ZArith List.
Require Import Lang.ExtendedSV Lang.ExtendedSVRegisterBank
 Lang.ExtendedSVValueRequirements
 Ex.External.CPUISAOperandValue Ex.External.CPUISAOwnedEffects
 Ex.External.CPUOwnedOperandReference Ex.External.CPURegisterEffectRelation
 Ex.RvCore.FormalSpec Ex.RvCore.Machine
 coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth
 coqutil.Map.Interface coqutil.Byte.
Import ExtendedSV ExtendedSVRegisterBank ExtendedSVValueRequirements
 CPUISAOperandValue CPUISAOwnedEffects CPUOwnedOperandReference
 CPURegisterEffectRelation.
Local Open Scope Z_scope.
Module CPUISAValueRequirements.

Definition selected_value {Token:Type}
 (physical:Z->Z)(batches:list(Token*list BankOperation))(address:Z):Z :=
 if address=?0 then 0 else
 match latest_owner 32 batches address with
 | Some(WriteOf _ _ value)=>value
 | None=>physical address
 end.

Definition source_requirements {Token:Type} width expression fixed
 (physical:Z->Z)(batches:list(Token*list BankOperation)) address : Prop :=
 requirements width expression fixed(selected_value physical batches address).

Section OriginalRead.
Context {word:Interface.word 32}{BW:Bitwidth 32}
 {Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}{Token:Type}.

Theorem source_requirements_exact (token_pc token_word:Token->Z)
 width root expression fixed initial batches before after address value physical:
 CertifiedBatches token_pc token_word initial batches before ->
 RegisterRelated physical initial -> 0<=address<32 ->
 Machine.getRegister address before=(Some value,after) ->
 norm width(read_signal fixed root)=norm width(eval_expr fixed expression) ->
 (source_requirements width expression fixed physical batches address <->
  norm width(read_signal fixed root)=word.unsigned value).
Proof.
 intros HC HP HA HR HE.
 assert(HV:selected_value physical batches address=word.unsigned value).
 { exact(selected_source_matches_read token_pc token_word initial batches before
     after address value physical(selected_value physical batches address)
     HC HP HA HR eq_refl). }
 unfold source_requirements.
 rewrite(actual_output_requirements width root expression fixed
   (selected_value physical batches address)HE),HV;reflexivity.
Qed.
End OriginalRead.
End CPUISAValueRequirements.
Print Assumptions CPUISAValueRequirements.source_requirements_exact.
