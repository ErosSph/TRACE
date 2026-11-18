(** A source must be fresh when the consumer actually uses it, not in a
    stalled/inactive cycle. Consumer guard identification is a DUT obligation. *)
From Coq Require Import ZArith List.
Require Import Lang.ExtendedSV Lang.ExtendedSVValueRequirements
 Ex.External.CPUReadyOperand Ex.External.CPUISAReadyBatches
 Ex.External.CPUISAOwnedEffects Ex.External.CPURegisterEffectRelation
 Ex.RvCore.FormalSpec Ex.RvCore.Machine
 coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth
 coqutil.Map.Interface coqutil.Byte.
Import ExtendedSV ExtendedSVValueRequirements CPUReadyOperand CPUISAReadyBatches
 CPUISAOwnedEffects CPURegisterEffectRelation.
Local Open Scope Z_scope.
Module CPUReadySelectionRequirements.

Definition selection_requirements width expression state physical address slots:Prop:=
 if address=?0 then requirements width expression state 0 else
 match lookup address slots with
 |None=>requirements width expression state(physical address)
 |Some None=>False
 |Some(Some value)=>requirements width expression state value
 end.

Theorem selection_exact width expression state physical address slots:
 selection_requirements width expression state physical address slots <->
 resolve 0 physical address slots=Some(norm width(eval_expr state expression)).
Proof.
 unfold selection_requirements,resolve.
 destruct(address=?0);[rewrite requirements_exact;split;congruence|].
 destruct(lookup address slots)as[[value|]|].
 - rewrite requirements_exact;split;congruence.
 - split;intro H;[contradiction|discriminate].
 - rewrite requirements_exact;split;congruence.
Qed.

Definition guarded_requirements guard width expression state physical address slots:=
 eval_expr state guard<>0 ->selection_requirements width expression state physical address slots.

Theorem actual_consumption_ready guard width root expression state physical address slots:
 norm width(read_signal state root)=norm width(eval_expr state expression) ->
 guarded_requirements guard width expression state physical address slots ->
 eval_expr state guard<>0 ->
 resolve 0 physical address slots=Some(norm width(read_signal state root)).
Proof. intros HE HG HA;rewrite HE;apply selection_exact;exact(HG HA). Qed.

Theorem unready_requires_inactive guard width expression state physical address slots:
 address<>0 ->lookup address slots=Some None ->
 guarded_requirements guard width expression state physical address slots ->
 eval_expr state guard=0.
Proof.
 intros HZ HL HG;destruct(Z.eq_dec(eval_expr state guard)0)as[H|H];[exact H|].
 specialize(HG H);unfold selection_requirements in HG.
 assert(HB:(address=?0)=false)by(now apply Z.eqb_neq).
 rewrite HB,HL in HG;contradiction.
Qed.

Section OriginalRead.
Context {word:Interface.word 32}{BW:Bitwidth 32}
 {Registers:map.map Z word}{Mem:map.map word byte}{word_ok:word.ok word}{Token:Type}.
Theorem active_source_matches_original_read (token_pc token_word:Token->Z)
 guard width root expression state initial batches before after address value physical slots:
 CertifiedBatches token_pc token_word initial batches before ->
 RegisterRelated physical initial ->0<=address<32 ->
 Machine.getRegister address before=(Some value,after) ->
 Forall2 SlotRelated slots(batch_writes 32 address batches) ->
 norm width(read_signal state root)=norm width(eval_expr state expression) ->
 guarded_requirements guard width expression state physical address slots ->
 eval_expr state guard<>0 ->
 norm width(read_signal state root)=word.unsigned value.
Proof.
 intros HC HP HA HR HS HE HG HU.
 exact(actual_ready_selector_matches_read token_pc token_word initial batches before
   after address value physical slots(norm width(read_signal state root)) HC HP HA HR HS
   (actual_consumption_ready guard width root expression state physical address slots HE HG HU)).
Qed.
End OriginalRead.
End CPUReadySelectionRequirements.
Print Assumptions CPUReadySelectionRequirements.selection_exact.
Print Assumptions CPUReadySelectionRequirements.unready_requires_inactive.
Print Assumptions CPUReadySelectionRequirements.active_source_matches_original_read.
