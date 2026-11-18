(** Mechanically checked packed-bank plans from ordinary NBA plans.
    Unsupported overlap, nested lvalues and case plans are rejected. Values
    are sampled from the same pre-update state as the original NBA semantics. *)
From Coq Require Import List ZArith Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection
 Lang.ExtendedSVAutoAdapterPlan Lang.ExtendedSVAutoAdapterPhase
 Lang.ExtendedSVBankAlignment Lang.ExtendedSVRegisterBank.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVAutoAdapterPlan
 ExtendedSVAutoAdapterPhase ExtendedSVBankAlignment ExtendedSVRegisterBank.
Local Open Scope Z_scope.
Module ExtendedSVBankPlan.

Inductive BankPlan :=
| BPEmpty
| BPWord (offset rhs:Expr)
| BPReset (rhs:Expr)
| BPSeq (plans:list BankPlan)
| BPIf (guard:Expr) (yes no:BankPlan).

Definition compile_bank_assign root total rhs lhs : option BankPlan :=
 if Nat.eqb(lvalue_root lhs)root then
   match lhs with
   | LVar basewidth _ =>
     if Nat.eqb basewidth total && (1024<=?total)%nat
     then Some(BPReset rhs) else None
   | LSel width (LVar basewidth _) offset =>
     if Nat.eqb width 32 && Nat.eqb basewidth total && bounded32b offset
     then Some(BPWord offset rhs) else None
   | _=>None
   end
 else Some BPEmpty.

Fixpoint compile_bank (fuel:nat) (root:signal) (total:nat) (plan:NbPlan)
 : option BankPlan :=
 match fuel with
 | O=>None
 | S f=>match plan with
   | NEmpty=>Some BPEmpty
   | NAssign rhs lhs=>compile_bank_assign root total rhs lhs
   | NSeq plans=>option_map BPSeq(traverse(compile_bank f root total)plans)
   | NIf guard yes no=>match compile_bank f root total yes,compile_bank f root total no with
     | Some y,Some n=>Some(BPIf guard y n)|_,_=>None end
   | NCase _ _=>None
   end
 end.

Fixpoint eval_bank_plan (total:nat) (s:State) (plan:BankPlan) : list BankOperation :=
 match plan with
 | BPEmpty=>[]
 | BPWord offset rhs=>[WriteLane(eval_expr s offset/32)(norm 32(eval_expr s rhs))]
 | BPReset rhs=>[ResetBank total(norm total(eval_expr s rhs))]
 | BPSeq plans=>flat_map(eval_bank_plan total s)plans
 | BPIf guard yes no=>eval_bank_plan total s
     (if Z.eqb(eval_expr s guard)0 then no else yes)
 end.

Definition root_updates root updates :=
 filter(fun u=>Nat.eqb(update_signal u)root)updates.

Lemma compile_bank_assign_sound root total rhs lhs bp :
 compile_bank_assign root total rhs lhs=Some bp ->forall s,
 root_updates root[resolve_update s lhs(eval_expr s rhs)]=
   operation_updates root 32(eval_bank_plan total s bp) /\
 Forall(OperationValid 32 32)(eval_bank_plan total s bp).
Proof.
 unfold compile_bank_assign.
 destruct(Nat.eqb(lvalue_root lhs)root)eqn:HR.
 - destruct lhs as[basewidth id|width base offset].
   + destruct(Nat.eqb basewidth total && (1024<=?total)%nat)eqn:HW;[|discriminate].
     intro HC;inversion HC;subst bp.
     apply andb_true_iff in HW as[HW HT]. apply Nat.eqb_eq in HW;subst basewidth.
     apply Nat.leb_le in HT. cbn in HR;apply Nat.eqb_eq in HR;subst id.
     intro s;split.
     * unfold root_updates,operation_updates;cbn. rewrite Nat.eqb_refl;reflexivity.
     * constructor;[cbn;lia|constructor].
   + destruct base as[basewidth id|nestedwidth nestedbase nestedoffset];[|discriminate].
     destruct(Nat.eqb width 32 && Nat.eqb basewidth total && bounded32b offset)eqn:HW;[|discriminate].
     intro HC;inversion HC;subst bp.
     apply andb_true_iff in HW as[HW HB]. apply andb_true_iff in HW as[HW HT].
     apply Nat.eqb_eq in HW;subst width. apply Nat.eqb_eq in HT;subst basewidth.
     cbn in HR;apply Nat.eqb_eq in HR;subst id.
     intro s. destruct(bounded32b_sound offset HB s)as[HI HM].
     pose proof(Z.div_mod(eval_expr s offset)32 ltac:(lia))as HD.
     split.
     * unfold root_updates,operation_updates;cbn. rewrite Nat.eqb_refl.
       change
        ([{|update_signal:=root;update_offset:=eval_expr s offset;update_width:=32;
            update_value:=norm 32(eval_expr s rhs)|}]=
         [{|update_signal:=root;update_offset:=32*(eval_expr s offset/32);update_width:=32;
            update_value:=norm 32(eval_expr s rhs)|}]).
       assert(HE:eval_expr s offset=32*(eval_expr s offset/32))by nia.
       now rewrite <-HE.
     * constructor;[exact(proj1 HI)|constructor].
 - intro HC;inversion HC;subst bp. intro s;split;[|constructor].
   unfold root_updates;cbn. rewrite resolve_update_root,HR;reflexivity.
Qed.

Theorem compile_bank_sound fuel : forall root total nb bp,
 compile_bank fuel root total nb=Some bp ->forall s,
 root_updates root(eval_plan s nb)=operation_updates root 32(eval_bank_plan total s bp) /\
 Forall(OperationValid 32 32)(eval_bank_plan total s bp).
Proof.
 induction fuel as[|f IH];intros root total nb bp HC s;[discriminate|].
 destruct nb as[|rhs lhs|plans|guard yes no|scrutinee arms];cbn in HC.
 - inversion HC;split;[reflexivity|constructor].
 - now apply compile_bank_assign_sound.
 - destruct(traverse(compile_bank f root total)plans)as[bps|]eqn:HT;[|discriminate].
   inversion HC;subst bp;cbn [eval_plan eval_bank_plan].
   induction plans as[|plan rest IHr]in bps,HT|-*;cbn in HT.
   + inversion HT;split;[reflexivity|constructor].
   + destruct(compile_bank f root total plan)as[p|]eqn:HP;[|discriminate].
     destruct(traverse(compile_bank f root total)rest)as[ps|]eqn:HS;[|discriminate].
     inversion HT;subst bps;cbn [flat_map].
     destruct(IH root total plan p HP s)as[HE HV].
     destruct(IHr ps eq_refl)as[HER HVR]. split.
     * unfold root_updates in *. rewrite filter_app,HE,HER.
       unfold operation_updates. now rewrite map_app.
     * now apply Forall_app.
 - destruct(compile_bank f root total yes)as[y|]eqn:HY;[|discriminate].
   destruct(compile_bank f root total no)as[n|]eqn:HN;[|discriminate].
   inversion HC;subst bp;cbn [eval_plan eval_bank_plan].
   destruct(Z.eqb(eval_expr s guard)0);apply IH;assumption.
 - discriminate.
Qed.
Lemma apply_updates_root_value_filter root updates : forall current,
 apply_updates_root_value root current updates=
 apply_updates_root_value root current(root_updates root updates).
Proof.
 induction updates as[|u rest IH];intro current;[reflexivity|].
 unfold root_updates at 1;cbn [filter].
 destruct(Nat.eqb(update_signal u)root)eqn:HE.
 - cbn [apply_updates_root_value]. apply IH.
 - cbn [apply_updates_root_value].
   unfold apply_update_root_value;rewrite HE. apply IH.
Qed.

Record BankEntry := {
 bank_process:Process;
 bank_nb:NbPlan;
 bank_plan:BankPlan
}.
Definition bank_nb_entries (entries:list BankEntry) :=
 map(fun entry=>(bank_process entry,bank_nb entry))entries.

Record BankRootCertificate (p:Program) (root:signal) (total:nat)
 (entries:list BankEntry) : Prop := {
 bank_root_plans:PlanRootCertificate p root(bank_nb_entries entries);
 bank_root_compiled:Forall(fun entry=>
   compile_bank(statement_fuel p)root total(bank_nb entry)=Some(bank_plan entry))entries
}.

Definition bank_phase_operations total pre driven (entries:list BankEntry) :=
 flat_map(fun entry=>if process_matches_states pre driven(bank_process entry)
   then eval_bank_plan total driven(bank_plan entry)else[])entries.

Lemma compiled_bank_entries fuel root total entries old new :
 Forall(fun entry=>compile_bank fuel root total(bank_nb entry)=Some(bank_plan entry))entries ->
 root_updates root(plan_transition_updates old new(bank_nb_entries entries))=
   operation_updates root 32(bank_phase_operations total old new entries) /\
 Forall(OperationValid 32 32)(bank_phase_operations total old new entries).
Proof.
 intro HC;induction HC as[|[proc nb bp]rest HH HT IH].
 - split;[reflexivity|constructor].
 - cbn [bank_nb_entries map plan_transition_updates bank_phase_operations
     flat_map fst snd bank_process bank_nb bank_plan]in *.
   destruct(process_matches_states old new proc)eqn:HE;cbn [app].
   + destruct(compile_bank_sound fuel root total nb bp HH new)as[HU HV].
     destruct IH as[HR HVR]. split.
     * change(root_updates root(eval_plan new nb ++
         plan_transition_updates old new(bank_nb_entries rest))=
         operation_updates root 32(eval_bank_plan total new bp ++
         bank_phase_operations total old new rest)).
       unfold root_updates in *. rewrite filter_app,HU,HR.
       unfold operation_updates. now rewrite map_app.
     * now apply Forall_app.
   + exact IH.
Qed.

Theorem bank_phase_updates p root total entries :
 BankRootCertificate p root total entries -> forall ev pre,
 changed_signal ev<>root ->
 read_signal(PhaseSemantics p ev pre)root=
 apply_updates_root_value root(read_signal pre root)
   (operation_updates root 32
     (bank_phase_operations total pre(phase_driven_state p ev pre)entries)).
Proof.
 intros[HP HC]ev pre HE.
 rewrite(planned_phase_root p root(bank_nb_entries entries)HP ev pre HE).
 rewrite apply_updates_root_value_filter.
 exact(f_equal (apply_updates_root_value root(read_signal pre root))
   (proj1(compiled_bank_entries(statement_fuel p)root total entries pre
     (phase_driven_state p ev pre)HC))).
Qed.

Theorem bank_phase_related p root total entries :
 BankRootCertificate p root total entries ->forall ev pre abstract,
 changed_signal ev<>root -> BankRelated 32 32(read_signal pre root)abstract ->
 BankRelated 32 32(read_signal(PhaseSemantics p ev pre)root)
   (operation_effects 32 abstract
     (bank_phase_operations total pre(phase_driven_state p ev pre)entries)).
Proof.
 intros[HP HC]ev pre abstract HE HR.
 rewrite(planned_phase_root p root(bank_nb_entries entries)HP ev pre HE).
 rewrite apply_updates_root_value_filter.
 destruct(compiled_bank_entries(statement_fuel p)root total entries pre
   (phase_driven_state p ev pre)HC)as[HU HV]. rewrite HU.
 now apply bank_related_operations.
Qed.
End ExtendedSVBankPlan.
Print Assumptions ExtendedSVBankPlan.compile_bank_sound.
Print Assumptions ExtendedSVBankPlan.bank_phase_updates.
Print Assumptions ExtendedSVBankPlan.bank_phase_related.
