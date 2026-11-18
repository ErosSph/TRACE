From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVProcessSlice.
Module ExtendedSVStateLength.
Lemma write_length s r v : (r < length s)%nat -> length (write_signal s r v)=length s.
Proof. induction s in r|-*;destruct r;cbn;intros H;try lia. now rewrite IHs by lia. Qed.
Lemma update_length n s u : length s=n -> (update_signal u<n)%nat -> length(apply_update s u)=n.
Proof. intros H HU. unfold apply_update. rewrite write_length;lia. Qed.
Definition ExecLength n es := length(blocking_state es)=n /\
 Forall(fun u=>(update_signal u<n)%nat)(pending_nba es).
Theorem exec_length fuel st n es :
 (forall r,In r(stmt_writers st)->(r<n)%nat)->ExecLength n es->
 ExecLength n(exec_stmt fuel st es).
Proof.
 induction fuel as[|fuel IH]in st,es|-*;[auto|].
 destruct st as[|nba e lv|ss|g y no|e arms];intros HW HE.
 - exact HE.
 - destruct HE as[HL HP]. assert(HU:(update_signal(resolve_update(blocking_state es)lv(eval_expr(blocking_state es)e))<n)%nat).
   { rewrite resolve_update_root. apply HW. cbn. auto. }
   destruct nba;unfold ExecLength;cbn[exec_stmt blocking_state pending_nba].
   + split;[exact HL|]. apply Forall_app. split;[exact HP|]. constructor;auto.
   + split;[now apply update_length|exact HP].
 - cbn[exec_stmt]. induction ss as[|a rest IHr]in es,HW,HE|-*;cbn[fold_left];[exact HE|].
   apply IHr.
   + intros r HR. apply HW. cbn. apply in_or_app. auto.
   + apply IH;[|exact HE]. intros r HR. apply HW. cbn. apply in_or_app. auto.
 - cbn[exec_stmt]. destruct(Z.eqb(eval_expr(blocking_state es)g)0);apply IH;try exact HE;
   intros r HR;apply HW;cbn;apply in_or_app;auto.
 - cbn[exec_stmt]. apply IH;[|exact HE]. intros r HR. apply HW.
   exact(select_case_writers _ _ _ SSkip r HR).
Qed.
Lemma nba_length n us s : Forall(fun u=>(update_signal u<n)%nat)us -> length s=n -> length(apply_nba s us)=n.
Proof. induction us as[|u us IH]in s|-*;intros HU HL;[exact HL|]. inversion HU;subst. cbn[apply_nba]. apply IH;auto. now apply update_length. Qed.
Lemma process_length p proc n s :
 (forall r,In r(process_writers proc)->(r<n)%nat)->length s=n->length(run_process p s proc)=n.
Proof.
 intros HW HL. unfold run_process.
 destruct(exec_length(statement_fuel p)(process_body proc)n
 {|blocking_state:=s;pending_nba:=[];emitted_updates:=[]|} HW
 ltac:(split;[exact HL|constructor]))as[HB HN].
 now apply nba_length.
Qed.
Definition program_lengthb p n := forallb(fun proc=>forallb(fun r=>Nat.ltb r n)(process_writers proc))(processes p).
Lemma fold_length p n ps s : program_lengthb p n=true ->
 (forall proc,In proc ps->In proc(processes p))->length s=n->
 length(fold_left(run_process p)ps s)=n.
Proof.
 intros HC. induction ps as[|proc rest IH]in s|-*;intros HI HL;[exact HL|].
 cbn[fold_left]. apply IH;[intros q HQ;apply HI;right;exact HQ|].
 apply process_length;[|exact HL]. intros r HR. unfold program_lengthb in HC.
 apply forallb_forall with(x:=proc)in HC;[|apply HI;left;reflexivity].
 apply forallb_forall with(x:=r)in HC;[now apply Nat.ltb_lt|exact HR].
Qed.
Lemma round_length p n s : program_lengthb p n=true ->length s=n->length(comb_round p s)=n.
Proof. intros HC HL. unfold comb_round. apply fold_length;auto. intros proc HP. apply filter_In in HP. tauto. Qed.
Lemma iter_length p n k s : program_lengthb p n=true ->length s=n->length(comb_iter p k s)=n.
Proof. intros HC. induction k in s|-*;intro HL;[exact HL|]. cbn[comb_iter]. apply IHk. now apply round_length. Qed.
Lemma state_ext s t : length s=length t -> (forall r,read_signal s r=read_signal t r)->s=t.
Proof.
 induction s as[|a s IH]in t|-*;destruct t as[|b t];cbn;intros HL HR;try discriminate;auto.
 assert(a=b)by exact(HR 0%nat). subst b. f_equal. apply IH;[lia|]. intro r. exact(HR(S r)).
Qed.
Lemma updates_length n us s : Forall(fun u=>(update_signal u<n)%nat)us -> length s=n -> length(apply_updates s us)=n.
Proof. induction us as[|u us IH]in s|-*;intros HU HL;[exact HL|]. inversion HU;subst. cbn[apply_updates]. apply IH;auto. now apply update_length. Qed.
Lemma captured_length p n order s : program_lengthb p n=true ->
 (forall proc,In proc order->In proc(processes p))->length s=n->
 length(execute_process_order p s order)=n.
Proof.
 intros HC HI HL. unfold execute_process_order. apply updates_length;[|exact HL].
 apply Forall_forall. intros u HU. apply in_flat_map in HU as[proc[HP HU]].
 unfold program_lengthb in HC. apply forallb_forall with(x:=proc)in HC;[|now apply HI].
 apply forallb_forall with(x:=update_signal u)in HC;[now apply Nat.ltb_lt|].
 exact(process_emitted_writers p s proc u HU).
Qed.
End ExtendedSVStateLength.
