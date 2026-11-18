(** Static, sound paths through one-bit OR expressions. CPU-independent. *)
From Coq Require Import ZArith Bool PeanoNat btauto.Btauto.
Require Import Lang.ExtendedSV.
Import ExtendedSV.
Local Open Scope Z_scope.
Module ExtendedSVOneBitOrPath.
Fixpoint one_bit_or_pathb (root:signal)(expression:Expr):bool:=
 match expression with
 |EVar 1 id=>Nat.eqb root id
 |EBinary 1 BOr lhs rhs=>one_bit_or_pathb root lhs || one_bit_or_pathb root rhs
 |_=>false
 end.
Lemma one_or_left x:norm 1(Z.lor 1 x)=1.
Proof.
 unfold norm,mask;change(Z.land(Z.lor 1 x)1=1).
 rewrite Z.land_lor_distr_l;change(Z.land 1 1)with 1.
 apply Z.bits_inj;intro i;rewrite Z.lor_spec,Z.land_spec;btauto.
Qed.
Lemma one_or_right x:norm 1(Z.lor x 1)=1.
Proof. rewrite Z.lor_comm;apply one_or_left. Qed.
Theorem one_bit_or_path_sound expression:forall root s,
 one_bit_or_pathb root expression=true -> norm 1(read_signal s root)=1 ->
 eval_expr s expression=1.
Proof.
 induction expression as[w z|w id|w base IHbase lsb IHlsb|
 w high IHhigh low IHlow|w count body IHbody|w signed body IHbody|
 w op body IHbody|w op lhs IHlhs rhs IHrhs|
 w guard IHguard yes IHyes no IHno];intros root s HC HV;
 try discriminate.
 - destruct w as[|[|w]];try discriminate.
   cbn[one_bit_or_pathb]in HC;apply Nat.eqb_eq in HC;subst root;exact HV.
 - destruct w as[|[|w]];try discriminate;destruct op;try discriminate.
   cbn[one_bit_or_pathb]in HC;apply Bool.orb_true_iff in HC.
   change(norm 1(Z.lor(eval_expr s lhs)(eval_expr s rhs))=1).
   destruct HC as[HC|HC].
   + rewrite(IHlhs root s HC HV);apply one_or_left.
   + rewrite(IHrhs root s HC HV);apply one_or_right.
Qed.
End ExtendedSVOneBitOrPath.
Print Assumptions ExtendedSVOneBitOrPath.one_bit_or_path_sound.
