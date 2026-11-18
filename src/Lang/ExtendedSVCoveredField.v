(** A concrete, pointwise invariant component. No future execution, safety
    promise, commit result or progress property is hidden in this record. *)
From Coq Require Import ZArith.
Require Import Lang.ExtendedSV.
Import ExtendedSV.
Module ExtendedSVCoveredField.
Section Fields.
Context {Label:Type}.
Record Related width root validroot(reference:Label->Z)(tag:option Label)(s:State):Prop:={
 field_coverage:norm 1(read_signal s validroot)<>0%Z ->exists label,tag=Some label;
 field_value:forall label,tag=Some label ->norm width(read_signal s root)=reference label
}.
Theorem related_valid_value width root validroot reference tag s:
 Related width root validroot reference tag s ->norm 1(read_signal s validroot)<>0%Z ->
 exists label,tag=Some label /\norm width(read_signal s root)=reference label.
Proof.
 intros[HC HV]Hvalid;destruct(HC Hvalid)as[label Htag].
 exists label;split;[exact Htag|now apply HV].
Qed.
Theorem invalid_empty_related width root validroot reference s:
 norm 1(read_signal s validroot)=0%Z ->Related width root validroot reference None s.
Proof. intros Hzero;constructor;[intro H;contradiction|intros label H;discriminate]. Qed.
End Fields.
Print Assumptions related_valid_value.
Print Assumptions invalid_empty_related.
End ExtendedSVCoveredField.
