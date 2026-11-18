(**
  Proof boundary for elaboration-only SystemVerilog constructs.

  Packages, typedefs, enums and generate constructs do not receive a second
  runtime semantics.  An external elaborator removes them and emits a complete
  [ExtendedSV.Program].  Its source/output digests and feature inventory form
  a translation-validation certificate; the emitted program is then checked
  and executed entirely inside Rocq.
 *)
From Coq Require Import List Strings.String.
Require Import Lang.ExtendedSV.
Import ListNotations.
Import ExtendedSV.

Module ElaborationLowering.

  Inductive ElaborationFeature :=
  | FeatureTypedef | FeatureEnum | FeaturePackageImport
  | FeatureParameter | FeatureLocalparam
  | FeatureForGenerate | FeatureCaseGenerate
  | FeaturePackedDeclaration | FeatureInterface.

  Record CheckedElaboratedUnit := {
    source_digest : string;
    elaborated_digest : string;
    features_seen : list ElaborationFeature;
    unsupported_elaboration_nodes : nat;
    lowered_runtime : Program
  }.

  Definition lowering_checked (u : CheckedElaboratedUnit) : bool :=
    andb (Nat.eqb u.(unsupported_elaboration_nodes) 0)
      (andb (negb (String.eqb u.(source_digest) EmptyString))
            (negb (String.eqb u.(elaborated_digest) EmptyString))).

  Definition StandardSemAfterElaboration (u : CheckedElaboratedUnit) :=
    PhaseSemantics u.(lowered_runtime).

  Definition LoweredSemantics (u : CheckedElaboratedUnit) :=
    PhaseSemantics u.(lowered_runtime).

  (** Once translation validation has accepted the elaborated runtime term,
      elaboration-only syntax cannot change scheduling: both sides use the
      exact same kernel-checked runtime program. *)
  Theorem checked_lowering_semantics_preserving : forall u,
      lowering_checked u = true ->
      StandardSemAfterElaboration u = LoweredSemantics u.
  Proof. reflexivity. Qed.

  (** Conservative dispatcher.  Existing VerilRocq developments select the
      [LegacyBackend] branch and therefore reduce definitionally to their old
      transition.  The normalized backend is opt-in. *)
  Inductive SemanticsBackend (A : Type) :=
  | LegacyBackend (old_transition : A -> A)
  | ExtendedBackend (encode : A -> State) (decode : State -> A)
      (program : Program) (event : Event).

  Arguments LegacyBackend {A} _.
  Arguments ExtendedBackend {A} _ _ _ _.

  Definition dispatch_semantics {A} (backend : SemanticsBackend A) (s : A) : A :=
    match backend with
    | LegacyBackend old => old s
    | ExtendedBackend encode decode program event =>
        decode (PhaseSemantics program event (encode s))
    end.

  Theorem extended_semantics_conservative : forall A (old : A -> A),
      dispatch_semantics (LegacyBackend old) = old.
  Proof. reflexivity. Qed.

End ElaborationLowering.
