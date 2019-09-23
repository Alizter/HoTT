Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import Spectrum.
Require Import Colimits.Colimit.
Require Import Diagrams.Cocone.
Require Import Diagrams.Sequence.
Require Import Spaces.Nat.

Local Open Scope pointed_scope.
Local Open Scope nat_scope.

(** Spectrification defined as a sequential colimit *)

Section Spectrification.

  (* The diagram we will be taking a colimit of *)
  (* We write k + n so that 0 + n is definitionally n *)
  Definition Seq (Y : Prespectrum) (n : nat) : Sequence.
  Proof.
    serapply Build_Sequence.
    { intro k.
      exact (iterated_loops k (Y (k + n))). }
    intros k x.
    refine (transport _ (unfold_iterated_loops k _)^ _).
    revert x.
    refine (iterated_loops_functor k _).
    apply glue.
  Defined.

  Definition L (Y : Prespectrum) (n : nat) : pType.
  Proof.
    serapply Build_pType.
    1: exact (Colimit (Seq Y n)).
    serapply colim; cbn.
    1: exact 0.
    apply ispointed_type.
  Defined.

  Definition glueL {Y : Prespectrum} (n : nat)
    : L Y n ->* loops (L Y n.+1).
  Proof.
  Admitted.

  Global Instance isequiv_glueL {Y : Prespectrum} {n : nat}
    : IsEquiv (@glueL Y n).
  Proof.
  Admitted.

  Definition Spectrification (Y : Prespectrum) : Spectrum.
  Proof.
    serapply Build_Spectrum.
    + by apply L.
    + apply glueL.
    + intro n.
      exact _.
  Defined.

End Spectrification.
