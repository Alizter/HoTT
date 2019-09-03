Require Import Basics Types Pointed Spectrum.
Require Import UnivalenceAxiom.
Require Import abstract_algebra.

Require Import EMSpace.

Definition EMSpectrum (A : Type) `{AbGroup A} : Spectrum.
Proof.
  serapply (Build_Spectrum (Build_Prespectrum _ _) _).
  1: apply (EilenbergMacLane A).
  { intro.
    apply pointed_equiv_fun.
    symmetry.
    apply pequiv_loops_em_em. }
  unfold IsSpectrum.
  exact _.
Defined.
