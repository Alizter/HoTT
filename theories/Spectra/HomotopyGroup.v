Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import Spectrum.
Require Import Colimits.Colimit.
Require Import Diagrams.Sequence.
Require Import Homotopy.HomotopyGroup.
Require Import Spaces.Nat.
Require Import HIT.Truncations.
Require Import abstract_algebra.

Import TrM.

(* Homotopy groups of spectra *)

Local Open Scope nat_scope.

(* Currently wrong. n should be an integer. And the diagram needs to be shifted for a negative n *)

Definition PiSpectra_Sequence (n : nat) (X : Spectrum) : Sequence.
Proof.
  serapply Build_Sequence.
  { intro a.
    exact (Pi (a + n) (X a)). }
  intro a.
  destruct a.
  { apply Trunc_functor.
    intro x.
    apply unfold_iterated_loops'.
    revert x.
    apply iterated_loops_functor.
    apply glue. }
  intro x.
  apply Pi_loops.
  revert x.
  refine (pi_functor _).
  apply glue.
Defined.

Definition PiSpectra (n : nat) (X : Spectrum)
  := Colimit (PiSpectra_Sequence n X).

Section PiSpectraGroup.

  Context (n : nat) (X : Spectrum).

  Global Instance PiS_Unit : MonUnit (PiSpectra n X).
  Proof.
    unfold MonUnit.
    serapply colim.
    1: exact 0.
    simpl.
    apply PiUnit.








