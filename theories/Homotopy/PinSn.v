Require Import Basics.
Require Import Types.
Require Import Pointed.

Require Import Spaces.Int.

Require Import HIT.Spheres.

Require Import HIT.Truncations.

Require Import Homotopy.HomotopyGroup.
Require Import Homotopy.Pi1S1.
Require Import Homotopy.Pi2S2.
Require Import EMSpace.

Import TrM.

Section PinSn.

  Context `{Univalence}.

  Local Open Scope pointed_scope.

  Theorem PinSn (n : nat) : Pi n.+1 (psphere n.+1) <~> Int.
  Proof.
    induction n as [|[]].
    1: apply Pi1S1'.
    1: apply Pi2S2.
    refine (IHn oE _).
    refine (_ oE _ oE _).
    1: symmetry.
    { unfold Pi.
      refine (EMSpace.trunc_lemma n _).
    
    EMSpace.trunc_lemma n _).
    
    pequiv_ptr_loop_psusp
    
    destruct n.
