Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import Coherence.

(* In this file we describe the postcomposition functor. *)

Local Open Scope pointed_scope.

Global Instance isprofunctor_pmap : IsProfunctor (fun x y => x ->* y).
Proof.
  serapply Build_IsProfunctor.
  { intros A B C D f g.
    serapply Build_pMap.
    { intros i.
      refine (g o* i o* f). }
    by pointed_reduce. }
  { cbn.
    intros A B.
    serapply Build_pHomotopy.
    { intro; cbn.
      by pointed_reduce. }
    reflexivity. }
  intros A B C D E F f g f' g'.
  serapply Build_pHomotopy.
  1: intro.
  all: by pointed_reduce.
Defined.

Global Instance isfunctor_pmap (X : pType) : IsFunctor (fun x => X ->* x).
Proof.
  serapply isfunctor_profunctor_left.
Defined.

Definition pequiv_profunctor_pmap `{Funext} {A B C D : pType}
  (f : B <~>* A) (g : C <~>* D) : (A ->* C) <~>* (B ->* D).
Proof.
  by serapply pequiv_isprofunctor.
Defined.


