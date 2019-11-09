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

Definition functor_pmap (X : pType) {A B : pType} (f : A ->* B)
  := @F_functor _ (isfunctor_pmap X) _ _ f.

Definition pequiv_functor_pmap `{Funext} (X : pType) {A B : pType} (f : A <~>* B)
  : (X ->* A) <~>* (X ->* B).
Proof.
  by serapply (@pequiv_isfunctor _ (isfunctor_pmap X)).
Defined.

Global Instance isnatural_functor_pmap `{Funext}
  {F G : pType -> pType} `{IsFunctor F} `{IsFunctor G}
  (P : forall (X : pType), F X ->* G X) {nP : IsNatural P}
  (A : pType) : IsNatural (fun X => functor_pmap A (P X)).
Proof.
Admitted.

Global Instance isnatural_compose
  {F G H : pType -> pType}
 `{IsFunctor F} `{IsFunctor G} `{IsFunctor H}
  (P : forall (X : pType), F X ->* G X) {nP : IsNatural P}
  (Q : forall (X : pType), G X ->* H X) {nQ : IsNatural Q}
  : IsNatural (fun X => Q X o* P X).
Proof.
Admitted.

Definition pequiv_profunctor_pmap `{Funext} {A B C D : pType}
  (f : B <~>* A) (g : C <~>* D) : (A ->* C) <~>* (B ->* D).
Proof.
  by serapply pequiv_isprofunctor.
Defined.
