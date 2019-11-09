Require Import Basics.
Require Import Types.
Require Import Pointed.Core.
Require Import Pointed.pMap.
Require Import Pointed.pHomotopy.
Require Import Pointed.pEquiv.
Require Import PointedCategory.Profunctor.
Require Import PointedCategory.Functor.
Require Import PointedCategory.pFunctor.

Local Open Scope pointed_scope.


(* In this file we describe the postcomposition functor. *)

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

Definition profunctor_pmap : Profunctor
  := Build_Profunctor _ isprofunctor_pmap.

Definition functor_pmap (A : pType) : Functor.
Proof.
  apply (functor_profunctor A), profunctor_pmap.
Defined.

Global Instance ispointedfunctor_functor_pmap `{Funext}
  (B : pType) : IsPointedFunctor (functor_pmap B).
Proof.
  serapply Build_IsPointedFunctor.
  serapply pequiv_adjointify'.
  { serapply Build_pMap.
    { intro f.
      apply f, ispointed_type. }
    apply point_eq. }
  { serapply Build_pMap.
    { intros x.
      serapply Build_pMap.
      1: intro; apply x.
      by destruct x. }
    reflexivity. }
  1: cbn; reflexivity.
  intros x.
  apply path_pmap.
  serapply Build_pHomotopy.
  1: cbn; intro; apply path_unit.
  apply path_contr.
Defined.

