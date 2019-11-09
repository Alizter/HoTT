Require Import Basics.
Require Import Types.
Require Import Pointed.Core.
Require Import Pointed.pMap.
Require Import Pointed.pHomotopy.
Require Import Pointed.pEquiv.
Require Import PointedCategory.Functor.

Local Open Scope pointed_scope.

(* A profunctor is like a bifunctor but contravariant in its first argument. *)
Class IsProfunctor (F : pType -> pType -> pType) := {
  F_profunctor {A B A' B' : pType} (f : A ->* B) (f : A' ->* B')
    : F B A' ->* F A B';
  F_proidmap {A A' : pType} : F_profunctor (@pmap_idmap A) (@pmap_idmap A')
    ==* pmap_idmap;
  F_procompose {A A' B B' C C' : pType} {g : B ->* C} {f : A ->* B}
    {g' : B' ->* C'} {f' : A' ->* B'}
    : F_profunctor (g o* f) (g' o* f')
      ==* (F_profunctor f g') o* (F_profunctor g f');
}.

(* Notably filling the left side of a profunctor gives a functor. *)
Global Instance isfunctor_profunctor_left (F : pType -> pType -> pType)
  `(IsProfunctor F) (A : pType) : IsFunctor (F A).
Proof.
  serapply Build_IsFunctor.
  { intros X Y.
    apply F_profunctor, pmap_idmap. }
  { intro X.
    apply F_proidmap. }
  intros X Y Z f' f; cbn.
  apply (F_procompose (g:=pmap_idmap) (f:=pmap_idmap)).
Defined.

(* TODO: Change name. *)
(* A "2profunctor" is a profunctor which preserves pHomotopies in each argument *)
Class Is2Profunctor (F : pType -> pType -> pType) `{IsProfunctor F} := {
  F_2profunctor : forall (A A' B B' : pType) (f g : A ->* B) (f' g' : A' ->* B'),
    f ==* g -> f' ==* g' -> F_profunctor f f' ==* F_profunctor g g';
}.

(* Given funext any profunctor is a "2profunctor". *)
Global Instance is2profunctor_profunctor `{Funext} {F : pType -> pType -> pType}
  `{IsProfunctor F} : Is2Profunctor F.
Proof.
  serapply Build_Is2Profunctor.
  intros A A' B B' f g f' g' p p'.
  by destruct (path_pmap p), (path_pmap p').
Defined.

(* The equivalence generated from being a profunctor *)
Definition pequiv_isprofunctor (F : pType -> pType -> pType) `{Is2Profunctor F}
  {A A' B B' : pType} : A <~>* B -> A' <~>* B' -> F B A' <~>* F A B'.
Proof.
  intros e e'.
  serapply pequiv_adjointify.
  1: exact (F_profunctor e e').
  1: exact (F_profunctor e^-1* e'^-1*).
  1,2: refine (F_procompose^* @* _).
  1,2: refine (_ @* F_proidmap).
  1,2: apply F_2profunctor.
  2,3: apply peisretr.
  1,2: apply peissect.
Defined.

Class Profunctor := {
  profunctor : pType -> pType -> pType;
  isprofunctor_profunctor :> IsProfunctor profunctor;
}.

Coercion profunctor : Profunctor >-> Funclass.

Global Instance functor_profunctor (A : pType) : Profunctor -> Functor.
Proof.
  intros [P isP].
  exact (Build_Functor _ (isfunctor_profunctor_left _ isP A)).
Defined.

