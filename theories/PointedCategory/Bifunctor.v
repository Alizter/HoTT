Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import PointedCategory.Functor.

Local Open Scope pointed_scope.

Class IsBifunctor (F : pType -> pType -> pType) := {
  F_bifunctor {A B A' B' : pType} (f : A ->* B) (f : A' ->* B')
    : F A A' ->* F B B';
  F_bidmap {A A' : pType} : F_bifunctor (@pmap_idmap A) (@pmap_idmap A')
    ==* pmap_idmap;
  F_bicompose {A A' B B' C C' : pType} {g : B ->* C} {f : A ->* B}
    {g' : B' ->* C'} {f' : A' ->* B'}
    : F_bifunctor (g o* f) (g' o* f')
      ==* (F_bifunctor g g') o* (F_bifunctor f f');
}.

Global Instance isfunctor_bifunctor_left (F : pType -> pType -> pType)
  `{IsBifunctor F} (A : pType) : IsFunctor (F A).
Proof.
  serapply Build_IsFunctor.
  { intros X Y.
    apply F_bifunctor, pmap_idmap. }
  { intro X.
    apply F_bidmap. }
  intros X Y Z f' f; cbn.
  apply (F_bicompose (g:=pmap_idmap) (f:=pmap_idmap)).
Defined.

Global Instance isfunctor_bifunctor_right (F : pType -> pType -> pType)
  `{IsBifunctor F} (A : pType) : IsFunctor (fun x => F x A).
Proof.
  serapply Build_IsFunctor.
  { intros X Y f; cbn.
    refine (F_bifunctor f pmap_idmap). }
  { intro X.
    apply F_bidmap. }
  intros X Y Z f' f; cbn.
  apply (F_bicompose (g':=pmap_idmap) (f':=pmap_idmap)).
Defined.

(* TODO: Change name. *)
(* A "2Bifunctor" is a bifunctor which preserves pHomotopies in each argument *)
Class Is2Bifunctor (F : pType -> pType -> pType) `{IsBifunctor F} := {
  F_2bifunctor : forall (A A' B B' : pType) (f g : A ->* B) (f' g' : A' ->* B'),
    f ==* g -> f' ==* g' -> F_bifunctor f f' ==* F_bifunctor g g';
}.

(* Given funext any bifunctor is a "2Bifunctor". *)
Global Instance is2bifunctor_bifunctor `{Funext} {F : pType -> pType -> pType}
  `{IsBifunctor F} : Is2Bifunctor F.
Proof.
  serapply Build_Is2Bifunctor.
  intros A A' B B' f g f' g' p p'.
  by destruct (path_pmap p), (path_pmap p').
Defined.

(* The equivalence generated from being a bifunctor *)
Definition pequiv_isbifunctor (F : pType -> pType -> pType) `{Is2Bifunctor F}
  {A A' B B' : pType} : A <~>* B -> A' <~>* B' -> F A A' <~>* F B B'.
Proof.
  intros e e'.
  serapply pequiv_adjointify.
  1: exact (F_bifunctor e e').
  1: exact (F_bifunctor e^-1* e'^-1*).
  1,2: refine (F_bicompose^* @* _).
  1,2: refine (_ @* F_bidmap).
  1,2: apply F_2bifunctor.
  1,2: apply peisretr.
  1,2: apply peissect.
Defined.

Class Bifunctor := {
  bifunctor : pType -> pType -> pType;
  isbifunctor_bifunctor :> IsBifunctor bifunctor;
}.

Coercion bifunctor : Bifunctor >-> Funclass.
