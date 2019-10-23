Require Import Basics.
Require Import Types.
Require Import Pointed.Core.
Require Import Pointed.pMap.
Require Import Pointed.pEquiv.
Require Import Pointed.pHomotopy.

(* Naming convention *)
(*

  functor_X = the actual functor object corresponding to X,
              can be applied to objects.
  X_functor = the functorial action of X

*)


Local Open Scope pointed_scope.

(* By functor we really mean 1-coherent functor *)
Class IsFunctor (F : pType -> pType) := {
  F_functor {A B : pType} (f : A ->* B) : F A ->* F B;
  F_idmap {A : pType} : F_functor (@pmap_idmap A) ==* pmap_idmap;
  F_compose {A B C : pType} {f' : B ->* C} {f : A ->* B}
    : F_functor (f' o* f) ==* F_functor f' o* F_functor f;
}.

(* TODO: Change name. *)
(* A "2Functor" is a functor which preserves pHomotopies *)
Class Is2Functor (F : pType -> pType) `{IsFunctor F} := {
  F_2functor {A B : pType} {f g : A ->* B}
    : f ==* g -> F_functor f ==* F_functor g
}.

(* Given funext any functor is a "2functor". *)
Global Instance is2functor_functor `{Funext} {F : pType -> pType}
  `{IsFunctor F} : Is2Functor F.
Proof.
  serapply Build_Is2Functor.
  intros A B f g p.
  by destruct (path_pmap p).
Defined.

(* The equivalence generated from being a functor *)
Definition pequiv_isfunctor (F : pType -> pType) `{Is2Functor F}
  {A B : pType} : A <~>* B -> F A <~>* F B.
Proof.
  intro e.
  serapply pequiv_adjointify.
  1: apply F_functor, e.
  1: apply F_functor, e^-1*.
  1,2: refine (F_compose^* @* _).
  1,2: refine (_ @* F_idmap).
  1,2: apply F_2functor.
  1: apply peisretr.
  apply peissect.
Defined.

Global Instance isfunctor_compose (F G : pType -> pType)
  `{Is2Functor F} `{IsFunctor G} : IsFunctor (F o G).
Proof.
  serapply Build_IsFunctor.
  { intros A B f; cbn.
    apply F_functor, F_functor, f. }
  { intros A; cbn.
    refine (F_2functor F_idmap @* F_idmap). }
  intros A B C f' f; cbn.
  refine (F_2functor F_compose @* F_compose).
Defined.

Class Functor := {
  functor : pType -> pType;
  isfunctor_functor :> IsFunctor functor;
}.

Coercion functor : Functor >-> Funclass.

Global Instance isfunctor_id : IsFunctor idmap.
Proof.
  by serapply Build_IsFunctor.
Defined.

Arguments F_functor _ {_ _ _}.

