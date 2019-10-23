Require Import Basics.
Require Import Types.
Require Import Pointed.Core.
Require Import Pointed.pMap.
Require Import Pointed.pHomotopy.
Require Import Pointed.pEquiv.
Require Import PointedCategory.Functor.

Local Open Scope pointed_scope.


Class IsPointedFunctor (F : Functor) := {
  F_zero : F punit <~>* punit
}.

Lemma pmap_const_factor' {A B C : pType} {f : C ->* B} {g : A ->* C}
  (p : C <~>* punit) : f o* g ==* pmap_const.
Proof.
  refine (pmap_postwhisker _ (pmap_postcompose_idmap _)^* @* _).
  refine (pmap_postwhisker _ (pmap_prewhisker _ (peissect p)^* ) @* _).
  refine (pmap_postwhisker _ (pmap_compose_assoc _ _ _) @* _).
  refine ((pmap_compose_assoc _ _ _)^* @* _).
  apply pmap_const_factor.
Defined.

(* TODO: Rename? *)
Lemma F_functor_zero {F : Functor} {h : IsPointedFunctor F} {A B : pType}
  : F_functor F (pmap_const : A ->* B) ==* pmap_const.
Proof.
  change (F_functor F ((pmap_const : punit ->* B)
    o* (pmap_const : A ->* punit)) ==* pmap_const).
  refine (F_compose @* _).
  serapply pmap_const_factor'.
  apply F_zero.
Defined.
