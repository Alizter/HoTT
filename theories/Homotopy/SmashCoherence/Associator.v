Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import PointedCategory.Functor.
Require Import PointedCategory.Bifunctor.
Require Import PointedCategory.pMapFunctor.
Require Import Homotopy.Smash.
Require Import Homotopy.SmashCoherence.Bifunctor.
Require Import SmashAdj.
Require Import pMapFunctor.
Require Import Coherence.

(* Smash product is associative *)

Local Open Scope path_scope.
Local Open Scope pointed_scope.

Local Notation "A '->*' B" := (Build_pType (A ->* B) _).
Local Notation "1" := pequiv_pmap_idmap.

Require Import pYoneda.

Section Assoc.

Context `{Funext}.

(* TODO: we need this just to assume what is below. *)
Global Instance isfunctor_smash_adj (A B : pType)
  : IsFunctor (fun X : pType => A ->* B ->* X).
Proof.
  serapply isfunctor_compose.
Defined.

(* TODO : Prove in SmashAdj.v *)
Global Instance isnatural_smash_adj {A B : pType}
  : IsNatural (fun X => @pequiv_smash_adj _ A B X).
Proof.
Admitted.

Definition isnatural_pequiv_inv {F G : pType -> pType}
  `{IsFunctor F} `{IsFunctor G} {P : forall (X : pType), F X <~>* G X}
  `{IsNatural _ _ (fun X => P X)} : IsNatural (fun X => (P X)^-1*).
Proof.
Admitted.

Arguments pequiv_smash_adj {_} A B C.

Global Instance foo {A B C : pType}
  : @IsNatural _ _ _ (isfunctor_compose _ _)
    (fun X => pequiv_functor_pmap A (pequiv_smash_adj B C X)).
Proof.
Admitted.

Theorem pequiv_smash_assoc (A B C : pType)
  : (A ∧ B) ∧ C <~>* A ∧ (B ∧ C).
Proof.
  serapply pYoneda.
  1: intro X.
  (* e^-1 *)
  1: srefine (_ o*E pequiv_smash_adj _ _ _).
  2: srefine (isnatural_compose _ _);
   [ | apply isnatural_smash_adj | ].
  (* A -> e^-1 *)
  1: srefine (_ o*E pequiv_functor_pmap A (pequiv_smash_adj _ _ _)).
  2: srefine (isnatural_compose _ _);
    [ serapply isfunctor_compose
    | serapply foo | ].
  (* e *)
  1: srefine (_ o*E (pequiv_smash_adj _ _ _)^-1*).
  2: {
    srefine (isnatural_compose _ _).
    1: shelve.
    { serapply isnatural_pequiv_inv.
      1: serapply isfunctor_compose.
      refine @isnatural_compose _ _ _ _ _ _ _ isnatural_functor_pmap _.
    
   [ | serapply isnatural_pequiv_inv | ].
    [ serapply isfunctor_compose
    | |].
    
    
  2: serapply (@isnatural_compose _ _ _ _ _ _ _ _ _ (isnatural_smash_adj_inv)).
  
  3: isnatural_smash_adj_inv.
  
  2: { 
  serapply (isnatural_functor_pmap (fun X => @pequiv_smash_adj _ A B X) A).
  1: 
  
  serapply isnatural_compose.
    change (IsNatural ((pequiv_functor_pmap A) o composeD (pequiv_smash_adj B C))).
  2: refine (isnatural_compose _ _).
  
  1: refine (_ o*E pequiv_smash_adj^-1*).
  apply pequiv_smash_adj^-1*.
  Unshelve.
  cbv beta.
  change
    (IsNatural
      (fun X : pType =>
        (@pequiv_smash_adj H (A ∧ B) C X)^-1*
    o* (@pequiv_smash_adj H A B (C ->* X))^-1*
    o*  @pequiv_functor_pmap H A (B ∧ C ->* X) (B ->* C ->* X)
        (@pequiv_smash_adj H B C X)
    o* @pequiv_smash_adj H A (B ∧ C) X)).
  srefine (isnatural_compose _ _).
  1: serapply isfunctor_compose.
  1: shelve.
  srefine (isnatural_compose _ _).
  1: refine (isfunctor_compose _ _.
  1: shelve.
  refine (isnatural_compose _ _).
  Unshelve.
  
  
  
  
  
  refine (isnatural_compose _ (fun X => (pequiv_smash_adj (C:=X))^-1*)).
  (* This should follow from the fact that our equivalences are natural in their arguments. We need to package up this data and make it accessible somehow. *)
Admitted.

Theorem smash_assoc_nat (A A' B B' C C' : pType)
  (f : A ->* A') (g : B ->* B') (h : C ->* C')
  : f [∧] (g [∧] h) o* pequiv_smash_assoc A B C
  ==* pequiv_smash_assoc A' B' C' o* (f [∧] g) [∧] h.
Proof.
  serapply Build_pHomotopy.
  { serapply Smash_ind.
    { serapply Smash_ind.
      { intros a b c.
Admitted.