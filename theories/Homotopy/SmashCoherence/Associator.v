Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import PointedCategory.Natural.
Require Import PointedCategory.pMapFunctor.
Require Import Homotopy.Smash.
Require Import Homotopy.SmashCoherence.Bifunctor.
Require Import Homotopy.SmashCoherence.SmashAdj.
Require Import PointedCategory.Adjunction.

(* Smash product is associative *)

Local Open Scope path_scope.
Local Open Scope pointed_scope.

Local Notation "A '->*' B" := (Build_pType (A ->* B) _).
Local Notation "1" := pequiv_pmap_idmap.

Section Assoc.

  Context `{Funext}.

  Definition natequiv_smash_adj {A B : pType}
    := natequiv_adj (adjunction_smash_pmap A) B.

  Local Infix "~" := NaturalEquivalence (at level 20).
  Local Infix "oN" := natequiv_compose (at level 15).
  Local Notation "e '^N'" := (natequiv_inv e) (at level 0).

  Theorem pequiv_smash_assoc (A B C : pType)
    : (A ∧ B) ∧ C <~>* A ∧ (B ∧ C).
  Proof.
    serapply pYoneda.
    refine (natequiv_smash_adj oN _).
    refine (natequiv_postwhisker _ natequiv_smash_adj oN _).
    refine (natequiv_functor_compose_assoc _ _ _ oN _).
    refine (natequiv_prewhisker _ natequiv_smash_adj^N oN _).
    apply natequiv_smash_adj^N.
  Defined.

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

End Assoc.

