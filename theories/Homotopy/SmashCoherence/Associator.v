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

Section Assoc.

  Context `{Funext}.

  Definition natequiv_smash_adj {A B : pType}
    := natequiv_adj (adjunction_smash_pmap A) B.

  Lemma natequiv_smash_assoc {A B C : pType}
    :  functor_pmap (A ∧ (B ∧ C)) ~ functor_pmap ((A ∧ B) ∧ C).
  Proof.
    refine (natequiv_smash_adj oN _).
    refine (functor_postwhisker _ natequiv_smash_adj oN _).
    refine (natequiv_functor_compose_assoc _ _ _ oN _).
    refine (functor_prewhisker _ natequiv_smash_adj^N oN _).
    apply natequiv_smash_adj^N.
  Defined.

  Theorem pequiv_smash_assoc (A B C : pType)
    : (A ∧ B) ∧ C <~>* A ∧ (B ∧ C).
  Proof.
    serapply pYoneda.
    apply natequiv_smash_assoc.
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
          simpl.
  Admitted.

End Assoc.

