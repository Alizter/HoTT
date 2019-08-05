Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import Smash.
Require Import Bifunctor.

(* Smash product is associative *)

Local Open Scope path_scope.
Local Open Scope pointed_scope.

(* TODO: use 3x3 lemma? *)
Theorem pequiv_smash_assoc (A B C : pType)
  : (A ∧ B) ∧ C <~>* A ∧ (B ∧ C).
Proof.
  serapply Build_pEquiv'.
  { serapply equiv_adjointify.
    { serapply smash_rec'.
      { serapply smash_rec'.
        { intros a b c.
          exact (sm a (sm b c)). }
Admitted.

Theorem smash_assoc_nat (A A' B B' C C' : pType)
  (f : A ->* A') (g : B ->* B') (h : C ->* C')
  : f [∧] (g [∧] h) o* pequiv_smash_assoc A B C
  ==* pequiv_smash_assoc A' B' C' o* (f [∧] g) [∧] h.
Proof.
  serapply Build_pHomotopy.
  { serapply smash_ind.
    { serapply smash_ind.
      { intros a b c.
Admitted.