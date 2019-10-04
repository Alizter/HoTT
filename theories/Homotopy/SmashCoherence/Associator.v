Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import Smash.
Require Import Bifunctor.
Require Import SmashAdj.

(* Smash product is associative *)

Local Open Scope path_scope.
Local Open Scope pointed_scope.

Local Notation "A '->*' B" := (Build_pType (A ->* B) _).
Local Notation "1" := pequiv_pmap_idmap.

Require Import pYoneda.

Section Assoc.

Context `{Funext}.

Theorem pequiv_smash_assoc (A B C : pType)
  : (A ∧ B) ∧ C <~>* A ∧ (B ∧ C).
Proof.
  serapply pYoneda.
  2: shelve.
  intro X.
  refine (_ o*E pequiv_smash_adj).
  refine (_ o*E pequiv_functor_pmap 1 pequiv_smash_adj).
  refine (_ o*E pequiv_smash_adj^-1*).
  apply pequiv_smash_adj^-1*.
  Unshelve.
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