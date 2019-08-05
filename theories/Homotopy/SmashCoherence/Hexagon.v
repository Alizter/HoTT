Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import Smash.

Require Import Bifunctor.
Require Import Associator.
Require Import Symmetry.

Local Open Scope pointed_scope.

Local Notation id := pmap_idmap.
Local Notation α := pequiv_smash_assoc.
Local Notation σ := pequiv_smash_symm.

Theorem smash_hexagon (A B C : pType)
  : (α B C A o* σ A (B ∧ C)) o* α A B C
  ==* (id [∧] (σ A C) o* α B A C) o* (σ A B) [∧] id.
Proof.
Admitted.
