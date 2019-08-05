Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import Smash.

Require Import Bifunctor.
Require Import Associator.

Local Open Scope pointed_scope.

Local Notation id := pmap_idmap.
Local Notation α := pequiv_smash_assoc.

Theorem smash_pentagon (A B C D : pType)
  : α A B (C ∧ D) o* α (A ∧ B) C D
  ==* (id [∧] (α B C D) o* α A (B ∧ C) D) o* (α A B C) [∧] id.
Proof.
Admitted.
