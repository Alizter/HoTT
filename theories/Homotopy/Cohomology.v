Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import abstract_algebra.
Require Import EMSpace.

Local Open Scope pointed_scope.

Definition Cohomology (n : nat) (X : pType) (G : Type) `{AbGroup G}
  := Tr 0 (X ->* K(G, n)).

Section Cohomology.

Context (n : nat) (X : pType) (G : Type) `{AbGroup G}.


Global Instance group_cohomology (n : nat) (X : pType) (G : Type) `{AbGroup G}
  : AbGroup (Cohomology n X G).