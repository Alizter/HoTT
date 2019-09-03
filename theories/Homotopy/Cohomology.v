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

Global Instance sgop_cohomology : SgOp (Cohomology n X G).
Proof.
Admitted.

Global Instance monunit_cohomology : MonUnit (Cohomology n X G).
Proof.
  apply tr.
  apply pmap_const.
Defined.

Global Instance negate_cohomology : Negate (Cohomology n X G).
Proof.
Admitted.

Global Instance group_cohomology : AbGroup (Cohomology n X G).
Proof.
Admitted.