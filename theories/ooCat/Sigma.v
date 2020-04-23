(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.
Require Import ooCat.Cat1.

Generalizable Variables m n A B.

(** * Sigma oo-categories of displayed oo-categories *)

CoFixpoint isglob_sigma `{IsDGlob n A m B}
  : IsGlob m (sig B).
Proof.
  unshelve econstructor.
  - intros [a u] [b v]; exact { f : a $-> b & DHom f u v }.
  - intros [a u] [b v]; exact _.
Defined.

Global Existing Instance isglob_sigma.

CoFixpoint isfunctor0_pr1 `{IsDGlob n A m B}
  : IsFunctor0 (@pr1 A B).
Proof.
  snrapply Build_IsFunctor0.
  1: intros x y; exact pr1.
  intros x y.
  rapply isfunctor0_pr1.
Defined.

Global Existing Instance isfunctor0_pr1.

CoFixpoint iscat0_sigma `{IsDCat0 n A m B}
  : IsCat0 m (sig B).
Proof.
  unshelve econstructor.
  - intros [a u] [b v] [c w] [g q] [f p].
    exists (g $o f).
    exact (q $oD p).
  - intros [a u].
    exists (cat_id a).
    exact (dcat_id u).
  - intros [a u] [b v] [c w] [g q].
Abort.

(* Global Existing Instance iscat0_sigma. *)
