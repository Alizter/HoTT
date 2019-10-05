Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import Coherence.
Require Import pMapFunctor.

(* The yoneda lemma for pointed types. *)

Local Open Scope pointed_scope.

Local Notation id := pmap_idmap.

Lemma pYoneda (A B : pType) (phi : forall X, (B ->* X) <~>* (A ->* X))
  {p : IsNatural phi} : A <~>* B.
Proof.
  set (to := phi B id).
  set (fr := (phi A)^-1 id).
  destruct p as [p].
  serapply (pequiv_adjointify to fr).

Admitted.