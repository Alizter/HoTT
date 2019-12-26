Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import Homotopy.Suspension.
Require Import HIT.Spheres.

Local Open Scope pointed_scope.

Definition base {n : nat} : psphere n.
Proof.
  destruct n; exact North.
Defined.

Definition loop {n : nat} : iterated_loops n (psphere n).
Proof.
  induction n.
  1: exact South.
  apply unfold_iterated_loops'.
  revert IHn.
  apply iterated_loops_functor.
  apply loop_susp_unit.
Defined.

Notation pt := (point _).

(** Dependent iterated loops *)
Definition dloops (n : nat) {A : pType} (P : A -> Type)
  (p : iterated_loops n A) : pType.
Proof.
  induction n.
  + serapply Build_pType.
    - apply P, p.
    - simpl in *.
Admitted.

Context `{Funext}.

Definition psphere_rec {n : nat} (P : pType) (l : iterated_loops n P)
  : psphere n ->* P.
Proof.
  serapply Build_pMap.
  { revert P l.
    induction n.
    + intros P l.
      exact (Susp_rec pt l (Empty_ind _)).
    + intros P l.
      change (psusp (psphere n) -> P).
      serapply Susp_rec.
      1,2: exact pt.
      serapply (IHn (loops P)).
      apply unfold_iterated_loops'.
      exact l. }
  destruct n; reflexivity.
Defined.

Definition psphere_ind {n : nat} (P : psphere n -> Type) (b : P base)
  (l : dloops n P loop) (x : psphere n) : P x.
Proof.
Admitted.


