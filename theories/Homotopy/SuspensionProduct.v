Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import Smash.
Require Import Wedge.
Require Import HIT.Suspension.

Local Open Scope pointed_scope.

(* We can characterise the suspenson of a product in the following way *)
Theorem susp_product {X Y : pType}
  : psusp (X * Y) <~>* (psusp X) V (psusp Y) V (psusp (Smash X Y)).
Proof.
  serapply pequiv_adjointify'.
  { serapply Build_pMap.
    { serapply Susp_rec.
      { apply winl.
        apply winl.
        erapply point. }
      { apply winl.
        apply winr.
        erapply point. }
      intros [x y].
      cbn.
      apply ap.
      refine wpp. }
    reflexivity. }
  { serapply Wedge_rec'.
    { serapply Wedge_rec'.
      { apply psusp_functor.
(*         serapply Build_pMap. *)
(*         1: intro; exact (point X, point Y). *)
        refine (Build_pMap X (X * Y) (fun x : X => pair x (point Y)) _).
        reflexivity. }
      { apply psusp_functor.
(*         serapply Build_pMap. *)
(*         1: intro; exact (point X, point Y). *)
        refine (Build_pMap Y (X * Y) (pair (point X)) _).
        reflexivity. } }
    apply psusp_functor.
    serapply Build_pMap.
    { serapply smash_rec'.
      { intros x y; erapply point. }
      all: reflexivity. }
    reflexivity. }
  { cbn.
    serapply Wedge_ind.
    { serapply Wedge_ind.
      { serapply Susp_ind.
        1: reflexivity.
        { cbn beta.
          simpl.
          apply ap.
          symmetry.
Admitted.