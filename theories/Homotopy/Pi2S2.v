Require Import Basics.
Require Import Types.
Require Import Pointed.

Require Import Spaces.Int.

Require Import HomotopyGroup.
Require Import HIT.Spheres.


(** Calculation of Pi 2 S2 *)

Section Pi2S2.

  Context `{Univalence}.

  (* Use licata_finster and HSpace on S1 *)
  Theorem Pi2S2 : Pi 2 (psphere 2) <~> Int.
  Proof.
  Admitted.

End Pi2S2.