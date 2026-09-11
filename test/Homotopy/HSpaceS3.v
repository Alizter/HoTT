From HoTT Require Import Basics Types.Universe.
From HoTT Require Import Pointed.Core Spaces.Spheres.
From HoTT Require Import Homotopy.HSpace.Core Homotopy.HSpaceS1.
From HoTT Require Import Homotopy.HSpaceS3.

Example sphere_is_small (n : trunc_index) : Type0 := Sphere@{} n.

Example circle_hspace_is_small : IsHSpace@{Set} (psphere@{} 1)
  := hspace_s1@{}.

(** No diamond or doubled associativity needs to be supplied. *)
Example sphere_three_hspace `{Univalence}
  : IsHSpace@{Set} (psphere@{} 3) := _.
