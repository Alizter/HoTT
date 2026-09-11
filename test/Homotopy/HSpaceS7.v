From HoTT Require Import Basics Types.Universe.
From HoTT Require Import Pointed.Core Spaces.Spheres.
From HoTT Require Import Homotopy.HSpace.Core Homotopy.HSpaceS1.
From HoTT Require Import Homotopy.HSpaceS3 Homotopy.HSpaceS7.
From HoTT Require Import Homotopy.Join.Core Homotopy.CayleyDickson.

(** The full rectangle family is still a required input. *)
Example sphere_seven_hspace_conditional `{Univalence}
  (h : forall (a b : Sphere 1) (u v : Join (Sphere 1) (Sphere 1)),
    cd_associativity_rectangle (X:=psphere 1) a b u v)
  : IsHSpace@{Set} (psphere 7) := hspace_s7_from_rectangle h.
