From HoTT Require Import Basics Types.Universe.
From HoTT Require Import Classes.interfaces.abstract_algebra Spaces.Spheres.
From HoTT Require Import Homotopy.CayleyDickson Homotopy.HSpaceS1 Homotopy.HSpaceS3.
Local Set Universe Minimization ToSet.
Module Probe.
#[local] Monomorphic Instance circle_imaginaroid `{Univalence}
  : CayleyDicksonImaginaroid (Sphere 0) := cdi_s0.
Definition diamond_arg `{Univalence}
  `(D0 : CayleyDicksonDiamond (psphere 1) (-))
  := cd_op (X:=psphere 1).
End Probe.
