From HoTT Require Import Basics Types.Paths Types.Prod Types.Universe.
From HoTT Require Import Classes.interfaces.abstract_algebra.
From HoTT Require Import Pointed.Core Pointed.pSusp Spaces.Spheres.
From HoTT Require Import Homotopy.HSpace.Core Homotopy.HSpaceS1.
From HoTT Require Import Homotopy.CayleyDickson Homotopy.Join.Core.
From HoTT Require Import Homotopy.Join.SuspDiamond.
From HoTT Require Import Homotopy.HSpaceS7.LeftScalar Homotopy.HSpaceS7.RightScalar.

Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.
Module R := S7RightScalar.

(** The parameter and maps work for arbitrary commutative associative spheroids. *)
Section Scalars.
  Universe u.
  Context {X : pType@{u}} `{CayleyDicksonSpheroid X}
    `{!Associative (@hspace_op X _)} `{!Commutative (@hspace_op X _)}.

  Example right_parameter (s a b c d : X)
    : cd_diamond_parameter ((-b) * conj s) (a * s) c d
      = -cd_diamond_parameter a b c d
    := R.parameter s a b c d.
  Example right_map_l (s a c t : X)
    : cd_diamond_map_l a c t * s = cd_diamond_map_r (a * s) c (-t)
    := R.map_l s a c t.
  Example right_map_r (s b c t : X)
    : (-cd_diamond_map_r b c t) * conj s
      = cd_diamond_map_l ((-b) * conj s) c (-t)
    := R.map_r s b c t.
End Scalars.

(** The actual filler theorem is not circle-specific and does not assume extensionality, connectedness, or truncation. *)
Section Suspension.
  Universe u.
  Context {A : Type@{u}} `{CayleyDicksonImaginaroid A}
    `{!Associative (@hspace_op (psusp A) _)}
    `{!Commutative (@hspace_op (psusp A) _)}.
  Local Notation X := (psusp A).
  Local Instance scalar_op : SgOp X := @hspace_op X (@cdi_susp_hspace A H).
  Local Notation conj := (conjugate_susp A cdi_negate).
  Local Notation D := (cd_op_diamond (H:=cds_susp_cdi _)).

  Example actual_right_diamond (s a b c d : X)
    : transport011
        (fun x : X * X => fun y : X * X =>
          zigzag@{u u u} (fst x) (snd x) (fst y)
            = zigzag@{u u u} (fst x) (snd x) (snd y))
        (path_prod' (R.e10 s b c) (R.e01 s a b c d))
        (path_prod' (R.e00 s a c) (R.e11 s a b c d))
        (join_diamond_turn (.* s) (fun t => (-t) * conj s) (D a b c d)^)
      = (D ((-b) * conj s) (a * s) c d)^
    := R.diamond s a b c d.
End Suspension.

(** Specialization uses the same small circle data as the executable outline. *)
Local Existing Instances S7LeftScalar.circle_imaginaroid
  S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative
  S7LeftScalar.circle_commutative.
Local Set Universe Minimization ToSet.
Section Circle.
  Context `{Univalence}.
  Local Notation C := (Sphere 1).
  Local Notation D := (cd_op_diamond (X:=psphere 1)).

  Example circle_right_diamond (s a b c d : C)
    : transport011
        (fun x : C * C => fun y : C * C =>
          zigzag@{Set Set Set} (fst x) (snd x) (fst y)
            = zigzag (fst x) (snd x) (snd y))
        (path_prod' (R.e10 s b c) (R.e01 s a b c d))
        (path_prod' (R.e00 s a c) (R.e11 s a b c d))
        (join_diamond_turn (.* s) (fun t => (-t) * conj s) (D a b c d)^)
      = (D ((-b) * conj s) (a * s) c d)^
    := R.diamond s a b c d.
End Circle.
