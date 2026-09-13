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
  S7LeftScalar.circle_commutative S7LeftScalar.circle_connected
  S7LeftScalar.circle_truncated.
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
  (** These are transparent coherence constructions, not opaque proof closures. *)
  Local Transparent R.first_r_glue_glue R.overlap_glue R.loop_y_joinr.
  Local Notation J := (Join@{Set Set Set} C C).

  Example standard_00 (s a c : C)
    : (R.e00 s a c)^ = cd_assoc_ll_scalar_r (X:=psphere 1) a c s
    := R.standard_00 s a c.
  Example standard_01 (s a b c d : C)
    : (R.e01 s a b c d)^ = cd_assoc_lr_scalar_r (X:=psphere 1) a d s
    := R.standard_01 s a b c d.
  Example standard_10 (s b c : C)
    : (R.e10 s b c)^ = cd_assoc_rl_scalar_r (X:=psphere 1) b c s
    := R.standard_10 s b c.
  Example standard_11 (s a b c d : C)
    : (R.e11 s a b c d)^ = cd_assoc_rr_scalar_r (X:=psphere 1) b d s
    := R.standard_11 s a b c d.

  Example first_right_small (s : C) (y z : J)
    : cd_op@{Set} (X:=psphere 1) (cd_op (joinr s) y) z
      = cd_op (joinr s) (cd_op y z)
    := R.first_r s y z.
  Example first_right_row_l (s a : C) (z : J)
    : R.first_r s (joinl a) z
      = cd_assoc_first_rl@{Set} (X:=psphere 1) s a z := idpath.
  Example first_right_row_r (s b : C) (z : J)
    : R.first_r s (joinr b) z
      = cd_assoc_first_rr@{Set} (X:=psphere 1) s b z := idpath.
  Example first_right_glue (s a b : C) (z : J)
    : concat_Ap (fun y => R.first_r s y z) (jglue a b)
      = R.first_r_glue s a b z.
  Proof.
    exact (Join_ind_FlFr_beta_jglue _ _ _ _ _ a b).
  Defined.
  Example first_right_glue_l (s a b c : C)
    : R.first_r_glue s a b (joinl c) = R.first_r_glue_l s a b c := idpath.
  Example first_right_glue_r (s a b d : C)
    : R.first_r_glue s a b (joinr d) = R.first_r_glue_r s a b d := idpath.
  Example first_right_mixed (s a b c d : C)
    : apD (R.first_r_glue s a b) (jglue c d) = R.first_r_glue_glue s a b c d.
  Proof.
    exact (Join_ind_beta_jglue _ _ _ _ c d).
  Defined.
  Example overlap_row_l (s a c : C)
    : R.overlap s (joinl a) c
      = cd_assoc_last_joinl_first_rl@{Set} (X:=psphere 1) s a c := idpath.
  Example overlap_row_r (s b c : C)
    : R.overlap s (joinr b) c
      = cd_assoc_last_joinl_first_rr@{Set} (X:=psphere 1) s b c := idpath.
  Example loop_row_l (s a d : C) {c : C} (p : c = c)
    : R.row_loop s d (joinl a) p
      = cd_assoc_last_transport_loop_rl@{Set} (X:=psphere 1) s a d p
    := idpath.
  Example loop_row_r (s b d : C) {c : C} (p : c = c)
    : R.row_loop s d (joinr b) p
      = cd_assoc_last_transport_loop_rr@{Set} (X:=psphere 1) s b d p
    := idpath.
  Example right_row_glue (s a b d : C) {c : C} (p : c = c)
    : transport (fun y =>
        ap (cd_assoc_last_transport@{Set} (X:=psphere 1) (joinr s) y d) p = 1)
        (jglue a b) (cd_assoc_last_transport_loop_rl@{Set} s a d p)
      = cd_assoc_last_transport_loop_rr@{Set} s b d p
    := R.loop_y_joinr s a b d p.
End Circle.
