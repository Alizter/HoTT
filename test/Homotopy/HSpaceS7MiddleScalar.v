From HoTT Require Import Basics Types.Universe.
From HoTT Require Import Classes.interfaces.abstract_algebra.
From HoTT Require Import Pointed.Core Spaces.Spheres.
From HoTT Require Import Homotopy.CayleyDickson Homotopy.Join.Core.
From HoTT Require Import Homotopy.HSpaceS7.LeftScalar Homotopy.HSpaceS7.MiddleScalar.

Local Set Universe Minimization ToSet.
Local Open Scope pointed_scope.
Local Open Scope path_scope.

Module M := S7MiddleScalar.

Section ChosenDiamond.
  Context `{Univalence}.
  Local Existing Instances S7LeftScalar.circle_imaginaroid
    S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative
    S7LeftScalar.circle_commutative S7LeftScalar.circle_connected
    S7LeftScalar.circle_truncated.
  Context (D : CayleyDicksonDiamond (psphere 1) (-)).
  Local Existing Instance D.
  Local Notation C := (Sphere 1).
  Local Notation J := (Join@{Set Set Set} C C).

  Example middle_left_small (s : C) (x z : J)
    : cd_op@{Set} (X:=psphere 1) (cd_op x (joinl s)) z
      = cd_op x (cd_op (joinl s) z)
    := M.middle_l D s x z.

  Example middle_left_row_l (a s : C) (z : J)
    : M.middle_l D s (joinl a) z
      = cd_assoc_first_ll@{Set} (X:=psphere 1) a s z := idpath.
  Example middle_left_row_r (b s : C) (z : J)
    : M.middle_l D s (joinr b) z
      = cd_assoc_first_rl@{Set} (X:=psphere 1) b s z := idpath.

  Example middle_left_glue (s a b : C) (z : J)
    : concat_Ap (fun x => M.middle_l D s x z) (jglue a b)
      = M.middle_l_glue D s a b z.
  Proof.
    exact (Join_ind_FlFr_beta_jglue _ _ _ _ _ a b).
  Defined.
  Example middle_left_glue_l (s a b c : C)
    : M.middle_l_glue D s a b (joinl c) = M.middle_l_glue_l D s a b c
    := idpath.
  Example middle_left_glue_r (s a b d : C)
    : M.middle_l_glue D s a b (joinr d) = M.middle_l_glue_r D s a b d
    := idpath.
  Example middle_left_mixed (s a b c d : C)
    : apD (M.middle_l_glue D s a b) (jglue c d)
      = M.middle_l_glue_glue D s a b c d.
  Proof.
    exact (Join_ind_beta_jglue _ _ _ _ c d).
  Defined.

  (** Both the overlap and the nullhomotopy retain the original witnesses, not merely parallel paths. *)
  Example overlap_row_l (s a c : C)
    : M.overlap D s (joinl a) c
      = cd_assoc_last_joinl_first_ll@{Set} (X:=psphere 1) a s c
    := idpath.
  Example overlap_row_r (s b c : C)
    : M.overlap D s (joinr b) c
      = cd_assoc_last_joinl_first_rl@{Set} (X:=psphere 1) b s c
    := idpath.
  Example loop_column_l (s a d : C) {c : C} (p : c = c)
    : M.column_loop D s d (joinl a) p
      = cd_assoc_last_transport_loop_ll@{Set} (X:=psphere 1) a s d p
    := M.column_loop_l D s a d p.
  Example loop_column_r (s b d : C) {c : C} (p : c = c)
    : M.column_loop D s d (joinr b) p
      = cd_assoc_last_transport_loop_rl@{Set} (X:=psphere 1) b s d p
    := M.column_loop_r D s b d p.
  Example left_column_glue (a b s d : C) {c : C} (p : c = c)
    : transport (fun x =>
        ap (cd_assoc_last_transport@{Set} (X:=psphere 1)
          x (joinl s) d) p = 1) (jglue a b)
        (cd_assoc_last_transport_loop_ll@{Set} a s d p)
      = cd_assoc_last_transport_loop_rl@{Set} b s d p
    := M.loop_x_joinl D a b s d p.
End ChosenDiamond.
