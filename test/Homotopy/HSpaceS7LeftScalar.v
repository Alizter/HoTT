From HoTT Require Import Basics Types.Universe.
From HoTT Require Import Classes.interfaces.abstract_algebra.
From HoTT Require Import Pointed.Core Spaces.Spheres.
From HoTT Require Import Modalities.ReflectiveSubuniverse Truncations.Core.
From HoTT Require Import Homotopy.HSpace.Core Homotopy.HSpaceS1 Homotopy.HSpaceS3.
From HoTT Require Import Homotopy.CayleyDickson Homotopy.Join.Core.
From HoTT Require Import Homotopy.HSpaceS7.LeftScalar Homotopy.Suspension.

Local Set Universe Minimization ToSet.
Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.

Module L := S7LeftScalar.

(** The algebraic filler comparison remains universe-polymorphic and needs no extensionality. *)
Section PolynomialTranslation.
  Context {X : pType@{u}} `{CayleyDicksonSpheroid X}
    `{!Associative (@hspace_op X _)}
    (D : CayleyDicksonDiamond X (-))
    `{!Commutative (@hspace_op X _)}.
  Check (fun r a b c d : X => @L.left_diamond@{u} X _ _ D _ r a b c d).
End PolynomialTranslation.

Section ChosenDiamond.
  Context `{Univalence}.

  (** The shared witnesses are the usual circle data, with their universe instances fixed. Check this before registering them locally. *)
  Example scalar_spheroid
    : L.circle_spheroid = (_ : CayleyDicksonSpheroid (psphere 1))
    := idpath.
  Example scalar_associative
    : L.circle_associative = (_ : Associative sgop_s1) := idpath.
  Example scalar_commutative
    : L.circle_commutative = (_ : Commutative sgop_s1) := idpath.
  Example scalar_connected
    : L.circle_connected = (_ : IsConnected (0%trunc) (psphere 1))
    := idpath.
  Example scalar_truncated
    : L.circle_truncated = (_ : IsTrunc 1 (psphere 1)) := idpath.

  Local Existing Instances L.circle_imaginaroid L.circle_spheroid
    L.circle_associative L.circle_commutative L.circle_connected
    L.circle_truncated.
  Context (D : CayleyDicksonDiamond (psphere 1) (-)).
  Local Existing Instance D.
  Local Notation C := (Sphere 1).
  Local Notation J := (Join@{Set Set Set} C C).

  (** The partial associator works for the supplied diamond, not just the canonical suspension diamond. *)
  Example first_left_small (a : C) (y z : J)
    : cd_op@{Set} (X:=psphere 1) (cd_op (joinl a) y) z
      = cd_op (joinl a) (cd_op y z)
    := L.first_l D a y z.

  Example first_left_row_l (a b : C) (z : J)
    : L.first_l D a (joinl b) z
      = cd_assoc_first_ll@{Set} (X:=psphere 1) a b z := idpath.
  Example first_left_row_r (a b : C) (z : J)
    : L.first_l D a (joinr b) z
      = cd_assoc_first_lr@{Set} (X:=psphere 1) a b z := idpath.

  Example first_left_glue (a b b' : C) (z : J)
    : concat_Ap (fun y => L.first_l D a y z) (jglue b b')
      = L.first_l_glue D a b b' z.
  Proof.
    exact (Join_ind_FlFr_beta_jglue _ _ _ _ _ b b').
  Defined.
  Example first_left_glue_l (a b b' c : C)
    : L.first_l_glue D a b b' (joinl c) = L.first_l_glue_l D a b b' c
    := idpath.
  Example first_left_glue_r (a b b' d : C)
    : L.first_l_glue D a b b' (joinr d) = L.first_l_glue_r D a b b' d
    := idpath.
  Example first_left_mixed (a b b' c d : C)
    : apD (L.first_l_glue D a b b') (jglue c d)
      = L.first_l_glue_glue D a b b' c d.
  Proof.
    exact (Join_ind_beta_jglue _ _ _ _ c d).
  Defined.

  (** The overlap and loop comparison have no additional coherence inputs. *)
  Example overlap_row_l (s a c : C)
    : L.overlap D s (joinl a) c
      = cd_assoc_last_joinl_first_ll@{Set} (X:=psphere 1) s a c
    := idpath.
  Example overlap_row_r (s b c : C)
    : L.overlap D s (joinr b) c
      = cd_assoc_last_joinl_first_lr@{Set} (X:=psphere 1) s b c
    := idpath.
  Example loop_row_l (s a d : C)
    : L.row_loop D s d (joinl a) (merid North @ (merid South)^)
      = cd_assoc_last_transport_loop_ll@{Set} (X:=psphere 1) s a d
          (merid North @ (merid South)^)
    := L.row_loop_l D s a d (merid North @ (merid South)^).
  Example loop_row_r (s b d : C) {c : C} (p : c = c)
    : L.row_loop D s d (joinr b) p
      = cd_assoc_last_transport_loop_lr@{Set} (X:=psphere 1) s b d p
    := L.row_loop_r D s b d p.
  Example left_loop_glue (s a b d : C) {c : C} (p : c = c)
    : transport (fun y =>
        ap (cd_assoc_last_transport@{Set} (X:=psphere 1)
          (joinl s) y d) p = 1) (jglue a b)
        (cd_assoc_last_transport_loop_ll@{Set} s a d p)
      = cd_assoc_last_transport_loop_lr@{Set} s b d p
    := L.loop_y_joinl D s a b d p.
End ChosenDiamond.
