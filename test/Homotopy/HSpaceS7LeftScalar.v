From HoTT Require Import Basics Types.Universe.
From HoTT Require Import Classes.interfaces.abstract_algebra.
From HoTT Require Import Pointed.Core Spaces.Spheres.
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

  (** This remains a conditional test of the overlap reduction, not a proof of the missing comparison. *)
  Context (q : forall s a b c : C,
    concat_Ap (fun y => cd_assoc_last_joinl@{Set} (X:=psphere 1) (joinl s) y c)
        (jglue a b) @ (cd_assoc_last_joinl_first_ll@{Set} s a c @@ 1)
      = (1 @@ cd_assoc_last_joinl_first_lr@{Set} s b c)
        @ L.first_l_glue_l D s a b c).

  Example conditional_loop_row_l (s a d : C)
    : L.row_loop D q s d (joinl a) (merid North @ (merid South)^)
      = cd_assoc_last_transport_loop_ll@{Set} (X:=psphere 1) s a d
          (merid North @ (merid South)^)
    := L.row_loop_l D q s a d (merid North @ (merid South)^).
  Example conditional_loop_row_r (s b d : C) {c : C} (p : c = c)
    : L.row_loop D q s d (joinr b) p
      = cd_assoc_last_transport_loop_lr@{Set} (X:=psphere 1) s b d p
    := L.row_loop_r D q s b d p.
  Check (L.loop_y_joinl_from_overlap D q).
End ChosenDiamond.
