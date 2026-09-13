From HoTT Require Import Basics Types.Universe.
From HoTT Require Import Classes.interfaces.abstract_algebra.
From HoTT Require Import Pointed.Core Spaces.Spheres.
From HoTT Require Import Homotopy.HSpace.Core Homotopy.HSpaceS1.
From HoTT Require Import Homotopy.HSpaceS3 Homotopy.HSpaceS7.
From HoTT Require Import Homotopy.CayleyDickson Homotopy.Suspension.
From HoTT Require Import Homotopy.Join.Core.

Local Set Universe Minimization ToSet.
Local Open Scope pointed_scope.
Local Open Scope path_scope.

Module O := S7ProofOutline.

(** Test the actual outline in [theories/Homotopy/HSpaceS7.v], not a second implementation of the assembly. The four remaining open comparisons are explicit parameters; the left row uses the proved comparison. *)
Section OutlineChecks.
  Context `{Univalence}.
  Local Existing Instances S7LeftScalar.circle_imaginaroid
    S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative
    S7LeftScalar.circle_commutative S7LeftScalar.circle_connected
    S7LeftScalar.circle_truncated.

  Local Notation C := (Sphere 1).
  Local Notation J := (Join@{Set Set Set} C C).
  Local Notation mu := (cd_op@{Set} (X:=psphere 1)).
  Local Notation AL := (cd_assoc_last_joinl@{Set} (X:=psphere 1)).
  Local Notation AR := (cd_assoc_last_joinr_transport@{Set} (X:=psphere 1)).
  Local Notation T := (cd_assoc_last_transport@{Set} (X:=psphere 1)).
  Local Notation ell :=
    ((merid (North : Sphere 0) @ (merid South)^) : (North = North :> C)).
  Local Notation m_ll := O.m_ll.
  Local Notation m_lr := O.m_lr.
  Local Notation m_rl := O.m_rl.
  Local Notation m_rr := O.m_rr.

  Let M (x y : J) (d : C) := ap (T x y d) ell = 1.

  Local Notation loop_y_joinl :=
    (fun a b b' d => S7LeftScalar.loop_y_joinl
      cd_diamond_susp a b b' d ell).

  Context
    (loop_y_joinr : forall a b b' d : C,
      transport (fun y => M (joinr a) y d) (jglue b b') (m_rl a b d)
        = m_rr a b' d)
    (loop_x_joinl : forall a a' b d : C,
      transport (fun x => M x (joinl b) d) (jglue a a') (m_ll a b d)
        = m_rl a' b d)
    (loop_x_joinr : forall a a' b d : C,
      transport (fun x => M x (joinr b) d) (jglue a a') (m_lr a b d)
        = m_rr a' b d).

  Let row_l := O.loop_row_l.
  Let row_r := O.loop_row_r loop_y_joinr.

  Context (loop_mixed : forall a a' b b' d : C,
    transport (O.XGlue loop_y_joinr a a' d) (jglue b b')
      (loop_x_joinl a a' b d) = loop_x_joinr a a' b' d).

  Let column := O.loop_column loop_y_joinr
    loop_x_joinl loop_x_joinr loop_mixed.
  Let loops := O.all_scalar_loops loop_y_joinr
    loop_x_joinl loop_x_joinr loop_mixed.
  Let glue := O.last_glue loop_y_joinr
    loop_x_joinl loop_x_joinr loop_mixed.
  Let assoc := O.associator loop_y_joinr
    loop_x_joinl loop_x_joinr loop_mixed.

  Example loops_ll (a b d : C)
    : loops (joinl a) (joinl b) d = m_ll a b d := idpath.
  Example loops_lr (a b d : C)
    : loops (joinl a) (joinr b) d = m_lr a b d := idpath.
  Example loops_rl (a b d : C)
    : loops (joinr a) (joinl b) d = m_rl a b d := idpath.
  Example loops_rr (a b d : C)
    : loops (joinr a) (joinr b) d = m_rr a b d := idpath.

  Example row_l_glue (a b b' d : C)
    : apD (row_l a d) (jglue b b') = loop_y_joinl a b b' d.
  Proof.
    exact (Join_ind_beta_jglue _ _ _ _ b b').
  Defined.
  Example row_r_glue (a b b' d : C)
    : apD (row_r a d) (jglue b b') = loop_y_joinr a b b' d.
  Proof.
    exact (Join_ind_beta_jglue _ _ _ _ b b').
  Defined.
  Example column_mixed (a a' b b' d : C)
    : apD (column a a' d) (jglue b b') = loop_mixed a a' b b' d.
  Proof.
    exact (Join_ind_beta_jglue _ _ _ _ b b').
  Defined.
  Example full_x_glue (a a' d : C) (y : J)
    : apD (fun x => loops x y d) (jglue a a') = column a a' d y.
  Proof.
    exact (Join_ind_beta_jglue _ _ _ _ a a').
  Defined.

  Example second_circle_coherence (x y : J)
    : transport (M x y) ell (loops x y North) = loops x y North
    := apD (loops x y) ell.
  Example last_glue_unit_left (x y : J) (d : C)
    : glue x y North d = 1 := idpath.
  Example associator_left (x y : J) (c : C)
    : assoc x y (joinl c) = AL x y c := idpath.
  Example associator_right (x y : J) (d : C)
    : assoc x y (joinr d) = AR x y d := idpath.
  Example associator_glue (x y : J) (c d : C)
    : apD (assoc x y) (jglue c d) = glue x y c d.
  Proof.
    exact (Join_ind_beta_jglue _ _ _ _ c d).
  Defined.

  Example associativity_orientation (x y z : J)
    : O.associative_cd_s1_from_gaps loop_y_joinr
        loop_x_joinl loop_x_joinr loop_mixed x y z = (assoc x y z)^
    := idpath.
  Example conditional_s7_small : IsHSpace@{Set} (psphere 7)
    := O.hspace_s7_from_gaps loop_y_joinr
         loop_x_joinl loop_x_joinr loop_mixed.
End OutlineChecks.
