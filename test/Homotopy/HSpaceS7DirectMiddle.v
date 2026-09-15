From HoTT Require Import Basics Types.Paths Types.Universe.
From HoTT Require Import Pointed.Core Spaces.Spheres.
From HoTT Require Import Homotopy.CayleyDickson Homotopy.Suspension.
From HoTT Require Import Homotopy.Join.Core.
From HoTT Require Import Homotopy.HSpaceS7.LeftScalar.
From HoTT Require Import Homotopy.HSpaceS7.MiddleScalar.
From HoTT Require Import Homotopy.HSpaceS7.RightScalar.
From HoTT Require Import Homotopy.HSpaceS7.Direct.

Local Set Universe Minimization ToSet.
Local Open Scope pointed_scope.
Local Open Scope path_scope.
Module D := S7DirectGluing.

Section GenericChecks.
  Context {X T : Type} {f g : X -> T} {x0 x1 : X} (r : x0 = x1).
  Context (A B M : f == g).
  Context (h : forall x, A x = M x) (k : forall x, B x = M x).

  Example exact_ratio_computation
    : adjusted_naturality_comparison r A B (M x0) (M x1)
        (h x0) (h x1) (k x0) (k x1)
        (fun x => h x @ (k x)^) 1 1
      = adjusted_naturality_homotopic r A M h
        @ (adjusted_naturality_homotopic r B M k)^
    := adjusted_naturality_comparison_homotopic r A B M h k
      (fun x => h x @ (k x)^) (fun x => 1).
End GenericChecks.

(** This checks propagation of an explicitly supplied relative associator comparison. It does not construct that geometric comparison or claim an unconditional mixed filler. *)
Section ChosenMiddleChecks.
  Universe u.
  Context `{Univalence}.
  Local Existing Instances S7LeftScalar.circle_imaginaroid
    S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative
    S7LeftScalar.circle_commutative S7LeftScalar.circle_connected
    S7LeftScalar.circle_truncated.

  Local Notation C := (Sphere 1).
  Local Notation J := (Join@{Set Set Set} C C).
  Local Notation BL := (S7LeftScalar.first_l@{u} cd_diamond_susp).
  Local Notation BR := (S7RightScalar.first_r@{u}).
  Local Notation BM := (S7MiddleScalar.middle_l@{u} cd_diamond_susp).
  Context (c d : C).
  Context (Q : forall x y : J,
    D.eta_associator c d x y = D.eta_associator North d x y).
  Context (Ql : forall (a : C) (y : J), Q (joinl a) y
    = D.eta_overlap_l@{u} a c d y
      @ (D.eta_overlap_l@{u} a North d y)^).
  Context (Qr : forall (b : C) (y : J), Q (joinr b) y
    = D.eta_overlap_r@{u} b c d y
      @ (D.eta_overlap_r@{u} b North d y)^).
  Context (Qm : forall (s : C) (x : J), Q x (joinl s)
    = D.eta_overlap_m@{u} s c d x
      @ (D.eta_overlap_m@{u} s North d x)^).
  Context (Qlm : forall a s : C, Ql a (joinl s) = Qm s (joinl a)).
  Context (Qrm : forall b s : C, Qr b (joinl s) = Qm s (joinr b)).

  Let K (a b : C) (y : J)
    : D.eta_face@{u} a b c d y = D.eta_face@{u} a b North d y
    := adjusted_naturality_comparison (jglue a b)
      (fun x => D.eta_associator c d x y)
      (fun x => D.eta_associator North d x y)
      (BL a y (joinr d)) (BR b y (joinr d))
      (D.eta_overlap_l@{u} a c d y) (D.eta_overlap_r@{u} b c d y)
      (D.eta_overlap_l@{u} a North d y)
      (D.eta_overlap_r@{u} b North d y)
      (fun x => Q x y) (Ql a y) (Qr b y).

  Example specified_middle_boundary (a b s : C)
    : K a b (joinl s)
      = D.eta_face_middle@{u} a b s c d
        @ (D.eta_face_middle@{u} a b s North d)^.
  Proof.
    unfold K.
    lhs napply (ap011
      (fun ql qr => adjusted_naturality_comparison (jglue a b)
        (fun x => D.eta_associator c d x (joinl s))
        (fun x => D.eta_associator North d x (joinl s))
        (BL a (joinl s) (joinr d)) (BR b (joinl s) (joinr d))
        (D.eta_overlap_l@{u} a c d (joinl s))
        (D.eta_overlap_r@{u} b c d (joinl s))
        (D.eta_overlap_l@{u} a North d (joinl s))
        (D.eta_overlap_r@{u} b North d (joinl s))
        (fun x => Q x (joinl s)) ql qr) (Qlm a s) (Qrm b s)).
    exact (adjusted_naturality_comparison_homotopic (jglue a b)
      (fun x => D.eta_associator c d x (joinl s))
      (fun x => D.eta_associator North d x (joinl s))
      (fun x => BM s x (joinr d))
      (D.eta_overlap_m@{u} s c d) (D.eta_overlap_m@{u} s North d)
      (fun x => Q x (joinl s)) (Qm s)).
  Defined.

  Example relative_comparison_to_original (a b s t : C)
    : D.Mixed@{u} a b s t c d
    := D.equiv_mixed_eta@{u} a b s t c d
      (moveL_Vp _ _ _ (D.eta_edge_comparison_of_section@{u}
        a b c d (K a b) (specified_middle_boundary a b) s t))^.
End ChosenMiddleChecks.
