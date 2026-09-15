From HoTT Require Import Basics.
Require Import Types.Universe.
Require Import Classes.interfaces.canonical_names.
Require Import Pointed.Core Spaces.Spheres.
Require Import Homotopy.HSpace.Core Homotopy.CayleyDickson Homotopy.Suspension.
Require Import Homotopy.Join.Core Homotopy.Join.Rec2.
Require Import Homotopy.HSpaceS7.LeftScalar Homotopy.HSpaceS7.MiddleScalar.
Require Import Homotopy.HSpaceS7.RightScalar.

Local Set Universe Minimization ToSet.
Local Open Scope pointed_scope.
Local Open Scope path_scope.

(** * Direct gluing of the first-left and first-right associators *)
Module S7DirectCore.
Section Construction.
  Context `{Univalence}.
  Local Existing Instances S7LeftScalar.circle_imaginaroid
    S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative
    S7LeftScalar.circle_commutative S7LeftScalar.circle_connected
    S7LeftScalar.circle_truncated.

  Local Notation C := (Sphere 1).
  Local Notation J := (Join@{Set Set Set} C C).
  Local Notation mu := (cd_op@{Set} (X:=psphere 1)).
  Local Notation BL := (S7LeftScalar.first_l cd_diamond_susp).
  Local Notation BR := S7RightScalar.first_r.
  Local Notation BM := (S7MiddleScalar.middle_l cd_diamond_susp).
  Local Notation AL := (cd_assoc_last_joinl@{Set} (X:=psphere 1)).
  Local Notation F := (fun y z x : J => mu (mu x y) z).
  Local Notation G := (fun y z x : J => mu x (mu y z)).

  (** The only additional datum for join induction in the first argument. A value is a 2-path in [J], not a scalar-loop proof. *)
  Definition Gamma (a b : C) (y z : J)
    := ap (F y z) (jglue a b) @ BR b y z
      = BL a y z @ ap (G y z) (jglue a b).

  (** The whole middle-left face is naturality of the existing middle associator. Its endpoint rows are definitionally [BL] and [BR]. *)
  Definition face_y (a b s : C) (z : J)
    : Gamma a b (joinl s) z
    := concat_Ap (fun x => BM s x z) (jglue a b).

  (** The whole last-left face uses the existing [AL] homotopy and the two specified overlaps. *)
  Definition face_z (a b : C) (y : J) (c : C)
    : Gamma a b y (joinl c)
    := (ap (fun r => ap (F y (joinl c)) (jglue a b) @ r)
          (S7RightScalar.overlap b y c))^
      @ (concat_Ap (fun x => AL x y c) (jglue a b)
        @ ap (fun r => r @ ap (G y (joinl c)) (jglue a b))
          (S7LeftScalar.overlap cd_diamond_susp a y c)).

  (** The intersection comparison is naturality of the middle overlap. Its endpoints are exactly the overlaps used in [face_z]. *)
  Definition face_overlap (a b s c : C)
    : face_z a b (joinl s) c = face_y a b s (joinl c).
  Proof.
    napply moveR_Vp.
    exact (concat_Ap_homotopic _ _
      (fun x => S7MiddleScalar.overlap cd_diamond_susp s x c)
      (jglue a b)).
  Defined.

  Local Notation E := (fun a b =>
    JoinInd2LeftGlue (Gamma a b) North (face_y a b)).
  Local Notation el := (fun a b => Join_ind2_from_left_glue_l
    (Gamma a b) North (face_y a b) (face_z a b) (face_overlap a b)).
  Local Notation er := (fun a b => Join_ind2_from_left_glue_r
    (Gamma a b) North North (face_y a b) (face_z a b)
    (face_overlap a b)).

  (** The remaining mixed extension. The right y-face is transported from [face_y a b North], and its z-glue comparison is transported from [el a b s t North]. Both choices retain the actual [face_overlap]; no uniqueness of join-valued fillers is used. This type is a 4-path in [J]. *)
  Definition Mixed (a b s t c d : C)
    := transport (E a b s t) (jglue c d) (el a b s t c)
      = er a b s t d.

  (** The [s = North] face follows from [Join_ind2_from_left_mixed_base]. The [c = North] face is reflexivity by the choice of [er]. *)

  (** OPEN: the general mixed filler is not constructed here. The following direct assembly has no scalar-loop or circle-induction step. *)
  Context (mixed : forall a b s t c d : C, Mixed a b s t c d).

  Definition first_glue (a b : C) (y z : J) : Gamma a b y z
    := Join_ind2_from_left (Gamma a b) North North
      (face_y a b) (face_z a b) (face_overlap a b) (mixed a b) y z.

  Definition associator (x y z : J) : mu (mu x y) z = mu x (mu y z)
    := Join_ind_FlFr (F y z) (G y z)
      (fun a => BL a y z) (fun b => BR b y z)
      (fun a b => first_glue a b y z) x.

  Definition associative : Associative mu
    := fun x y z => (associator x y z)^.
End Construction.

End S7DirectCore.
