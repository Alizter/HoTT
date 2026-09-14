From HoTT Require Import Basics.
Require Import Types.Paths Types.Universe.
Require Import Classes.interfaces.abstract_algebra.
Require Import Pointed.Core Spaces.Spheres.
Require Import Homotopy.CayleyDickson Homotopy.Suspension.
Require Import Homotopy.Join.Core Homotopy.Join.Rec2.
Require Import Homotopy.HSpaceS7.LeftScalar Homotopy.HSpaceS7.MiddleScalar.
Require Import Homotopy.HSpaceS7.RightScalar.

Local Set Universe Minimization ToSet.
Local Open Scope pointed_scope.
Local Open Scope path_scope.

(** * Direct gluing of the first-left and first-right associators *)
Module S7DirectGluing.
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

(** ** Normalizing the mixed boundary *)
Section Normalization.
  Universe u.
  Context `{Univalence}.
  Local Existing Instances S7LeftScalar.circle_imaginaroid
    S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative
    S7LeftScalar.circle_commutative S7LeftScalar.circle_connected
    S7LeftScalar.circle_truncated.
  Local Notation C := (Sphere 1).
  Local Notation J := (Join@{Set Set Set} C C).
  Local Notation mu := (cd_op@{Set} (X:=psphere 1)).
  Local Notation F := (fun y z x : J => mu (mu x y) z).
  Local Notation G := (fun y z x : J => mu x (mu y z)).
  (** Keep the existing proof universe shared, including at constructor values where it is no longer inferable from the type. *)
  Local Notation Gamma := (S7DirectGluing.Gamma@{u}).
  Local Notation face_y := (S7DirectGluing.face_y@{u}).
  Local Notation face_z := (S7DirectGluing.face_z@{u}).
  Local Notation face_overlap := (S7DirectGluing.face_overlap@{u}).
  Local Notation Mixed := (S7DirectGluing.Mixed@{u}).
  Local Notation BM := (S7MiddleScalar.middle_l@{u} cd_diamond_susp).
  Local Notation el := (fun a b => Join_ind2_from_left_glue_l
    (Gamma a b) North (face_y a b) (face_z a b) (face_overlap a b)).
  Local Notation er := (fun a b => Join_ind2_from_left_glue_r
    (Gamma a b) North North (face_y a b) (face_z a b)
    (face_overlap a b)).

  Let U (a b s t : C) (z : J) : Gamma a b (joinr t) z
    := transport (fun y => Gamma a b y z) (jglue s t)
      (face_y a b s z).

  Let middle_beta (a b s : C) (z : J)
    : face_y a b s z
      = S7MiddleScalar.middle_l_glue@{u} cd_diamond_susp s a b z
    := Join_ind_FlFr_beta_jglue
      (fun x => F (joinl s) z x) (fun x => G (joinl s) z x)
      (fun a => BM s (joinl a) z) (fun b => BM s (joinr b) z)
      (fun a b => S7MiddleScalar.middle_l_glue@{u}
        cd_diamond_susp s a b z) a b.

  (** This is the original middle mixed computation, with the two actual outer beta paths. *)
  Let middle_cell (a b s c d : C)
    : transport (Gamma a b (joinl s)) (jglue c d)
        (face_y a b s (joinl c)) = face_y a b s (joinr d)
    := (ap (transport (Gamma a b (joinl s)) (jglue c d))
          (middle_beta a b s (joinl c))
        @ S7MiddleScalar.middle_l_glue_glue@{u} cd_diamond_susp s a b c d)
      @ (middle_beta a b s (joinr d))^.

  Definition face_y_glue (a b s c d : C)
    : apD (face_y a b s) (jglue c d) = middle_cell a b s c d.
  Proof.
    exact (Join_ind_FlFr_ind_beta_jglue_jglue
      (fun x z => F (joinl s) z x) (fun x z => G (joinl s) z x)
      (fun a z => BM s (joinl a) z) (fun b z => BM s (joinr b) z)
      (S7MiddleScalar.middle_l_glue_l cd_diamond_susp s)
      (S7MiddleScalar.middle_l_glue_r cd_diamond_susp s)
      (S7MiddleScalar.middle_l_glue_glue@{u} cd_diamond_susp s) a b c d).
  Defined.

  (** The z-side of the transported y-face: transport interchange followed by the specified middle cell. *)
  Let side (a b s t c d : C)
    : transport (Gamma a b (joinr t)) (jglue c d)
        (U a b s t (joinl c)) = U a b s t (joinr d)
    := transport_transport (Gamma a b) (jglue s t) (jglue c d)
        (face_y a b s (joinl c))
      @ ap (transport (fun y => Gamma a b y (joinr d)) (jglue s t))
        (middle_cell a b s c d).

  Definition transported_face_glue (a b s t c d : C)
    : apD (U a b s t) (jglue c d) = side a b s t c d.
  Proof.
    lhs napply apD_transport.
    exact (1 @@ ap (ap (transport
      (fun y => Gamma a b y (joinr d)) (jglue s t)))
      (face_y_glue a b s c d)).
  Defined.

  Let cap (a b s t c : C)
    : face_z a b (joinr t) c = U a b s t (joinl c)
    := Join_ind2_from_left_overlap_r (Gamma a b) s
      (face_y a b) (face_z a b) (face_overlap a b) t c.
  Let image (a b s t c d : C)
    := ap (transport (Gamma a b (joinr t)) (jglue c d))
      (cap a b s t c).

  Let image_el (a b s t c d : C)
    : ap (transport (Gamma a b (joinr t)) (jglue c d))
        (el a b s t c)
      = (image a b s t c d)^ @ image a b North t c d.
  Proof.
    refine (ap_pp _ _ _ @ _).
    exact (ap_V _ _ @@ 1).
  Defined.

  (** Compute the transported right edge as well, rather than leaving a transport in a family of 3-paths in the normalized equation. *)
  Let right_cell (a b s t d : C)
    : er a b s t d
      = ((side a b s t North d)^
          @ ap (transport (Gamma a b (joinr t)) (jglue North d))
            (el a b s t North)) @ side a b North t North d.
  Proof.
    lhs napply (transport_paths_FlFr_D
      (f:=U a b s t) (g:=U a b North t)
      (jglue North d) (el a b s t North)).
    exact ((inverse2 (transported_face_glue a b s t North d) @@ 1)
      @@ transported_face_glue a b North t North d).
  Defined.

  Let pasting (a b s t c d : C) := image a b s t c d @ side a b s t c d.

  (** These two normalized pastings have the same endpoints, independently of their original centers [U a b s t (joinr d)]. The equation is still a 4-path, with the actual middle cell, overlap, and transport interchange retained. No transport in a family of 3-paths remains. *)
  Definition NormalizedMixed (a b s t c d : C)
    := pasting a b s t c d @ (pasting a b s t North d)^
      = pasting a b North t c d @ (pasting a b North t North d)^.

  Definition equiv_mixed_normalize (a b s t c d : C)
    : NormalizedMixed a b s t c d <~> Mixed a b s t c d.
  Proof.
    refine (dpath_path_FlFr_D (U a b s t) (U a b North t)
      (jglue c d) (el a b s t c) (er a b s t d) oE _).
    refine (equiv_concat_lr
      (1 @@ transported_face_glue a b North t c d)
      (transported_face_glue a b s t c d @@ 1)^ oE _).
    refine (equiv_concat_lr (image_el a b s t c d @@ 1)
      (1 @@ (right_cell a b s t d
        @ ((1 @@ image_el a b s t North d) @@ 1)))^ oE _).
    exact (equiv_pasting_zigzags
      (image a b s t c d) (image a b s t North d)
      (image a b North t c d) (image a b North t North d)
      (side a b s t c d) (side a b s t North d)
      (side a b North t c d) (side a b North t North d)).
  Defined.
End Normalization.
End S7DirectGluing.
