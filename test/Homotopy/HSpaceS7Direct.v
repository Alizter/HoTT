From HoTT Require Import Basics Types.Paths Types.Universe.
From HoTT Require Import Pointed.Core Spaces.Spheres.
From HoTT Require Import Homotopy.CayleyDickson Homotopy.Suspension.
From HoTT Require Import Homotopy.Join.Core Homotopy.Join.Rec2.
From HoTT Require Import Homotopy.HSpace.Core Homotopy.HSpaceS7.
From HoTT Require Import Homotopy.HSpaceS7.LeftScalar.
From HoTT Require Import Homotopy.HSpaceS7.MiddleScalar.
From HoTT Require Import Homotopy.HSpaceS7.RightScalar.
From HoTT Require Import Homotopy.HSpaceS7.Direct.

Local Set Universe Minimization ToSet.
Local Open Scope pointed_scope.
Local Open Scope path_scope.
Module D := S7DirectGluing.

Local Transparent D.face_overlap D.associator D.face_y_glue
  D.transported_face_glue D.equiv_mixed_normalize.

Section DirectChecks.
  Universe u.
  Context `{Univalence}.
  Local Existing Instances S7LeftScalar.circle_imaginaroid
    S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative
    S7LeftScalar.circle_commutative S7LeftScalar.circle_connected
    S7LeftScalar.circle_truncated.

  Local Notation C := (Sphere 1).
  Local Notation J := (Join@{Set Set Set} C C).
  Local Notation mu := (cd_op@{Set} (X:=psphere 1)).
  Local Notation AL := (cd_assoc_last_joinl@{Set} (X:=psphere 1)).
  Local Notation BM := (S7MiddleScalar.middle_l cd_diamond_susp).
  Local Notation F := (fun y z x : J => mu (mu x y) z).
  Local Notation G := (fun y z x : J => mu x (mu y z)).

  (** Both whole faces and their specified intersection are unconditional. *)
  Example middle_face (a b s : C) (z : J)
    : D.face_y a b s z = concat_Ap (fun x => BM s x z) (jglue a b)
    := idpath.
  Example last_face (a b : C) (y : J) (c : C)
    : D.face_z a b y c
      = (ap (fun r => ap (F y (joinl c)) (jglue a b) @ r)
          (S7RightScalar.overlap b y c))^
        @ (concat_Ap (fun x => AL x y c) (jglue a b)
          @ ap (fun r => r @ ap (G y (joinl c)) (jglue a b))
            (S7LeftScalar.overlap cd_diamond_susp a y c))
    := idpath.
  Example overlap_left_endpoint (a s c : C)
    : S7MiddleScalar.overlap cd_diamond_susp s (joinl a) c
      = S7LeftScalar.overlap cd_diamond_susp a (joinl s) c
    := idpath.
  Example overlap_right_endpoint (b s c : C)
    : S7MiddleScalar.overlap cd_diamond_susp s (joinr b) c
      = S7RightScalar.overlap b (joinl s) c
    := idpath.
  Example specified_face_comparison (a b s c : C)
    : D.face_overlap a b s c
      = moveR_Vp _ _ _ (concat_Ap_homotopic _ _
          (fun x => S7MiddleScalar.overlap cd_diamond_susp s x c)
          (jglue a b))
    := idpath.
  Example mixed_middle_unit (a b t c d : C) : D.Mixed a b North t c d
    := Join_ind2_from_left_mixed_base (D.Gamma a b) North North
      (D.face_y a b) (D.face_z a b) (D.face_overlap a b) t c d.
  Example mixed_last_unit (a b s t d : C) : D.Mixed a b s t North d
    := idpath.

  (** Inspect the computed middle cell and transported sides, not a replacement mixed witness. *)
  Let U a b s t z := transport (fun y => D.Gamma a b y z)
    (jglue s t) (D.face_y a b s z).
  Let beta a b s z : D.face_y a b s z
    = S7MiddleScalar.middle_l_glue cd_diamond_susp s a b z
    := Join_ind_FlFr_beta_jglue _ _ _ _ _ a b.
  Let cell a b s c d :=
    (ap (transport (D.Gamma a b (joinl s)) (jglue c d))
        (beta a b s (joinl c))
      @ S7MiddleScalar.middle_l_glue_glue cd_diamond_susp s a b c d)
    @ (beta a b s (joinr d))^.
  Let side a b s t c d :=
    transport_transport (D.Gamma a b) (jglue s t) (jglue c d)
        (D.face_y a b s (joinl c))
      @ ap (transport (fun y => D.Gamma a b y (joinr d)) (jglue s t))
        (cell a b s c d).
  Let cap a b s t c := Join_ind2_from_left_overlap_r (D.Gamma a b) s
    (D.face_y a b) (D.face_z a b) (D.face_overlap a b) t c.
  Let pasting a b s t c d :=
    ap (transport (D.Gamma a b (joinr t)) (jglue c d))
      (cap a b s t c) @ side a b s t c d.

  Example actual_middle_cell (a b s c d : C)
    : apD (D.face_y a b s) (jglue c d) = cell a b s c d
    := D.face_y_glue@{u} a b s c d.
  Example transported_middle_cell (a b s t c d : C)
    : apD (U a b s t) (jglue c d) = side a b s t c d
    := D.transported_face_glue@{u} a b s t c d.
  (** The same nested beta theorem computes the first-left and first-right cells needed when expanding transport interchange in [Gamma]. *)
  Local Notation BL := (S7LeftScalar.first_l cd_diamond_susp).
  Local Notation BR := S7RightScalar.first_r.
  Let Sq (x : J)
    (B : forall y z : J, mu (mu x y) z = mu x (mu y z))
    (s t : C) (z : J)
    := ap (fun y => mu (mu x y) z) (jglue s t) @ B (joinr t) z
      = B (joinl s) z @ ap (fun y => mu x (mu y z)) (jglue s t).
  Let beta_l a s t z
    : concat_Ap (fun y => BL a y z) (jglue s t)
      = S7LeftScalar.first_l_glue cd_diamond_susp a s t z
    := Join_ind_FlFr_beta_jglue _ _ _ _ _ s t.
  Let beta_r a s t z
    : concat_Ap (fun y => BR a y z) (jglue s t)
      = S7RightScalar.first_r_glue a s t z
    := Join_ind_FlFr_beta_jglue _ _ _ _ _ s t.

  Example actual_first_left_cell (a s t c d : C)
    : apD (fun z => concat_Ap (fun y => BL a y z) (jglue s t))
        (jglue c d)
      = (ap (transport (Sq (joinl a) (BL a) s t) (jglue c d))
          (beta_l a s t (joinl c))
        @ S7LeftScalar.first_l_glue_glue cd_diamond_susp a s t c d)
        @ (beta_l a s t (joinr d))^.
  Proof.
    exact (Join_ind_FlFr_ind_beta_jglue_jglue
      (fun y z => mu (mu (joinl a) y) z)
      (fun y z => mu (joinl a) (mu y z))
      (fun s z => BL a (joinl s) z) (fun t z => BL a (joinr t) z)
      (S7LeftScalar.first_l_glue_l cd_diamond_susp a)
      (S7LeftScalar.first_l_glue_r cd_diamond_susp a)
      (S7LeftScalar.first_l_glue_glue cd_diamond_susp a) s t c d).
  Defined.
  Example actual_first_right_cell (a s t c d : C)
    : apD (fun z => concat_Ap (fun y => BR a y z) (jglue s t))
        (jglue c d)
      = (ap (transport (Sq (joinr a) (BR a) s t) (jglue c d))
          (beta_r a s t (joinl c))
        @ S7RightScalar.first_r_glue_glue a s t c d)
        @ (beta_r a s t (joinr d))^.
  Proof.
    exact (Join_ind_FlFr_ind_beta_jglue_jglue
      (fun y z => mu (mu (joinr a) y) z)
      (fun y z => mu (joinr a) (mu y z))
      (fun s z => BR a (joinl s) z) (fun t z => BR a (joinr t) z)
      (S7RightScalar.first_r_glue_l a)
      (S7RightScalar.first_r_glue_r a)
      (S7RightScalar.first_r_glue_glue a) s t c d).
  Defined.

  Example normalized_boundary (a b s t c d : C)
    : D.NormalizedMixed a b s t c d
      = (pasting a b s t c d @ (pasting a b s t North d)^
        = pasting a b North t c d @ (pasting a b North t North d)^)
    := idpath.
  Example normalized_middle_unit (a b t c d : C)
    : D.NormalizedMixed a b North t c d := idpath.
  Example normalized_last_unit (a b s t d : C)
    : D.NormalizedMixed a b s t North d
    := concat_pV _ @ (concat_pV _)^.
  Example normalized_to_original (a b s t c d : C)
    : D.NormalizedMixed a b s t c d <~> D.Mixed a b s t c d
    := D.equiv_mixed_normalize@{u} a b s t c d.
  Example normalized_roundtrip (a b s t c d : C)
    (q : D.NormalizedMixed a b s t c d)
    : (D.equiv_mixed_normalize a b s t c d)^-1
        (D.equiv_mixed_normalize a b s t c d q) = q
    := eissect (D.equiv_mixed_normalize a b s t c d) q.
  Example original_roundtrip (a b s t c d : C)
    (q : D.Mixed a b s t c d)
    : D.equiv_mixed_normalize a b s t c d
        ((D.equiv_mixed_normalize a b s t c d)^-1 q) = q
    := eisretr (D.equiv_mixed_normalize a b s t c d) q.

  Example normalized_s7_small
    (n : forall a b s t c d : C, D.NormalizedMixed@{u} a b s t c d)
    : IsHSpace@{Set} (psphere 7)
    := hspace_s7_from_direct_mixed (fun a b s t c d =>
      D.equiv_mixed_normalize@{u} a b s t c d (n a b s t c d)).

  Context (mixed : forall a b s t c d : C, D.Mixed a b s t c d).
  Let glue := D.first_glue@{u} mixed.
  Let assoc := D.associator@{u} mixed.
  Let edge a b := Join_ind2_from_left_glue (D.Gamma a b) North North
    (D.face_y a b) (D.face_z a b) (D.face_overlap a b) (mixed a b).

  Example glue_middle_face (a b s : C) (z : J)
    : glue a b (joinl s) z = D.face_y a b s z := idpath.
  Example glue_right_face (a b t : C) (z : J)
    : glue a b (joinr t) z
      = transport (fun y => D.Gamma a b y z) (jglue North t)
          (D.face_y a b North z)
    := idpath.
  Example glue_last_face (a b : C) (y : J) (c : C)
    : D.face_z a b y c = glue a b y (joinl c)
    := Join_ind2_from_left_overlap (D.Gamma a b) North North
      (D.face_y a b) (D.face_z a b) (D.face_overlap a b)
      (mixed a b) y c.
  Example retained_intersection (a b s c : C)
    : glue_last_face a b (joinl s) c = D.face_overlap a b s c
    := idpath.
  Example first_edge (a b s t : C) (z : J)
    : apD (fun y => glue a b y z) (jglue s t) = edge a b s t z.
  Proof.
    exact (Join_ind_beta_jglue _ _ _ _ s t).
  Defined.
  Example mixed_computation (a b s t c d : C)
    : apD (edge a b s t) (jglue c d) = mixed a b s t c d.
  Proof.
    exact (Join_ind_beta_jglue _ _ _ _ c d).
  Defined.

  (** The final associator glues the original first-variable associators. *)
  Example associator_left (a : C) (y z : J)
    : assoc (joinl a) y z = S7LeftScalar.first_l cd_diamond_susp a y z
    := idpath.
  Example associator_right (b : C) (y z : J)
    : assoc (joinr b) y z = S7RightScalar.first_r b y z := idpath.
  Example associator_glue (a b : C) (y z : J)
    : concat_Ap (fun x => assoc x y z) (jglue a b) = glue a b y z.
  Proof.
    exact (Join_ind_FlFr_beta_jglue _ _ _ _ _ a b).
  Defined.
  Example associativity_orientation (x y z : J)
    : D.associative mixed x y z = (assoc x y z)^ := idpath.
  Example direct_s7_small : IsHSpace@{Set} (psphere 7)
    := hspace_s7_from_direct_mixed mixed.
End DirectChecks.
