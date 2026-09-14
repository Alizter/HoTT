From HoTT Require Import Basics Types.Paths Types.Universe.
From HoTT Require Import Cubical.PathSquare Cubical.PathCube.
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
  D.transported_face_glue D.equiv_mixed_normalize D.transported_face
  D.transported_face_cell D.transported_face_cell_beta D.last_face_cell
  D.last_face_cell_beta D.computed_pasting D.equiv_mixed_expansion
  D.last_associator_transport_normal_form D.eta_square D.eta_square_beta
  D.eta_left_inner_cell_beta D.eta_inner_cell_beta
  D.right_product_cap_comparison
  D.last_middle_transport_normal_form
  D.last_middle_transport_cell_normal_form D.eta_last_associator_cell
  D.eta_last_associator_cell_beta.

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
  Local Notation BM := (S7MiddleScalar.middle_l@{u} cd_diamond_susp).
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
  Local Notation BL := (S7LeftScalar.first_l@{u} cd_diamond_susp).
  Local Notation BR := (S7RightScalar.first_r@{u}).
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

  (** The expanded face and its cube use all five original faces and their specified computations. *)
  Let xf a b y z := ap (F y z) (jglue a b).
  Let xg a b y z := ap (G y z) (jglue a b).
  Let nu a b s t z := concat_Ap (fun y => xf a b y z) (jglue s t).
  Let nv a b s t z := concat_Ap (fun y => xg a b y z) (jglue s t).
  Let nl a s t z := concat_Ap (fun y => BL a y z) (jglue s t).
  Let nr b s t z := concat_Ap (fun y => BR b y z) (jglue s t).
  Let left_cell a s t c d :=
    (ap (transport (Sq (joinl a) (BL a) s t) (jglue c d))
        (beta_l a s t (joinl c))
      @ S7LeftScalar.first_l_glue_glue@{u} cd_diamond_susp a s t c d)
    @ (beta_l a s t (joinr d))^.
  Let right_cell b s t c d :=
    (ap (transport (Sq (joinr b) (BR b) s t) (jglue c d))
        (beta_r b s t (joinl c))
      @ S7RightScalar.first_r_glue_glue@{u} b s t c d)
    @ (beta_r b s t (joinr d))^.
  Let theta a b s t z := transport_naturality_square_compute
    (fun y => xf a b y z) (fun y => xg a b y z)
    (fun y => BL a y z) (fun y => BR b y z)
    (jglue s t) (D.face_y a b s z).

  Example expanded_face_expression (a b s t : C) (z : J)
    : D.transported_face@{u} a b s t z
      = naturality_square_filler (nu a b s t z) (nv a b s t z)
          (nl a s t z) (nr b s t z) (D.face_y a b s z)
    := idpath.
  Example expanded_side_expression (a b s t c d : C)
    : D.transported_face_cell@{u} a b s t c d
      = naturality_square_filler_glue
          (nu a b s t) (nv a b s t) (nl a s t) (nr b s t)
          (D.face_y a b s) (jglue c d)
          (D.left_product_cell a b s t c d)
          (D.right_product_cell a b s t c d)
          (left_cell a s t c d) (right_cell b s t c d) (cell a b s c d)
    := idpath.
  Example actual_left_product_cube (a b s t c d : C)
    : apD (nu a b s t) (jglue c d) = D.left_product_cell a b s t c d
    := D.left_product_cell_beta a b s t c d.
  Example actual_right_product_cube (a b s t c d : C)
    : apD (nv a b s t) (jglue c d) = D.right_product_cell a b s t c d
    := D.right_product_cell_beta a b s t c d.
  Example expanded_side_beta (a b s t c d : C)
    : apD (D.transported_face a b s t) (jglue c d)
      = D.transported_face_cell a b s t c d
    := D.transported_face_cell_beta@{u} a b s t c d.
  Example actual_interchange_expansion (a b s t c d : C)
    : side a b s t c d @ theta a b s t (joinr d)
      = ap (transport (D.Gamma a b (joinr t)) (jglue c d))
          (theta a b s t (joinl c)) @ D.transported_face_cell a b s t c d
    := D.transported_face_glue_expansion@{u} a b s t c d.
  Example actual_last_associator_cube (a b s t c : C)
    : apD (fun y => concat_Ap (fun x => AL x y c) (jglue a b))
        (jglue s t) = D.last_associator_cell a b s t c
    := D.last_associator_cell_beta a b s t c.
  Example actual_last_face_expansion (a b s t c : C)
    : apD (fun y => D.face_z a b y c) (jglue s t)
      = D.last_face_cell a b s t c
    := D.last_face_cell_beta@{u} a b s t c.

  (** Check the target of the shared-face comparison against the original diamond and all four multiplication edge beta paths. The left side is inferred from the theorem, whose type retains both actual converted cubes. *)
  Let W (a b : C) (z : J) := ap (fun x => mu x z) (jglue a b).
  Let bh0 (a c d : C) : ap (mu (joinl a)) (jglue c d) = _
    := Join_rec_beta_jglue _ _ _ c d.
  Let bh1 (b c d : C) : ap (mu (joinr b)) (jglue c d) = _
    := Join_rec_beta_jglue _ _ _ c d.
  Let bv0 (a b c : C) : W a b (joinl c) = _
    := Join_rec_beta_jglue _ _ _ a b.
  Let bv1 (a b d : C) : W a b (joinr d) = _
    := Join_rec_beta_jglue _ _ _ a b.
  Let multiplication_square (a b c d : C) :=
    ((1 @@ bv1 a b d) @ ((bh0 a c d @@ 1)
      @ (cd_op_diamond@{Set} (X:=psphere 1) a b c d
        @ (1 @@ bh1 b c d)^))) @ (bv0 a b c @@ 1)^.
  Let rho (c : C) := cd_op_right_translate_joinl@{Set} (X:=psphere 1) c.
  Let diagonal (c : C) := functor_join
    (fun v => @hspace_op (psphere 1) _ v c)
    (fun v => @hspace_op (psphere 1) _ v c).
  Let eta (c d : C) (v : J)
    := (rho c v)^ @ ap (mu v) (jglue c d).

  Example actual_last_transport_normal_form (x y : J) (c d : C)
    : transport (fun z => mu (mu x y) z = mu x (mu y z))
        (jglue c d) (AL x y c)
      = ((eta c d (mu x y))^
          @ (cd_op_diagonal_equivariance c x y)^)
        @ ap (mu x) (eta c d y)
    := D.last_associator_transport_normal_form@{u} x y c d.
  Example actual_eta_square (c d s t : C)
    : concat_Ap (eta c d) (jglue s t) = D.eta_square@{u} c d s t
    := D.eta_square_beta@{u} c d s t.
  Example actual_eta_left_cube (a b s t c d : C)
    : _ = _ := D.eta_left_inner_cell_beta@{u} a b s t c d.
  Example actual_eta_right_cube (a b s t c d : C)
    : _ = _ := D.eta_inner_cell_beta@{u} a b s t c d.

  Example actual_left_product_cap_target (a b s t c d : C)
    : _ = sq_ap_nat (diagonal c) (fun v => mu v (joinr d))
        (fun v => (rho c v)^ @ ap (mu v) (jglue c d))
        (sq_path (multiplication_square a b s t))
    := D.left_product_cap_comparison a b s t c d.
  Example right_cap_rewritten_with_eta (a b s t c d : C)
    : _ = _ := D.right_product_cap_comparison@{u} a b s t c d.
  Example combined_cap_transport_normal_form (a b s t c d : C)
    : _ := D.last_middle_transport_cell_normal_form@{u} a b s t c d.
  Example combined_eta_associator_cell (a b s t c d : C)
    : _ = D.eta_last_associator_cell@{u} a b s t c d
    := D.eta_last_associator_cell_beta@{u} a b s t c d.

  Example computed_pasting_expression (a b s t c d : C)
    : D.computed_pasting@{u} a b s t c d
      = ap (transport (D.Gamma a b (joinr t)) (jglue c d))
          (((D.last_face_cell a b s t c)^
            @ ap (transport (fun y => D.Gamma a b y (joinl c)) (jglue s t))
              (D.face_overlap a b s c)) @ theta a b s t (joinl c))
        @ D.transported_face_cell a b s t c d
    := idpath.
  Example original_pasting_expansion (a b s t c d : C)
    : pasting a b s t c d @ theta a b s t (joinr d)
      = D.computed_pasting a b s t c d
    := D.pasting_expansion@{u} a b s t c d.

  Let expanded a b s t c d :=
    D.computed_pasting@{u} a b s t c d
      @ (D.computed_pasting@{u} a b s t North d)^
      = D.computed_pasting@{u} a b North t c d
        @ (D.computed_pasting@{u} a b North t North d)^.
  Example expanded_to_original (a b s t c d : C)
    : expanded a b s t c d <~> D.Mixed a b s t c d
    := D.equiv_mixed_expansion@{u} a b s t c d.
  Example expanded_middle_unit (a b t c d : C)
    : D.Mixed a b North t c d
    := D.equiv_mixed_expansion a b North t c d 1.
  Example expanded_last_unit (a b s t d : C)
    : D.Mixed a b s t North d
    := D.equiv_mixed_expansion a b s t North d
      (concat_pV _ @ (concat_pV _)^).
  Example expansion_roundtrip (a b s t c d : C) (q : expanded a b s t c d)
    : (D.equiv_mixed_expansion a b s t c d)^-1
        (D.equiv_mixed_expansion a b s t c d q) = q
    := eissect (D.equiv_mixed_expansion a b s t c d) q.
  Example expansion_original_roundtrip (a b s t c d : C)
    (q : D.Mixed a b s t c d)
    : D.equiv_mixed_expansion a b s t c d
        ((D.equiv_mixed_expansion a b s t c d)^-1 q) = q
    := eisretr (D.equiv_mixed_expansion a b s t c d) q.
  Example expanded_s7_small
    (q : forall a b s t c d : C, expanded a b s t c d)
    : IsHSpace@{Set} (psphere 7)
    := hspace_s7_from_direct_mixed (fun a b s t c d =>
      D.equiv_mixed_expansion@{u} a b s t c d (q a b s t c d)).

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
