From HoTT Require Import Basics.
Require Import Types.Paths Types.Prod Types.Sigma Types.Universe.
Require Import Cubical.PathSquare Cubical.PathCube.
Require Import Classes.interfaces.canonical_names.
Require Import Pointed.Core Spaces.Spheres.
Require Import Homotopy.HSpace.Core Homotopy.HSpaceS1.
Require Import Homotopy.CayleyDickson Homotopy.Suspension.
Require Import Homotopy.Join.Core Homotopy.Join.Rec2.
Require Import Homotopy.HSpaceS7.LeftScalar Homotopy.HSpaceS7.MiddleScalar.
Require Import Homotopy.HSpaceS7.RightScalar.
Require Import Homotopy.HSpaceS7.Direct.Core.

Local Set Universe Minimization ToSet.
Local Open Scope pointed_scope.
Local Open Scope path_scope.

(** * Normalizing the mixed boundary *)
Module S7DirectNormalization.
Include S7DirectCore.
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
  Local Notation Gamma := (S7DirectCore.Gamma@{u}).
  Local Notation face_y := (S7DirectCore.face_y@{u}).
  Local Notation face_z := (S7DirectCore.face_z@{u}).
  Local Notation face_overlap := (S7DirectCore.face_overlap@{u}).
  Local Notation Mixed := (S7DirectCore.Mixed@{u}).
  Local Notation BM := (S7MiddleScalar.middle_l@{u} cd_diamond_susp).
  Local Notation BL := (S7LeftScalar.first_l@{u} cd_diamond_susp).
  Local Notation BR := (S7RightScalar.first_r@{u}).
  Local Notation AL := (cd_assoc_last_joinl@{Set} (X:=psphere 1)).
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

  (** ** Expanding transport interchange into the actual side cubes *)

  Let xf (a b : C) (y z : J) := ap (F y z) (jglue a b).
  Let xg (a b : C) (y z : J) := ap (G y z) (jglue a b).
  Let scalar_mul : C -> C -> C := @sg_op (psphere 1) _.
  Definition diagonal (c : C) := functor_join
    (fun v => scalar_mul v c) (fun v => scalar_mul v c).
  Definition rho (c : C)
    := cd_op_right_translate_joinl@{Set} (X:=psphere 1) c.
  Definition eta (c d : C) (v : J)
    := (rho c v)^ @ ap (mu v) (jglue c d).

  (** Transporting [AL] absorbs both right-translation corrections into [eta]. This is path algebra on the free last-input path; it imposes no new coherence on the diamond. *)
  Definition last_associator_transport_normal_form
    (x y : J) (c d : C)
    : transport (fun z => mu (mu x y) z = mu x (mu y z))
        (jglue c d) (AL x y c)
      = ((eta c d (mu x y))^
          @ (cd_op_diagonal_equivariance c x y)^)
        @ ap (mu x) (eta c d y)
    := transport_associator_normal_form mu (jglue c d)
      (diagonal c) (rho c) (cd_op_diagonal_equivariance c) x y.

  Let yf (x : J) (s t : C) (z : J)
    := ap (fun y => F y z x) (jglue s t).
  Let yg (x : J) (s t : C) (z : J)
    := ap (fun y => G y z x) (jglue s t).
  Let nu a b s t z := concat_Ap (fun y => xf a b y z) (jglue s t).
  Let nv a b s t z := concat_Ap (fun y => xg a b y z) (jglue s t).
  Let nl a s t z := concat_Ap (fun y => BL a y z) (jglue s t).
  Let nr b s t z := concat_Ap (fun y => BR b y z) (jglue s t).

  (** Unlike [U], this face is a path-algebra expression in the original five faces, not a transport in [Gamma]. *)
  Definition transported_face (a b s t : C) (z : J)
    : Gamma a b (joinr t) z
    := naturality_square_filler (nu a b s t z) (nv a b s t z)
      (nl a s t z) (nr b s t z) (face_y a b s z).

  Definition face_transport_compute (a b s t : C) (z : J)
    : U a b s t z = transported_face a b s t z
    := transport_naturality_square_compute
      (fun y => xf a b y z) (fun y => xg a b y z)
      (fun y => BL a y z) (fun y => BR b y z)
      (jglue s t) (face_y a b s z).

  Let left_beta a s t z
    : nl a s t z = S7LeftScalar.first_l_glue@{u} cd_diamond_susp a s t z
    := Join_ind_FlFr_beta_jglue _ _ _ _ _ s t.
  Let right_beta b s t z
    : nr b s t z = S7RightScalar.first_r_glue@{u} b s t z
    := Join_ind_FlFr_beta_jglue _ _ _ _ _ s t.
  Let left_square a s t z := yf (joinl a) s t z @ BL a (joinr t) z
    = BL a (joinl s) z @ yg (joinl a) s t z.
  Let right_square b s t z := yf (joinr b) s t z @ BR b (joinr t) z
    = BR b (joinl s) z @ yg (joinr b) s t z.
  Let left_cell a s t c d :=
    (ap (transport (left_square a s t) (jglue c d))
        (left_beta a s t (joinl c))
      @ S7LeftScalar.first_l_glue_glue@{u} cd_diamond_susp a s t c d)
    @ (left_beta a s t (joinr d))^.
  Let first_right_cell b s t c d :=
    (ap (transport (right_square b s t) (jglue c d))
        (right_beta b s t (joinl c))
      @ S7RightScalar.first_r_glue_glue@{u} b s t c d)
    @ (right_beta b s t (joinr d))^.

  (** The inner multiplication square, with its four recursor edge computations. *)
  Let W (a b : C) (z : J) := ap (fun x => mu x z) (jglue a b).
  Let mbh0 (a c d : C) : ap (mu (joinl a)) (jglue c d) = _
    := Join_rec_beta_jglue _ _ _ c d.
  Let mbh1 (b c d : C) : ap (mu (joinr b)) (jglue c d) = _
    := Join_rec_beta_jglue _ _ _ c d.
  Let mbv0 (a b c : C) : W a b (joinl c) = _
    := Join_rec_beta_jglue _ _ _ a b.
  Let mbv1 (a b d : C) : W a b (joinr d) = _
    := Join_rec_beta_jglue _ _ _ a b.
  Let multiplication_square (a b c d : C) :=
    ((1 @@ mbv1 a b d) @ ((mbh0 a c d @@ 1)
      @ (cd_op_diamond@{Set} (X:=psphere 1) a b c d
        @ (1 @@ mbh1 b c d)^))) @ (mbv0 a b c @@ 1)^.
  Let multiplication_square_beta (a b c d : C)
    : concat_Ap (W a b) (jglue c d) = multiplication_square a b c d.
  Proof.
    napply moveL_pV.
    exact (Join_rec2_beta_jglue_jglue J _ _ _ _ _ _ _ _
      (cd_op_diamond@{Set} (X:=psphere 1)) a b c d).
  Defined.
  Local Opaque cd_op cd_op_diamond.

  (** Postcomposition of the specified inner multiplication square gives the left-bracketed product's xy-face. The vertical and horizontal composition beta paths are kept. *)
  Let nu_vertical (a b : C) (y z : J)
    := ap_compose (fun x => mu x y) (fun v => mu v z) (jglue a b).
  Let nu_close (a b s t : C) (z : J)
    (n : ap (fun v => mu v z) (ap (mu (joinl a)) (jglue s t))
        @ ap (fun v => mu v z) (W a b (joinr t))
      = ap (fun v => mu v z) (W a b (joinl s))
        @ ap (fun v => mu v z) (ap (mu (joinr b)) (jglue s t)))
    := ((1 @@ nu_vertical a b (joinr t) z)
      @ naturality_change
        (ap_compose (mu (joinl a)) (fun v => mu v z) (jglue s t))
        (ap_compose (mu (joinr b)) (fun v => mu v z) (jglue s t)) n)
      @ (nu_vertical a b (joinl s) z @@ 1)^.
  Let nu_map (a b s t : C) (z : J)
    (n : ap (mu (joinl a)) (jglue s t) @ W a b (joinr t)
      = W a b (joinl s) @ ap (mu (joinr b)) (jglue s t))
    := nu_close a b s t z (ap_naturality (fun v => mu v z) n).
  Let nu_beta (a b s t : C) (z : J)
    : nu a b s t z = nu_map a b s t z (multiplication_square a b s t).
  Proof.
    napply moveL_pV.
    lhs napply (concat_Ap_homotopic _ _
      (fun y => nu_vertical a b y z) (jglue s t)).
    napply whiskerL.
    lhs napply (concat_Ap_postcompose (W a b) (fun v => mu v z)
      (jglue s t)).
    exact (ap (fun n => naturality_change _ _
      (ap_naturality (fun v => mu v z) n))
      (multiplication_square_beta a b s t)).
  Defined.

  (** The geometric inner cube is naturality of right multiplication on the specified multiplication square. Its six faces are fixed by [sq_ap_nat]; the equivalence retains the cube when converting back to a dependent path. *)
  Let nu_inner_cell (a b s t c d : C) :=
    (equiv_ap_naturality_cube (fun z v : J => mu v z) (jglue c d)
      (multiplication_square a b s t))^-1
      (sq_ap_nat (fun v => mu v (joinl c)) (fun v => mu v (joinr d))
        (fun v => ap (mu v) (jglue c d))
        (sq_path (multiplication_square a b s t))).
  Let nu_inner_cell_beta (a b s t c d : C)
    : apD (fun z => ap_naturality (fun v => mu v z)
        (multiplication_square a b s t)) (jglue c d)
      = nu_inner_cell a b s t c d.
  Proof.
    napply (moveL_equiv_V' (equiv_ap_naturality_cube
      (fun z v : J => mu v z) (jglue c d) (multiplication_square a b s t))).
    exact (ap_naturality_cube_beta (fun z v : J => mu v z)
      (jglue c d) (multiplication_square a b s t)).
  Defined.

  Definition left_product_cell (a b s t c d : C) :=
    (ap (transport _ (jglue c d)) (nu_beta a b s t (joinl c))
      @ ap01D1 (nu_close a b s t) (jglue c d)
        (nu_inner_cell a b s t c d)) @ (nu_beta a b s t (joinr d))^.

  Definition left_product_cell_beta (a b s t c d : C)
    : apD (nu a b s t) (jglue c d) = left_product_cell a b s t c d.
  Proof.
    refine (apD_homotopic (nu_beta a b s t) (jglue c d) @ _).
    nrefine ((1 @@ _) @@ 1).
    refine (apD_composeD (nu_close a b s t)
      (fun z => ap_naturality (fun v => mu v z)
        (multiplication_square a b s t)) (jglue c d) @ _).
    exact (ap (ap01D1 (nu_close a b s t) (jglue c d))
      (nu_inner_cell_beta a b s t c d)).
  Defined.

  (** The right-bracketed product uses naturality of the first multiplication homotopy on the specified inner square. Changing that source square by its actual mixed beta path rewrites both mapped faces of the cube, retaining the other four faces. *)
  Let nv_inner (a b s t : C) (z : J)
    (v : mu (joinl s) z = mu (joinr t) z) := concat_Ap (W a b) v.
  Let nv_change (a b s t : C) (z : J)
    (n : ap (mu (joinl a)) (W s t z) @ W a b (mu (joinr t) z)
      = W a b (mu (joinl s) z) @ ap (mu (joinr b)) (W s t z))
    := naturality_change
      (ap_compose (fun y => mu y z) (mu (joinl a)) (jglue s t))
      (ap_compose (fun y => mu y z) (mu (joinr b)) (jglue s t)) n.
  Let nv_beta (a b s t : C) (z : J)
    : nv a b s t z = nv_change a b s t z (nv_inner a b s t z (W s t z))
    := concat_Ap_precompose (W a b) (fun y => mu y z) (jglue s t).
  Let nv_inner_cell (a b s t c d : C) :=
    (equiv_concat_Ap_cube (W a b) (W s t) (jglue c d)
      (multiplication_square_beta s t c d))^-1
      (sq_ap_nat (mu (joinl a)) (mu (joinr b)) (W a b)
        (sq_path (multiplication_square s t c d))).
  Let nv_inner_cell_beta (a b s t c d : C)
    : apD (fun z => nv_inner a b s t z (W s t z)) (jglue c d)
      = nv_inner_cell a b s t c d.
  Proof.
    napply (moveL_equiv_V' (equiv_concat_Ap_cube (W a b) (W s t)
      (jglue c d) (multiplication_square_beta s t c d))).
    exact (equiv_concat_Ap_cube_beta (W a b) (W s t) (jglue c d)
      (multiplication_square_beta s t c d)).
  Defined.

  Definition right_product_cell (a b s t c d : C) :=
    (ap (transport _ (jglue c d)) (nv_beta a b s t (joinl c))
      @ ap01D1 (nv_change a b s t) (jglue c d)
        (nv_inner_cell a b s t c d)) @ (nv_beta a b s t (joinr d))^.

  Definition right_product_cell_beta (a b s t c d : C)
    : apD (nv a b s t) (jglue c d) = right_product_cell a b s t c d.
  Proof.
    lhs napply (apD_homotopic (nv_beta a b s t) (jglue c d)).
    napply (ap (fun q => (_ @ q) @ _)).
    lhs napply (apD_composeD (nv_change a b s t)
      (fun z => nv_inner a b s t z (W s t z)) (jglue c d)).
    exact (ap (ap01D1 (nv_change a b s t) (jglue c d))
      (nv_inner_cell_beta a b s t c d)).
  Defined.

  Local Transparent cd_op cd_op_diamond.

  Let paste_cubes a b s t c d := naturality_square_filler_glue
    (nu a b s t) (nv a b s t) (nl a s t) (nr b s t)
    (face_y a b s) (jglue c d).

  (** The first two cubes expose the inner multiplication diamonds: postcomposition for the left-bracketed product and dependent application of the first multiplication homotopy for the right-bracketed product. The other three are exactly the existing left, right, and balanced associator cubes, with their outer beta paths. There is no [transport_transport Gamma] here. *)
  Definition transported_face_cell (a b s t c d : C)
    : transport (Gamma a b (joinr t)) (jglue c d)
        (transported_face a b s t (joinl c))
      = transported_face a b s t (joinr d)
    := paste_cubes a b s t c d
      (left_product_cell a b s t c d) (right_product_cell a b s t c d)
      (left_cell a s t c d) (first_right_cell b s t c d)
      (middle_cell a b s c d).

  Definition transported_face_cell_beta (a b s t c d : C)
    : apD (transported_face a b s t) (jglue c d)
      = transported_face_cell a b s t c d.
  Proof.
    lhs napply (apD_naturality_square_filler
      (nu a b s t) (nv a b s t) (nl a s t) (nr b s t)
      (face_y a b s) (jglue c d)).
    lhs napply (ap011 (fun l r => paste_cubes a b s t c d l r
      (apD (nl a s t) (jglue c d)) (apD (nr b s t) (jglue c d))
      (apD (face_y a b s) (jglue c d)))
      (left_product_cell_beta a b s t c d)
      (right_product_cell_beta a b s t c d)).
    lhs napply (ap011 (fun l r => paste_cubes a b s t c d
      (left_product_cell a b s t c d) (right_product_cell a b s t c d)
      l r (apD (face_y a b s) (jglue c d)))
      (Join_ind_FlFr_ind_beta_jglue_jglue
        (fun y z => F y z (joinl a)) (fun y z => G y z (joinl a))
        (fun s z => BL a (joinl s) z) (fun t z => BL a (joinr t) z)
        (S7LeftScalar.first_l_glue_l cd_diamond_susp a)
        (S7LeftScalar.first_l_glue_r cd_diamond_susp a)
        (S7LeftScalar.first_l_glue_glue@{u} cd_diamond_susp a) s t c d)
      (Join_ind_FlFr_ind_beta_jglue_jglue
        (fun y z => F y z (joinr b)) (fun y z => G y z (joinr b))
        (fun s z => BR b (joinl s) z) (fun t z => BR b (joinr t) z)
        (S7RightScalar.first_r_glue_l b)
        (S7RightScalar.first_r_glue_r b)
        (S7RightScalar.first_r_glue_glue@{u} b) s t c d)).
    exact (ap (paste_cubes a b s t c d
      (left_product_cell a b s t c d) (right_product_cell a b s t c d)
      (left_cell a s t c d) (first_right_cell b s t c d))
      (face_y_glue a b s c d)).
  Defined.

  (** This is a computation of the previously specified interchange side, including both endpoint changes, not a newly chosen side with the same boundary. *)
  Definition transported_face_glue_expansion (a b s t c d : C)
    : side a b s t c d @ face_transport_compute a b s t (joinr d)
      = ap (transport (Gamma a b (joinr t)) (jglue c d))
          (face_transport_compute a b s t (joinl c))
        @ transported_face_cell a b s t c d.
  Proof.
    lhs_V napply (transported_face_glue a b s t c d @@ 1).
    exact (apD_natural (face_transport_compute a b s t) (jglue c d)
      @ (1 @@ transported_face_cell_beta a b s t c d)).
  Defined.

  (** ** The last face retains the original overlap cubes *)

  Let ol (a c : C) (y : J) := S7LeftScalar.overlap@{u} cd_diamond_susp a y c.
  Let or (b c : C) (y : J) := S7RightScalar.overlap@{u} b y c.
  Let ol_cell a s t c := equiv_naturality_transport2
    (fun y => AL (joinl a) y c) (fun y => BL a y (joinl c))
    (jglue s t) (ol a c (joinl s)) (ol a c (joinr t))
    (S7LeftScalar.overlap_glue@{u} cd_diamond_susp a s t c
      @ (1 @@ left_beta a s t (joinl c))^).
  Let or_cell b s t c := equiv_naturality_transport2
    (fun y => AL (joinr b) y c) (fun y => BR b y (joinl c))
    (jglue s t) (or b c (joinl s)) (or b c (joinr t))
    (S7RightScalar.overlap_glue@{u} b s t c
      @ (1 @@ right_beta b s t (joinl c))^).
  Let last_middle a b c y := concat_Ap (fun x => AL x y c) (jglue a b).

  (** The three factors of [AL] are scalar right translation, inverse diagonal equivariance, and the image of inverse scalar right translation. *)
  Let deq (c : C) := cd_op_diagonal_equivariance@{Set} (X:=psphere 1) c.
  Let h1 (c : C) (x y : J) := rho c (mu x y).
  Let h2 (c : C) (x y : J) := (deq c x y)^.
  Let h3 (c : C) (x y : J) := ap (mu x) (rho c y)^.
  Let e0 a b c y := xf a b y (joinl c).
  Let e1 (a b c : C) (y : J)
    := ap (fun x => diagonal c (mu x y)) (jglue a b).
  Let e2 (a b c : C) (y : J)
    := ap (fun x => mu x (diagonal c y)) (jglue a b).
  Let e3 a b c y := xg a b y (joinl c).
  Let n1 (a b c : C) (y : J) := concat_Ap (fun x => h1 c x y) (jglue a b).
  Let n2 (a b c : C) (y : J) := concat_Ap (fun x => h2 c x y) (jglue a b).
  Let n3 (a b c : C) (y : J) := concat_Ap (fun x => h3 c x y) (jglue a b).

  Local Opaque cd_op cd_op_diamond.

  Let n1_inner (a b c : C) (y : J) := concat_Ap (rho c) (W a b y).
  Let n1_change (a b c : C) (y : J)
    (n : ap (fun v => mu v (joinl c)) (W a b y) @ rho c (mu (joinr b) y)
      = rho c (mu (joinl a) y) @ ap (diagonal c) (W a b y))
    := naturality_change
      (ap_compose (fun x => mu x y) (fun v => mu v (joinl c)) (jglue a b))
      (ap_compose (fun x => mu x y) (diagonal c) (jglue a b)) n.
  Let n1_beta (a b c : C) (y : J)
    : n1 a b c y = n1_change a b c y (n1_inner a b c y)
    := concat_Ap_precompose (rho c) (fun x => mu x y) (jglue a b).
  Let n1_inner_cell (a b s t c : C) :=
    (equiv_concat_Ap_cube (rho c) (W a b) (jglue s t)
      (multiplication_square_beta a b s t))^-1
      (sq_ap_nat (fun v => mu v (joinl c)) (diagonal c) (rho c)
        (sq_path (multiplication_square a b s t))).
  Let n1_cell (a b s t c : C) :=
    (ap (transport _ (jglue s t)) (n1_beta a b c (joinl s))
      @ ap01D1 (n1_change a b c) (jglue s t) (n1_inner_cell a b s t c))
      @ (n1_beta a b c (joinr t))^.
  Let n1_cell_beta (a b s t c : C)
    : apD (n1 a b c) (jglue s t) = n1_cell a b s t c.
  Proof.
    refine (apD_homotopic (n1_beta a b c) (jglue s t) @ _).
    nrefine ((1 @@ _) @@ 1).
    refine (apD_composeD (n1_change a b c) (n1_inner a b c) (jglue s t) @ _).
    napply (ap (ap01D1 (n1_change a b c) (jglue s t))).
    napply (moveL_equiv_V' (equiv_concat_Ap_cube (rho c) (W a b)
      (jglue s t) (multiplication_square_beta a b s t))).
    exact (equiv_concat_Ap_cube_beta (rho c) (W a b) (jglue s t)
      (multiplication_square_beta a b s t)).
  Defined.

  (** The left-product cube and the first factor of the last-associator cube share a mapped multiplication square. Compare their actual converted inhabitants before merging them across that face. The four side-face computations are part of this 4-path. *)
  Let left_cap_cube (a b s t c d : C) := cu_concat_lr
    (cu_flip_lr
      (equiv_concat_Ap_cube (rho c) (W a b) (jglue s t)
        (multiplication_square_beta a b s t) (n1_inner_cell a b s t c)))
    (equiv_ap_naturality_cube (fun z v : J => mu v z) (jglue c d)
      (multiplication_square a b s t) (nu_inner_cell a b s t c d)).

  Definition left_product_cap_comparison (a b s t c d : C)
    : cu_ccGGGG
        (ap_nat_Vp (rho c) (fun v => ap (mu v) (jglue c d))
          (ap (mu (joinl a)) (jglue s t)))
        (ap_nat_Vp (rho c) (fun v => ap (mu v) (jglue c d))
          (ap (mu (joinr b)) (jglue s t)))
        (ap_nat_Vp (rho c) (fun v => ap (mu v) (jglue c d))
          (W a b (joinl s)))
        (ap_nat_Vp (rho c) (fun v => ap (mu v) (jglue c d))
          (W a b (joinr t))) (left_cap_cube a b s t c d)
      = sq_ap_nat (diagonal c) (fun v => mu v (joinr d))
        (fun v => (rho c v)^ @ ap (mu v) (jglue c d))
        (sq_path (multiplication_square a b s t)).
  Proof.
    pose (br := eisretr (equiv_concat_Ap_cube (rho c) (W a b)
      (jglue s t) (multiplication_square_beta a b s t))
      (sq_ap_nat (fun v => mu v (joinl c)) (diagonal c) (rho c)
        (sq_path (multiplication_square a b s t)))).
    pose (bp := eisretr (equiv_ap_naturality_cube (fun z v : J => mu v z)
      (jglue c d) (multiplication_square a b s t))
      (sq_ap_nat (fun v => mu v (joinl c)) (fun v => mu v (joinr d))
        (fun v => ap (mu v) (jglue c d))
        (sq_path (multiplication_square a b s t)))).
    refine (ap (cu_ccGGGG _ _ _ _)
      (ap011 (fun r p => cu_concat_lr (cu_flip_lr r) p) br bp) @ _).
    exact (sq_ap_nat_Vp (rho c) (fun v => ap (mu v) (jglue c d))
      (sq_path (multiplication_square a b s t))).
  Defined.

  (** The diagonal factor retains its original nested-induction mixed cell and both outer beta witnesses. *)
  Let dn (a b c : C) (y : J) := concat_Ap (fun x => deq c x y) (jglue a b).
  Let dbeta (a b c : C) (y : J)
    : dn a b c y
      = cd_op_diagonal_equivariance_glue@{Set} (X:=psphere 1) c a b y
    := Join_ind_FlFr_beta_jglue _ _ _ _ _ a b.
  Let dsquare (a b c : C) (y : J)
    := e2 a b c y @ deq c (joinr b) y = deq c (joinl a) y @ e1 a b c y.
  Let diagonal_input (a b s t c : C) := transport011
      (fun x : C * C => fun y : C * C =>
        zigzag (fst x) (snd x) (fst y)
          = zigzag (fst x) (snd x) (snd y))
      (path_prod' (cd_diamond_translate_l_neg_unit (X:=psphere 1) a s c)
        (cd_diamond_translate_l_parameter North b North t c))
      (path_prod' (cd_diamond_translate_r_parameter a North North t c)
        (cd_diamond_translate_r_unit b s c))
      (cd_op_diamond@{Set} (X:=psphere 1)
        a b (scalar_mul s c) (scalar_mul t c))
    = join_zigzag_filler (fun v => scalar_mul v c) (fun v => scalar_mul v c)
        1 1 1 1 (cd_op_diamond@{Set} (X:=psphere 1) a b s t).
  Let dcell (a b s t c : C) (delta : diagonal_input a b s t c) :=
    (ap (transport (dsquare a b c) (jglue s t)) (dbeta a b c (joinl s))
      @ cd_op_diagonal_equivariance_glue_glue_from_diamond@{Set}
          (X:=psphere 1) c a b s t delta)
      @ (dbeta a b c (joinr t))^.
  Let dcell_beta (a b s t c : C)
    : apD (dn a b c) (jglue s t)
      = dcell a b s t c (cd_op_diamond_diagonal a b s t c).
  Proof.
    exact (Join_ind_FlFr_ind_beta_jglue_jglue
      (fun x y => mu x (diagonal c y)) (fun x y => diagonal c (mu x y))
      (cd_op_diagonal_equivariance_joinl@{Set} (X:=psphere 1) c)
      (cd_op_diagonal_equivariance_joinr@{Set} (X:=psphere 1) c)
      (cd_op_diagonal_equivariance_glue_joinl@{Set} (X:=psphere 1) c)
      (cd_op_diagonal_equivariance_glue_joinr@{Set} (X:=psphere 1) c)
      (cd_op_diagonal_equivariance_glue_glue@{Set} (X:=psphere 1) c) a b s t).
  Defined.
  Let n2_change (a b c : C) (y : J) (n : dsquare a b c y)
    := (inverse_natural (e2 a b c y) (e1 a b c y) n)^.
  Let n2_beta (a b c : C) (y : J)
    : n2 a b c y = n2_change a b c y (dn a b c y)
    := concat_Ap_inverse (fun x => deq c x y) (jglue a b).
  Let n2_cell (a b s t c : C) (delta : diagonal_input a b s t c) :=
    (ap (transport _ (jglue s t)) (n2_beta a b c (joinl s))
      @ ap01D1 (n2_change a b c) (jglue s t) (dcell a b s t c delta))
      @ (n2_beta a b c (joinr t))^.
  Let n2_cell_beta (a b s t c : C)
    : apD (n2 a b c) (jglue s t)
      = n2_cell a b s t c (cd_op_diamond_diagonal a b s t c).
  Proof.
    refine (apD_homotopic (n2_beta a b c) (jglue s t) @ _).
    nrefine ((1 @@ _) @@ 1).
    refine (apD_composeD (n2_change a b c) (dn a b c) (jglue s t) @ _).
    exact (ap (ap01D1 (n2_change a b c) (jglue s t)) (dcell_beta a b s t c)).
  Defined.

  (** Scalar right translation's square is the original join naturality square for scalar commutativity. *)
  Let rho_square (c s t : C) :=
    (mbv0 s t c @@ 1)
      @ ((join_natsq (idpath (scalar_mul s c))
          (commutativity (f:=scalar_mul) c t))^
        @ (1 @@ functor_join_beta_jglue
          (fun v => scalar_mul v c) (fun v => scalar_mul v c) s t)^).
  Let rho_square_beta (c s t : C)
    : concat_Ap (rho c) (jglue s t) = rho_square c s t
    := Join_ind_FlFr_beta_jglue _ _ _ _ _ s t.
  Let rho_inverse_square (c s t : C) :=
    (inverse_natural (ap (fun y => mu y (joinl c)) (jglue s t))
      (ap (diagonal c) (jglue s t)) (rho_square c s t))^.
  Let rho_inverse_square_beta (c s t : C)
    : concat_Ap (fun y => (rho c y)^) (jglue s t) = rho_inverse_square c s t
    := concat_Ap_inverse (rho c) (jglue s t)
      @ ap (fun n => (inverse_natural
          (ap (fun y => mu y (joinl c)) (jglue s t))
          (ap (diagonal c) (jglue s t)) n)^) (rho_square_beta c s t).

  Let last_edge (c d : C) (v : J) := ap (mu v) (jglue c d).
  Let last_edge_square_beta (c d s t : C)
    : concat_Ap (last_edge c d) (jglue s t)
      = (multiplication_square s t c d)^
    := concat_Ap_ap mu (jglue s t) (jglue c d)
      @ inverse2 (multiplication_square_beta s t c d).

  (** The naturality square of [eta] is the pasting of inverse right translation with the transpose of the specified multiplication square. *)
  Definition eta_square (c d s t : C)
    : ap (diagonal c) (jglue s t) @ eta c d (joinr t)
      = eta c d (joinl s)
        @ ap (fun y => mu y (joinr d)) (jglue s t)
    := concat_natural
      (ap (diagonal c) (jglue s t))
      (ap (fun y => mu y (joinl c)) (jglue s t))
      (ap (fun y => mu y (joinr d)) (jglue s t))
      (rho c (joinl s))^ (rho c (joinr t))^
      (last_edge c d (joinl s)) (last_edge c d (joinr t))
      (rho_inverse_square c s t) (multiplication_square s t c d)^.

  Definition eta_square_beta (c d s t : C)
    : concat_Ap (eta c d) (jglue s t) = eta_square c d s t.
  Proof.
    refine (concat_Ap_concat (fun y => (rho c y)^)
      (last_edge c d) (jglue s t) @ _).
    exact (ap011 (concat_natural
      (ap (diagonal c) (jglue s t))
      (ap (fun y => mu y (joinl c)) (jglue s t))
      (ap (fun y => mu y (joinr d)) (jglue s t))
      (rho c (joinl s))^ (rho c (joinr t))^
      (last_edge c d (joinl s)) (last_edge c d (joinr t)))
      (rho_inverse_square_beta c s t)
      (last_edge_square_beta c d s t)).
  Defined.

  Let eta_left_inner (a b c d : C) (y : J)
    := concat_Ap (eta c d) (W a b y).
  Let eta_left_inner_cell (a b s t c d : C) :=
    (equiv_concat_Ap_cube (eta c d) (W a b) (jglue s t)
      (multiplication_square_beta a b s t))^-1
      (sq_ap_nat (diagonal c) (fun v => mu v (joinr d)) (eta c d)
        (sq_path (multiplication_square a b s t))).

  Definition eta_left_inner_cell_beta (a b s t c d : C)
    : apD (eta_left_inner a b c d) (jglue s t)
      = eta_left_inner_cell a b s t c d.
  Proof.
    napply (moveL_equiv_V' (equiv_concat_Ap_cube (eta c d) (W a b)
      (jglue s t) (multiplication_square_beta a b s t))).
    exact (equiv_concat_Ap_cube_beta (eta c d) (W a b) (jglue s t)
      (multiplication_square_beta a b s t)).
  Defined.

  Let eta_inner (a b c d : C) (y : J)
    := concat_Ap (W a b) (eta c d y).
  Let eta_inner_cell (a b s t c d : C) :=
    (equiv_concat_Ap_cube (W a b) (eta c d) (jglue s t)
      (eta_square_beta c d s t))^-1
      (sq_ap_nat (mu (joinl a)) (mu (joinr b)) (W a b)
        (sq_path (eta_square c d s t))).

  (** Applying the first multiplication homotopy to [eta_square] gives the common cube for the right-product and final-translation contributions. *)
  Definition eta_inner_cell_beta (a b s t c d : C)
    : apD (eta_inner a b c d) (jglue s t)
      = eta_inner_cell a b s t c d.
  Proof.
    napply (moveL_equiv_V' (equiv_concat_Ap_cube (W a b) (eta c d)
      (jglue s t) (eta_square_beta c d s t))).
    exact (equiv_concat_Ap_cube_beta (W a b) (eta c d) (jglue s t)
      (eta_square_beta c d s t)).
  Defined.

  Let n3_inner (a b c : C) (y : J) := concat_Ap (W a b) (rho c y)^.
  Let n3_change (a b c : C) (y : J)
    (n : ap (mu (joinl a)) (rho c y)^ @ W a b (mu y (joinl c))
      = W a b (diagonal c y) @ ap (mu (joinr b)) (rho c y)^) := n^.
  Let n3_beta (a b c : C) (y : J)
    : n3 a b c y = n3_change a b c y (n3_inner a b c y)
    := concat_Ap_ap mu (jglue a b) (rho c y)^.
  Let n3_inner_cell (a b s t c : C) :=
    (equiv_concat_Ap_cube (W a b) (fun y => (rho c y)^) (jglue s t)
      (rho_inverse_square_beta c s t))^-1
      (sq_ap_nat (mu (joinl a)) (mu (joinr b)) (W a b)
        (sq_path (rho_inverse_square c s t))).
  Let n3_inner_cell_beta (a b s t c : C)
    : apD (n3_inner a b c) (jglue s t) = n3_inner_cell a b s t c.
  Proof.
    napply (moveL_equiv_V' (equiv_concat_Ap_cube (W a b)
      (fun y => (rho c y)^) (jglue s t) (rho_inverse_square_beta c s t))).
    exact (equiv_concat_Ap_cube_beta (W a b) (fun y => (rho c y)^)
      (jglue s t) (rho_inverse_square_beta c s t)).
  Defined.
  Let n3_cell (a b s t c : C) :=
    (ap (transport _ (jglue s t)) (n3_beta a b c (joinl s))
      @ ap01D1 (n3_change a b c) (jglue s t) (n3_inner_cell a b s t c))
      @ (n3_beta a b c (joinr t))^.
  Let n3_cell_beta (a b s t c : C)
    : apD (n3 a b c) (jglue s t) = n3_cell a b s t c.
  Proof.
    refine (apD_homotopic (n3_beta a b c) (jglue s t) @ _).
    nrefine ((1 @@ _) @@ 1).
    refine (apD_composeD (n3_change a b c) (n3_inner a b c) (jglue s t) @ _).
    exact (ap (ap01D1 (n3_change a b c) (jglue s t))
      (n3_inner_cell_beta a b s t c)).
  Defined.

  (** Transpose the right-product cube so that it computes variation of the last-input edge in the middle argument. All six faces, including the original multiplication square, are retained. *)
  Let nv_cube (a b s t c d : C) :=
    equiv_concat_Ap_cube (W a b) (W s t) (jglue c d)
      (multiplication_square_beta s t c d)
      (nv_inner_cell a b s t c d).
  Let nv_cube_transposed_raw (a b s t c d : C) :=
    cu_GGcccc
      (sq_ap_tr (mu (joinl a))
        (sq_path (multiplication_square s t c d)))
      (sq_ap_tr (mu (joinr b))
        (sq_path (multiplication_square s t c d)))
      (cu_swap_tb_fb (nv_cube a b s t c d)).
  Let nv_cube_transposed (a b s t c d : C) :=
    cu_GGcccc
      (ap (fun q => sq_ap (mu (joinl a)) q)
        (sq_tr_path (multiplication_square s t c d)))
      (ap (fun q => sq_ap (mu (joinr b)) q)
        (sq_tr_path (multiplication_square s t c d)))
      (nv_cube_transposed_raw a b s t c d).

  Let cross_inner (a b c d : C) (y : J)
    := concat_Ap (W a b) (last_edge c d y).
  Let cross_inner_cell (a b s t c d : C) :=
    (equiv_concat_Ap_cube (W a b) (last_edge c d) (jglue s t)
      (last_edge_square_beta c d s t))^-1
      (nv_cube_transposed a b s t c d).

  Let cross_inner_cell_beta (a b s t c d : C)
    : apD (cross_inner a b c d) (jglue s t)
      = cross_inner_cell a b s t c d.
  Proof.
    napply (moveL_equiv_V' (equiv_concat_Ap_cube (W a b)
      (last_edge c d) (jglue s t) (last_edge_square_beta c d s t))).
    unfold nv_cube_transposed, nv_cube_transposed_raw, nv_cube.
    lhs napply (equiv_concat_Ap_cube_beta (W a b) (last_edge c d)
      (jglue s t) (last_edge_square_beta c d s t)).
    rhs napply (ap (fun q => cu_GGcccc _ _
      (cu_GGcccc _ _ (cu_swap_tb_fb q)))
      (eisretr (equiv_concat_Ap_cube (W a b) (W s t) (jglue c d)
        (multiplication_square_beta s t c d)) _)).
    rhs napply (ap (fun q => cu_GGcccc
      (ap (fun q => sq_ap (mu (joinl a)) q)
        (sq_tr_path (multiplication_square s t c d)))
      (ap (fun q => sq_ap (mu (joinr b)) q)
        (sq_tr_path (multiplication_square s t c d))) q)
      (sq_ap_nat_tr (mu (joinl a)) (mu (joinr b)) (W a b)
        (sq_path (multiplication_square s t c d)))).
    exact (cu_GGcccc_natural
      (fun q => sq_ap_nat (mu (joinl a)) (mu (joinr b)) (W a b) q)
      (sq_tr_path (multiplication_square s t c d)))^.
  Defined.

  Let eta_split_close (a b c d : C) (y : J)
    (n : ap (mu (joinl a)) (rho c y)^ @ W a b (mu y (joinl c))
      = W a b (diagonal c y) @ ap (mu (joinr b)) (rho c y)^)
    (m : ap (mu (joinl a)) (last_edge c d y) @ W a b (mu y (joinr d))
      = W a b (mu y (joinl c)) @ ap (mu (joinr b)) (last_edge c d y))
    := naturality_change
      (ap_pp (mu (joinl a)) (rho c y)^ (last_edge c d y))
      (ap_pp (mu (joinr b)) (rho c y)^ (last_edge c d y))
      (concat_pp_p (ap (mu (joinl a)) (rho c y)^)
          (ap (mu (joinl a)) (last_edge c d y)) (W a b (mu y (joinr d)))
        @ (1 @@ m)
        @ concat_p_pp (ap (mu (joinl a)) (rho c y)^)
          (W a b (mu y (joinl c)))
          (ap (mu (joinr b)) (last_edge c d y))
        @ (n @@ 1)
        @ concat_pp_p (W a b (diagonal c y))
          (ap (mu (joinr b)) (rho c y)^)
          (ap (mu (joinr b)) (last_edge c d y))).
  Let eta_split (a b c d : C) (y : J)
    := eta_split_close a b c d y
      (n3_inner a b c y) (cross_inner a b c d y).
  Let eta_split_beta (a b c d : C) (y : J)
    : eta_inner a b c d y = eta_split a b c d y
    := concat_Ap_pp (W a b) (rho c y)^ (last_edge c d y).

  Let right_product_cap_cell (a b s t c d : C) :=
    (ap (transport _ (jglue s t)) (eta_split_beta a b c d (joinl s))
      @ ap01D11 (eta_split_close a b c d) (jglue s t)
        (n3_inner_cell a b s t c)
        (cross_inner_cell a b s t c d))
      @ (eta_split_beta a b c d (joinr t))^.

  Let right_product_cap_cell_beta (a b s t c d : C)
    : apD (eta_inner a b c d) (jglue s t)
      = right_product_cap_cell a b s t c d.
  Proof.
    refine (apD_homotopic (eta_split_beta a b c d) (jglue s t) @ _).
    nrefine ((1 @@ _) @@ 1).
    lhs napply (apD_composeD2 (eta_split_close a b c d)
      (n3_inner a b c) (cross_inner a b c d) (jglue s t)).
    exact (ap011 (ap01D11 (eta_split_close a b c d) (jglue s t))
      (n3_inner_cell_beta a b s t c)
      (cross_inner_cell_beta a b s t c d)).
  Defined.

  (** This is the right-product analogue of [left_product_cap_comparison]. It first transposes the actual right-product cube, then combines it with the final inverse-translation cube by naturality on concatenated paths. *)
  Definition right_product_cap_comparison (a b s t c d : C)
    : right_product_cap_cell a b s t c d
      = eta_inner_cell a b s t c d
    := (right_product_cap_cell_beta a b s t c d)^
      @ eta_inner_cell_beta a b s t c d.

  (** Apply the normal form before varying the first two inputs. Its naturality combines both cap--product pairs and leaves the diagonal-equivariance contribution between the two [eta] terms. *)
  Let transported_associator (c d : C) (x y : J)
    := transport (fun z => mu (mu x y) z = mu x (mu y z))
      (jglue c d) (AL x y c).
  Definition eta_associator (c d : C) (x y : J)
    := ((eta c d (mu x y))^
        @ (cd_op_diagonal_equivariance c x y)^)
      @ ap (mu x) (eta c d y).
  Let transported_last_middle (a b c d : C) (y : J)
    := concat_Ap (fun x => transported_associator c d x y) (jglue a b).
  Definition eta_last_middle (a b c d : C) (y : J)
    := concat_Ap (fun x => eta_associator c d x y) (jglue a b).

  Definition last_middle_transport_normal_form
    (a b c d : C) (y : J)
    : transported_last_middle a b c d y
        @ ap (fun r => r @ ap (fun x => mu x (mu y (joinr d))) (jglue a b))
          (last_associator_transport_normal_form (joinl a) y c d)
      = ap (fun r => ap (fun x => mu (mu x y) (joinr d)) (jglue a b) @ r)
          (last_associator_transport_normal_form (joinr b) y c d)
        @ eta_last_middle a b c d y
    := concat_Ap_homotopic _ _
      (fun x => last_associator_transport_normal_form x y c d)
      (jglue a b).

  Definition last_middle_transport_cell_normal_form
    (a b s t c d : C)
    := apD (last_middle_transport_normal_form a b c d) (jglue s t).

  Let e0d a b d y := xf a b y (joinr d).
  Let e3d a b d y := xg a b y (joinr d).
  Let eh1 (c d : C) (x y : J) := (eta c d (mu x y))^.
  Let eh3 (c d : C) (x y : J) := ap (mu x) (eta c d y).
  Let en1 (a b c d : C) (y : J)
    := concat_Ap (fun x => eh1 c d x y) (jglue a b).
  Let en3 (a b c d : C) (y : J)
    := concat_Ap (fun x => eh3 c d x y) (jglue a b).

  Let en1_change (a b c d : C) (y : J)
    (n : ap (diagonal c) (W a b y) @ eta c d (mu (joinr b) y)
      = eta c d (mu (joinl a) y)
        @ ap (fun v => mu v (joinr d)) (W a b y))
    := (inverse_natural (e1 a b c y) (e0d a b d y)
      (naturality_change
        (ap_compose (fun x => mu x y) (diagonal c) (jglue a b))
        (ap_compose (fun x => mu x y) (fun v => mu v (joinr d))
          (jglue a b)) n))^.
  Let en1_beta (a b c d : C) (y : J)
    : en1 a b c d y
      = en1_change a b c d y (eta_left_inner a b c d y)
    := concat_Ap_inverse (fun x => eta c d (mu x y)) (jglue a b)
      @ ap (fun n => (inverse_natural (e1 a b c y) (e0d a b d y) n)^)
        (concat_Ap_precompose (eta c d) (fun x => mu x y) (jglue a b)).
  Let en1_cell (a b s t c d : C) :=
    (ap (transport _ (jglue s t)) (en1_beta a b c d (joinl s))
      @ ap01D1 (en1_change a b c d) (jglue s t)
        (eta_left_inner_cell a b s t c d))
      @ (en1_beta a b c d (joinr t))^.
  Let en1_cell_beta (a b s t c d : C)
    : apD (en1 a b c d) (jglue s t) = en1_cell a b s t c d.
  Proof.
    refine (apD_homotopic (en1_beta a b c d) (jglue s t) @ _).
    nrefine ((1 @@ _) @@ 1).
    refine (apD_composeD (en1_change a b c d)
      (eta_left_inner a b c d) (jglue s t) @ _).
    exact (ap (ap01D1 (en1_change a b c d) (jglue s t))
      (eta_left_inner_cell_beta a b s t c d)).
  Defined.

  Let en3_change (a b c d : C) (y : J)
    (n : ap (mu (joinl a)) (eta c d y) @ W a b (mu y (joinr d))
      = W a b (diagonal c y) @ ap (mu (joinr b)) (eta c d y)) := n^.
  Let en3_beta (a b c d : C) (y : J)
    : en3 a b c d y = en3_change a b c d y (eta_inner a b c d y)
    := concat_Ap_ap mu (jglue a b) (eta c d y).
  Let en3_cell (a b s t c d : C) :=
    (ap (transport _ (jglue s t)) (en3_beta a b c d (joinl s))
      @ ap01D1 (en3_change a b c d) (jglue s t)
        (eta_inner_cell a b s t c d))
      @ (en3_beta a b c d (joinr t))^.
  Let en3_cell_beta (a b s t c d : C)
    : apD (en3 a b c d) (jglue s t) = en3_cell a b s t c d.
  Proof.
    refine (apD_homotopic (en3_beta a b c d) (jglue s t) @ _).
    nrefine ((1 @@ _) @@ 1).
    refine (apD_composeD (en3_change a b c d)
      (eta_inner a b c d) (jglue s t) @ _).
    exact (ap (ap01D1 (en3_change a b c d) (jglue s t))
      (eta_inner_cell_beta a b s t c d)).
  Defined.

  Let eta_paste12 (a b c d : C) (y : J)
    (n : e0d a b d y @ eh1 c d (joinr b) y
      = eh1 c d (joinl a) y @ e1 a b c y)
    (m : e1 a b c y @ h2 c (joinr b) y
      = h2 c (joinl a) y @ e2 a b c y)
    := concat_natural (e0d a b d y) (e1 a b c y) (e2 a b c y)
      (eh1 c d (joinl a) y) (eh1 c d (joinr b) y)
      (h2 c (joinl a) y) (h2 c (joinr b) y) n m.
  Let eta_paste (a b c d : C) (y : J)
    (n : e0d a b d y
        @ (eh1 c d (joinr b) y @ h2 c (joinr b) y)
      = (eh1 c d (joinl a) y @ h2 c (joinl a) y) @ e2 a b c y)
    (m : e2 a b c y @ eh3 c d (joinr b) y
      = eh3 c d (joinl a) y @ e3d a b d y)
    := concat_natural (e0d a b d y) (e2 a b c y) (e3d a b d y)
      (eh1 c d (joinl a) y @ h2 c (joinl a) y)
      (eh1 c d (joinr b) y @ h2 c (joinr b) y)
      (eh3 c d (joinl a) y) (eh3 c d (joinr b) y) n m.
  Let eta_last_beta (a b c d : C) (y : J)
    : eta_last_middle a b c d y
      = eta_paste a b c d y
        (eta_paste12 a b c d y (en1 a b c d y) (n2 a b c y))
        (en3 a b c d y).
  Proof.
    lhs napply (concat_Ap_concat
      (fun x => eh1 c d x y @ h2 c x y)
      (fun x => eh3 c d x y) (jglue a b)).
    exact (ap (fun n => eta_paste a b c d y n (en3 a b c d y))
      (concat_Ap_concat (fun x => eh1 c d x y)
        (fun x => h2 c x y) (jglue a b))).
  Defined.

  Definition eta_last_associator_cell (a b s t c d : C) :=
    (ap (transport _ (jglue s t)) (eta_last_beta a b c d (joinl s))
      @ ap01D11 (eta_paste a b c d) (jglue s t)
        (ap01D11 (eta_paste12 a b c d) (jglue s t)
          (en1_cell a b s t c d)
          (n2_cell a b s t c (cd_op_diamond_diagonal a b s t c)))
        (en3_cell a b s t c d))
      @ (eta_last_beta a b c d (joinr t))^.

  Definition eta_last_associator_cell_beta (a b s t c d : C)
    : apD (eta_last_middle a b c d) (jglue s t)
      = eta_last_associator_cell a b s t c d.
  Proof.
    refine (apD_homotopic (eta_last_beta a b c d) (jglue s t) @ _).
    nrefine ((1 @@ _) @@ 1).
    lhs napply (apD_composeD2 (eta_paste a b c d)
      (fun y => eta_paste12 a b c d y
        (en1 a b c d y) (n2 a b c y))
      (en3 a b c d) (jglue s t)).
    napply (ap011 (ap01D11 (eta_paste a b c d) (jglue s t))).
    - lhs napply (apD_composeD2 (eta_paste12 a b c d)
        (en1 a b c d) (n2 a b c) (jglue s t)).
      exact (ap011 (ap01D11 (eta_paste12 a b c d) (jglue s t))
        (en1_cell_beta a b s t c d) (n2_cell_beta a b s t c)).
    - exact (en3_cell_beta a b s t c d).
  Defined.

  (** The duplicated product--translation block is now normalized. Transporting the last-left face produces a canonical right face built from [eta]. *)

  Definition eta_overlap_l (a c d : C) (y : J)
    : eta_associator c d (joinl a) y = BL a y (joinr d)
    := (last_associator_transport_normal_form (joinl a) y c d)^
      @ (ap (transport
          (fun z => mu (mu (joinl a) y) z = mu (joinl a) (mu y z))
          (jglue c d)) (ol a c y)
        @ apD (BL a y) (jglue c d)).

  Definition eta_overlap_r (b c d : C) (y : J)
    : eta_associator c d (joinr b) y = BR b y (joinr d)
    := (last_associator_transport_normal_form (joinr b) y c d)^
      @ (ap (transport
          (fun z => mu (mu (joinr b) y) z = mu (joinr b) (mu y z))
          (jglue c d)) (or b c y)
        @ apD (BR b y) (jglue c d)).

  Definition eta_overlap_m (s c d : C) (x : J)
    : eta_associator c d x (joinl s) = BM s x (joinr d)
    := (last_associator_transport_normal_form x (joinl s) c d)^
      @ (ap (transport
          (fun z => mu (mu x (joinl s)) z = mu x (mu (joinl s) z))
          (jglue c d))
          (S7MiddleScalar.overlap cd_diamond_susp s x c)
        @ apD (BM s x) (jglue c d)).

  Let eta_face_prefix (a b c d : C) (y : J)
    (n : e0d a b d y @ eta_associator c d (joinr b) y
      = eta_associator c d (joinl a) y @ e3d a b d y)
    (l : eta_associator c d (joinl a) y = BL a y (joinr d))
    := n @ ap (fun r => r @ e3d a b d y) l.
  Let eta_face_close (a b c d : C) (y : J)
    (r : eta_associator c d (joinr b) y = BR b y (joinr d))
    (n : e0d a b d y @ eta_associator c d (joinr b) y
      = BL a y (joinr d) @ e3d a b d y)
    := (ap (fun r => e0d a b d y @ r) r)^ @ n.

  Definition eta_face (a b c d : C) (y : J) : Gamma a b y (joinr d)
    := eta_face_close a b c d y (eta_overlap_r b c d y)
      (eta_face_prefix a b c d y (eta_last_middle a b c d y)
        (eta_overlap_l a c d y)).

  Let eta_face_prefix_cell (a b s t c d : C) :=
    ap01D11 (eta_face_prefix a b c d) (jglue s t)
      (eta_last_associator_cell a b s t c d)
      (apD (eta_overlap_l a c d) (jglue s t)).
  Definition eta_face_cell (a b s t c d : C) :=
    ap01D11 (eta_face_close a b c d) (jglue s t)
      (apD (eta_overlap_r b c d) (jglue s t))
      (eta_face_prefix_cell a b s t c d).

  Definition eta_face_cell_beta (a b s t c d : C)
    : apD (eta_face a b c d) (jglue s t)
      = eta_face_cell a b s t c d.
  Proof.
    unfold eta_face.
    lhs napply (apD_composeD2 (eta_face_close a b c d)
      (eta_overlap_r b c d)
      (fun y => eta_face_prefix a b c d y
        (eta_last_middle a b c d y) (eta_overlap_l a c d y))
      (jglue s t)).
    napply (ap011 (ap01D11 (eta_face_close a b c d) (jglue s t))).
    - reflexivity.
    - lhs napply (apD_composeD2 (eta_face_prefix a b c d)
        (eta_last_middle a b c d) (eta_overlap_l a c d) (jglue s t)).
      exact (ap011 (ap01D11 (eta_face_prefix a b c d) (jglue s t))
        (eta_last_associator_cell_beta a b s t c d) 1).
  Defined.

  Let eta_overlap_l_m (a s c d : C)
    : eta_overlap_l a c d (joinl s) = eta_overlap_m s c d (joinl a)
    := 1.
  Let eta_overlap_r_m (b s c d : C)
    : eta_overlap_r b c d (joinl s) = eta_overlap_m s c d (joinr b)
    := 1.

  (** On a left middle-input constructor, the transported [eta] face is the existing middle face. This uses the same middle overlap at both first-input endpoints. *)
  Definition eta_face_middle (a b s c d : C)
    : eta_face a b c d (joinl s) = face_y a b s (joinr d).
  Proof.
    exact (adjusted_naturality_homotopic (jglue a b)
      (fun x => eta_associator c d x (joinl s))
      (fun x => BM s x (joinr d)) (eta_overlap_m s c d)).
  Defined.

  (** This is the requested homotopy-first cancellation at the whole face: transport of the original last-left face is the [eta] face. The generic proof transports the adjusted naturality square once, rather than lifting the inner cube comparison through each outer correction separately. *)
  Definition eta_face_transport (a b c d : C) (y : J)
    : transport (fun z => Gamma a b y z) (jglue c d)
        (face_z a b y c) = eta_face a b c d y.
  Proof.
    exact (transport_adjusted_naturality
      (fun z x => mu (mu x y) z) (fun z x => mu x (mu y z))
      (jglue a b) (jglue c d)
      (fun x => AL x y c) (fun x => eta_associator c d x y)
      (fun z => BL a y z) (fun z => BR b y z)
      (ol a c y) (or b c y)
      (fun x => last_associator_transport_normal_form x y c d)).
  Defined.

  (** Naturality of adjusted naturality proves compatibility with the specified middle overlap and middle face. This is the 4-dimensional comparison left open after the separate cap calculations. *)
  Definition eta_face_middle_transport (a b s c d : C)
    : eta_face_middle a b s c d
      = (eta_face_transport a b c d (joinl s))^
        @ (ap (transport (Gamma a b (joinl s)) (jglue c d))
            (face_overlap a b s c)
          @ apD (face_y a b s) (jglue c d)).
  Proof.
    exact (transport_adjusted_naturality_homotopic
      (fun z x => mu (mu x (joinl s)) z)
      (fun z x => mu x (mu (joinl s) z))
      (jglue a b) (jglue c d)
      (fun x => AL x (joinl s) c)
      (fun x => eta_associator c d x (joinl s))
      (fun z x => BM s x z)
      (fun x => S7MiddleScalar.overlap cd_diamond_susp s x c)
      (fun x => last_associator_transport_normal_form x (joinl s) c d)).
  Defined.

  Definition eta_edge (a b s t c d : C)
    : U a b s t (joinr d) = eta_face a b c d (joinr t)
    := ap (transport (fun y => Gamma a b y (joinr d)) (jglue s t))
        (eta_face_middle a b s c d)^
      @ apD (eta_face a b c d) (jglue s t).

  (** The original normalized pasting followed by its [eta] edge is the pointwise transport comparison at the right middle-input constructor. *)
  Definition pasting_eta_factor (a b s t c d : C)
    : pasting a b s t c d @ eta_edge a b s t c d
      = eta_face_transport a b c d (joinr t).
  Proof.
    unfold pasting, image, eta_edge.
    lhs napply ((1 @@ (transported_face_glue a b s t c d)^) @@ 1).
    exact (transport_rectangle_factor (fun y z => Gamma a b y z)
      (jglue s t) (jglue c d)
      (fun y => face_z a b y c) (face_y a b s)
      (face_overlap a b s c) (eta_face a b c d)
      (eta_face_transport a b c d) (eta_face_middle a b s c d)
      (eta_face_middle_transport a b s c d)).
  Defined.

  Let last_paste12 (a b c : C) (y : J)
    (n : e0 a b c y @ h1 c (joinr b) y = h1 c (joinl a) y @ e1 a b c y)
    (m : e1 a b c y @ h2 c (joinr b) y = h2 c (joinl a) y @ e2 a b c y)
    := concat_natural (e0 a b c y) (e1 a b c y) (e2 a b c y)
      (h1 c (joinl a) y) (h1 c (joinr b) y)
      (h2 c (joinl a) y) (h2 c (joinr b) y) n m.
  Let last_paste (a b c : C) (y : J)
    (n : e0 a b c y @ (h1 c (joinr b) y @ h2 c (joinr b) y)
      = (h1 c (joinl a) y @ h2 c (joinl a) y) @ e2 a b c y)
    (m : e2 a b c y @ h3 c (joinr b) y = h3 c (joinl a) y @ e3 a b c y)
    := concat_natural (e0 a b c y) (e2 a b c y) (e3 a b c y)
      (h1 c (joinl a) y @ h2 c (joinl a) y)
      (h1 c (joinr b) y @ h2 c (joinr b) y)
      (h3 c (joinl a) y) (h3 c (joinr b) y) n m.
  Let last_beta (a b c : C) (y : J)
    : last_middle a b c y
      = last_paste a b c y
        (last_paste12 a b c y (n1 a b c y) (n2 a b c y)) (n3 a b c y).
  Proof.
    lhs napply (concat_Ap_concat (fun x => h1 c x y @ h2 c x y)
      (fun x => h3 c x y) (jglue a b)).
    exact (ap (fun n => last_paste a b c y n (n3 a b c y))
      (concat_Ap_concat (fun x => h1 c x y) (fun x => h2 c x y) (jglue a b))).
  Defined.

  (** The whole last-associator cube is now a pasting of two geometric naturality cubes and the original diagonal-equivariance cube. *)
  Definition last_associator_cell_from_diagonal (a b s t c : C)
    (delta : diagonal_input a b s t c) :=
    (ap (transport _ (jglue s t)) (last_beta a b c (joinl s))
      @ ap01D11 (last_paste a b c) (jglue s t)
        (ap01D11 (last_paste12 a b c) (jglue s t)
          (n1_cell a b s t c) (n2_cell a b s t c delta)) (n3_cell a b s t c))
      @ (last_beta a b c (joinr t))^.

  Definition last_associator_cell (a b s t c : C)
    := last_associator_cell_from_diagonal a b s t c
      (cd_op_diamond_diagonal a b s t c).

  Definition last_associator_cell_beta (a b s t c : C)
    : apD (last_middle a b c) (jglue s t) = last_associator_cell a b s t c.
  Proof.
    refine (apD_homotopic (last_beta a b c) (jglue s t) @ _).
    nrefine ((1 @@ _) @@ 1).
    lhs napply (apD_composeD2 (last_paste a b c)
      (fun y => last_paste12 a b c y (n1 a b c y) (n2 a b c y))
      (n3 a b c) (jglue s t)).
    napply (ap011 (ap01D11 (last_paste a b c) (jglue s t))).
    - lhs napply (apD_composeD2 (last_paste12 a b c)
        (n1 a b c) (n2 a b c) (jglue s t)).
      exact (ap011 (ap01D11 (last_paste12 a b c) (jglue s t))
        (n1_cell_beta a b s t c) (n2_cell_beta a b s t c)).
    - exact (n3_cell_beta a b s t c).
  Defined.

  Local Transparent cd_op cd_op_diamond.

  Let last_prefix a b c (y : J)
    (n : xf a b y (joinl c) @ AL (joinr b) y c
      = AL (joinl a) y c @ xg a b y (joinl c))
    (q : AL (joinl a) y c = BL a y (joinl c))
    := n @ ap (fun r => r @ xg a b y (joinl c)) q.
  Let last_close a b c (y : J)
    (q : AL (joinr b) y c = BR b y (joinl c))
    (n : xf a b y (joinl c) @ AL (joinr b) y c
      = BL a y (joinl c) @ xg a b y (joinl c))
    := (ap (fun r => xf a b y (joinl c) @ r) q)^ @ n.

  (** This pasting uses the computed last-associator cube and the two overlap eliminators' specified glue proofs, including their first-associator beta adjustments. *)
  Definition last_face_cell_from_diagonal (a b s t c : C)
    (delta : diagonal_input a b s t c)
    : transport (fun y => Gamma a b y (joinl c)) (jglue s t)
        (face_z a b (joinl s) c) = face_z a b (joinr t) c
    := ap01D11 (last_close a b c) (jglue s t) (or_cell b s t c)
      (ap01D11 (last_prefix a b c) (jglue s t)
        (last_associator_cell_from_diagonal a b s t c delta)
        (ol_cell a s t c)).

  Definition last_face_cell (a b s t c : C)
    := last_face_cell_from_diagonal a b s t c
      (cd_op_diamond_diagonal a b s t c).

  Definition last_face_cell_beta (a b s t c : C)
    : apD (fun y => face_z a b y c) (jglue s t) = last_face_cell a b s t c.
  Proof.
    lhs napply (apD_composeD2 (last_close a b c) (or b c)
      (fun y => last_prefix a b c y (last_middle a b c y) (ol a c y))
      (jglue s t)).
    napply (ap011 (ap01D11 (last_close a b c) (jglue s t))).
    - exact (Join_ind_beta_jglue _ _ _ _ s t).
    - lhs napply (apD_composeD2 (last_prefix a b c)
        (last_middle a b c) (ol a c) (jglue s t)).
      napply (ap011 (ap01D11 (last_prefix a b c) (jglue s t))).
      + exact (last_associator_cell_beta a b s t c).
      + exact (Join_ind_beta_jglue _ _ _ _ s t).
  Defined.

  Let computed_cap a b s t c (delta : diagonal_input a b s t c) :=
    ((last_face_cell_from_diagonal a b s t c delta)^
      @ ap (transport (fun y => Gamma a b y (joinl c)) (jglue s t))
        (face_overlap a b s c))
    @ face_transport_compute a b s t (joinl c).
  Let cap_expansion a b s t c
    : cap a b s t c @ face_transport_compute a b s t (joinl c)
      = computed_cap a b s t c (cd_op_diamond_diagonal a b s t c)
    := (inverse2 (last_face_cell_beta a b s t c) @@ 1) @@ 1.

  (** All four specified associator cubes, both overlap cubes, and the geometric naturality cubes now occur explicitly in the pasting. The remaining obligation is compatibility of these actual diamond pastings. *)
  Definition computed_pasting_from_diagonal (a b s t c d : C)
    (delta : diagonal_input a b s t c)
    : transport (Gamma a b (joinr t)) (jglue c d)
        (face_z a b (joinr t) c) = transported_face a b s t (joinr d)
    := ap (transport (Gamma a b (joinr t)) (jglue c d))
        (computed_cap a b s t c delta) @ transported_face_cell a b s t c d.

  Definition computed_pasting (a b s t c d : C)
    := computed_pasting_from_diagonal a b s t c d
      (cd_op_diamond_diagonal a b s t c).

  (** Attach the balanced--diagonal square to the actual last-left cap inside [computed_pasting]. The two [AL] overlap eliminators, the middle overlap, and the transport-interchange expansion are retained by [computed_pasting_from_diagonal]. *)
  Section BalancedCap.
    Local Open Scope mc_mult_scope.
    Local Existing Instance S7LeftScalar.circle_distropp.
    Context (s a b c d r : C).
    Let rt := fun z : C => z * r.
    Let Q := fun v : (C * C) * (C * C) =>
      zigzag@{Set Set Set} (fst (fst v)) (snd (fst v)) (fst (snd v))
        = zigzag (fst (fst v)) (snd (fst v)) (snd (snd v)).
    Let data (v : C * C) : sig Q :=
      (((a * fst v, (-snd v) * conj b), (conj a * snd v, fst v * b));
        cd_op_diamond@{Set} (X:=psphere 1) a b (fst v) (snd v)).
    Let source := data ((s * c) * r, (conj s * d) * r).
    Let target := functor_join_filler_data rt rt (data (s * c, conj s * d)).
    Let reassociation := ap data (path_prod'
      (simple_associativity (f:=sgop_s1) s c r)
      (simple_associativity (f:=sgop_s1) (conj s) d r)).
    Let alternate : source = target :=
      (S7MiddleScalar.diamond_path@{u} cd_diamond_susp s a b (c * r) (d * r)
        @ reassociation)^
      @ (S7MiddleScalar.diagonal_path cd_diamond_susp (a * s) (s * b) c d r
        @ ap (functor_join_filler_data rt rt)
          (S7MiddleScalar.diamond_path@{u} cd_diamond_susp s a b c d)).
    Let route : alternate
      = S7MiddleScalar.diagonal_path cd_diamond_susp a b (s * c) (conj s * d) r.
    Proof.
      unfold alternate.
      lhs napply (1 @@ S7MiddleScalar.diamond_translate_square_postcompose@{u}
        cd_diamond_susp s a b c d r).
      apply concat_V_pp.
    Defined.
    Let pl := path_prod'
      (cd_diamond_translate_l_neg_unit (X:=psphere 1) a (s * c) r)
      (cd_diamond_translate_l_parameter North b North (conj s * d) r).
    Let pr := path_prod'
      (cd_diamond_translate_r_parameter (X:=psphere 1) a North North (conj s * d) r)
      (cd_diamond_translate_r_unit b (s * c) r).
    Let beta := transport_path_prod' Q pl pr source.2.

    Definition computed_pasting_balanced_diagonal (e : C)
      (kappa : pr1_path alternate = path_prod' pl pr)
      : computed_pasting_from_diagonal a b (s * c) (conj s * d) r e
          (beta^ @ transport
            (fun p : source.1 = target.1 => transport Q p source.2 = target.2)
            kappa (pr2_path alternate))
        = computed_pasting a b (s * c) (conj s * d) r e.
    Proof.
      napply (ap (computed_pasting_from_diagonal a b (s * c) (conj s * d) r e)).
      lhs tapply (1 @@ path_sigma_fiber_square Q kappa (pr2_path alternate)
        (beta @ cd_op_diamond_diagonal (X:=psphere 1) a b (s * c) (conj s * d) r)
        (eta_path_sigma alternate @ route)).
      apply concat_V_pp.
    Defined.
  End BalancedCap.

  Definition pasting_expansion (a b s t c d : C)
    : pasting a b s t c d @ face_transport_compute a b s t (joinr d)
      = computed_pasting a b s t c d.
  Proof.
    lhs napply concat_pp_p.
    lhs napply (1 @@ transported_face_glue_expansion a b s t c d).
    lhs napply concat_p_pp.
    lhs_V napply (ap_pp (transport (Gamma a b (joinr t)) (jglue c d))
      (cap a b s t c) (face_transport_compute a b s t (joinl c)) @@ 1).
    exact (ap (ap (transport (Gamma a b (joinr t)) (jglue c d)))
      (cap_expansion a b s t c) @@ 1).
  Defined.

  (** The actual inner multiplication diamond changes the arbitrary final right label to the balanced--diagonal label. This comparison acts on the original complete pasting ratios: the cap adjustments and all five computed side cells are retained. The additional left vertex and the transport along the specified diamond remain explicit. *)
  Section InnerDiamondPasting.
    Local Open Scope mc_mult_scope.

    Let pasting_span (a b s t c c' d : C) :=
      (transport_pp (Gamma a b (joinr t)) (jglue c d) (jglue c' d)^
          (face_z a b (joinr t) c)
        @ ap (transport (Gamma a b (joinr t)) (jglue c' d)^)
          (computed_pasting a b s t c d @ (computed_pasting a b s t c' d)^))
      @ transport_Vp (Gamma a b (joinr t)) (jglue c' d)
        (face_z a b (joinr t) c').

    Definition computed_pasting_inner_diamond (a b v s t c d : C)
      : pasting_span a b v t c (conj s * ((-d) * conj t)) d
        = transport2 (Gamma a b (joinr t))
            (cd_op_diamond_pullback@{Set} (X:=psphere 1) s t c d)
            (face_z a b (joinr t) c)
          @ pasting_span a b v t c (conj s * ((-d) * conj t)) ((s * t) * c).
    Proof.
      napply (apD02_pV_beta (transported_face a b v t)
        (jglue c d) (jglue (conj s * ((-d) * conj t)) d)
        (jglue c ((s * t) * c))
        (jglue (conj s * ((-d) * conj t)) ((s * t) * c))
        (cd_op_diamond_pullback@{Set} (X:=psphere 1) s t c d)
        (computed_cap a b v t c
          (cd_op_diamond_diagonal (X:=psphere 1) a b v t c))
        (computed_cap a b v t (conj s * ((-d) * conj t))
          (cd_op_diamond_diagonal (X:=psphere 1) a b v t
            (conj s * ((-d) * conj t))))).
      - exact (1 @@ transported_face_cell_beta a b v t c d).
      - exact (1 @@ transported_face_cell_beta a b v t
          (conj s * ((-d) * conj t)) d).
      - exact (1 @@ transported_face_cell_beta a b v t c ((s * t) * c)).
      - exact (1 @@ transported_face_cell_beta a b v t
          (conj s * ((-d) * conj t)) ((s * t) * c)).
    Defined.

    (** The correction is independent of the chosen row, so it cancels when comparing two complete pasting ratios. This transports their difference; it does not assert that the difference vanishes. *)
    Definition computed_pasting_inner_diamond_difference (a b v w s t c d : C)
      : (pasting_span a b v t c (conj s * ((-d) * conj t)) d)^
          @ pasting_span a b w t c (conj s * ((-d) * conj t)) d
        = (pasting_span a b v t c (conj s * ((-d) * conj t)) ((s * t) * c))^
          @ pasting_span a b w t c (conj s * ((-d) * conj t)) ((s * t) * c).
    Proof.
      lhs napply (inverse2 (computed_pasting_inner_diamond a b v s t c d)
        @@ computed_pasting_inner_diamond a b w s t c d).
      lhs napply (inv_pp _ _ @@ 1).
      lhs napply concat_pp_p.
      exact (1 @@ concat_V_pp _ _).
    Defined.
  End InnerDiamondPasting.

  Definition eta_computed_edge (a b s t c d : C)
    : transported_face a b s t (joinr d)
      = eta_face a b c d (joinr t)
    := (face_transport_compute a b s t (joinr d))^
      @ eta_edge a b s t c d.

  (** This is the whole-face rewrite inside the existing [computed_pasting]. All original cell expansions remain on its left-hand side. *)
  Definition computed_pasting_eta_factor (a b s t c d : C)
    : computed_pasting a b s t c d @ eta_computed_edge a b s t c d
      = eta_face_transport a b c d (joinr t).
  Proof.
    unfold eta_computed_edge.
    lhs_V napply (pasting_expansion a b s t c d @@ 1).
    lhs napply concat_pp_p.
    lhs napply (1 @@ concat_p_pp _ _ _).
    lhs napply (1 @@ (concat_pV _ @@ 1)).
    lhs napply (1 @@ concat_1p _).
    exact (pasting_eta_factor a b s t c d).
  Defined.

  (** The source adjustment is independent of [c], so it cancels in each edge ratio. *)
  Definition eta_computed_edge_ratio (a b s t c d : C)
    : (eta_computed_edge a b s t c d)^
        @ eta_computed_edge a b s t North d
      = (eta_edge a b s t c d)^ @ eta_edge a b s t North d.
  Proof.
    unfold eta_computed_edge.
    lhs napply (inv_pp _ _ @@ 1).
    lhs napply concat_pp_p.
    exact (1 @@ concat_V_pp _ _).
  Defined.

  Let based_pasting_expansion a b s t c d
    : pasting a b s t c d @ (pasting a b s t North d)^
      = computed_pasting a b s t c d @ (computed_pasting a b s t North d)^
    := (concat_pV_pp (pasting a b s t c d) (pasting a b s t North d)
        (face_transport_compute a b s t (joinr d)))^
      @ (pasting_expansion a b s t c d
        @@ inverse2 (pasting_expansion a b s t North d)).

  (** The remaining equation compares these specific expanded pastings. This equivalence neither assumes the equation nor identifies arbitrary choices of any of its cubes. *)
  Definition equiv_mixed_expansion (a b s t c d : C)
    : (computed_pasting a b s t c d @ (computed_pasting a b s t North d)^
        = computed_pasting a b North t c d @ (computed_pasting a b North t North d)^)
      <~> Mixed a b s t c d
    := equiv_mixed_normalize a b s t c d oE equiv_concat_lr
      (based_pasting_expansion a b s t c d)
      (based_pasting_expansion a b North t c d)^.

End Normalization.
End S7DirectNormalization.
