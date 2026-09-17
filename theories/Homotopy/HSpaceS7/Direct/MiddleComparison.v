From HoTT Require Import Basics.
Require Import Types.Paths Types.Universe.
Require Import Pointed.Core Spaces.Spheres.
Require Import Homotopy.HSpaceS3 Homotopy.CayleyDickson Homotopy.Suspension.
Require Import Homotopy.Join.Core Homotopy.Join.Rec2.
Require Import Homotopy.HSpaceS7.LeftScalar Homotopy.HSpaceS7.MiddleScalar.
Require Import Homotopy.HSpaceS7.Direct.Core.
Require Import Homotopy.HSpaceS7.Direct.Normalization.
Require Import Homotopy.HSpaceS7.Direct.RightRightMiddle.
Require Import Homotopy.HSpaceS7.Direct.RightRightComparison.

Local Set Universe Minimization ToSet.
Local Open Scope pointed_scope.
Local Open Scope path_scope.

(** * The two computed middle faces in the original mixed boundary *)
Module S7DirectMiddle.
Include S7DirectRightRight.
Section Comparison.
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
  Local Notation Gamma := (S7DirectCore.Gamma@{u}).
  Local Notation face_y := (S7DirectCore.face_y@{u}).
  Local Notation face_z := (S7DirectCore.face_z@{u}).
  Local Notation face_overlap := (S7DirectCore.face_overlap@{u}).
  Local Notation eta_associator := (S7DirectNormalization.eta_associator@{u}).
  Local Notation eta_face := (S7DirectNormalization.eta_face@{u}).
  Local Notation eta_edge := (S7DirectNormalization.eta_edge@{u}).
  Local Notation BM := (S7MiddleScalar.middle_l@{u} cd_diamond_susp).
  Local Notation MR := (S7RightRightMiddle.middle_r@{u}).

  (** Retain the whole right-middle associator, rather than replacing its right column by [cd_assoc_rr]. The first-input point clauses are literally [eta_overlap_l/r]. *)
  Definition eta_overlap_mr (t c d : C) (x : J)
    : eta_associator c d x (joinr t) = MR t x (joinr d)
    := (last_associator_transport_normal_form@{u} x (joinr t) c d)^
      @ (ap (transport
          (fun z => mu (mu x (joinr t)) z = mu x (mu (joinr t) z))
          (jglue c d)) (S7RightRightMiddle.overlap@{u} t x c)
        @ apD (MR t x) (jglue c d)).

  Let right_face (a b t : C) (z : J) : Gamma a b (joinr t) z
    := concat_Ap (fun x => MR t x z) (jglue a b).
  Let right_overlap (a b t c : C)
    : face_z a b (joinr t) c = right_face a b t (joinl c)
    := adjusted_naturality_homotopic (jglue a b)
      (fun x => AL x (joinr t) c) (fun x => MR t x (joinl c))
      (fun x => S7RightRightMiddle.overlap@{u} t x c).
  Let eta_right (a b t c d : C)
    : eta_face a b c d (joinr t) = right_face a b t (joinr d)
    := adjusted_naturality_homotopic (jglue a b)
      (fun x => eta_associator c d x (joinr t))
      (fun x => MR t x (joinr d)) (eta_overlap_mr t c d).

  (** The right overlap has the same transport coherence as the prescribed left overlap, now using the actual right-middle section throughout the last-input path. *)
  Definition eta_right_transport (a b t c d : C)
    : eta_right a b t c d
      = (eta_face_transport@{u} a b c d (joinr t))^
        @ (ap (transport (Gamma a b (joinr t)) (jglue c d))
            (right_overlap a b t c)
          @ apD (right_face a b t) (jglue c d)).
  Proof.
    exact (transport_adjusted_naturality_homotopic
      (fun z x => mu (mu x (joinr t)) z)
      (fun z x => mu x (mu (joinr t) z))
      (jglue a b) (jglue c d)
      (fun x => AL x (joinr t) c)
      (fun x => eta_associator c d x (joinr t))
      (fun z x => MR t x z)
      (fun x => S7RightRightMiddle.overlap@{u} t x c)
      (fun x => last_associator_transport_normal_form@{u} x (joinr t) c d)).
  Defined.

  Let right_beta (a b t : C) (z : J)
    : right_face a b t z = S7RightRightMiddle.middle_r_glue@{u} t a b z
    := Join_ind_FlFr_beta_jglue
      (fun x => mu (mu x (joinr t)) z)
      (fun x => mu x (mu (joinr t) z))
      (fun a => MR t (joinl a) z) (fun b => MR t (joinr b) z)
      (fun a b => S7RightRightMiddle.middle_r_glue@{u} t a b z) a b.
  Let right_cell (a b t c d : C) :=
    (ap (transport (Gamma a b (joinr t)) (jglue c d))
        (right_beta a b t (joinl c))
      @ S7RightRightMiddle.middle_r_glue_glue@{u} t a b c d)
    @ (right_beta a b t (joinr d))^.

  Definition right_face_glue (a b t c d : C)
    : apD (right_face a b t) (jglue c d) = right_cell a b t c d.
  Proof.
    exact (Join_ind_FlFr_ind_beta_jglue_jglue
      (fun x z => mu (mu x (joinr t)) z)
      (fun x z => mu x (mu (joinr t) z))
      (fun a z => MR t (joinl a) z) (fun b z => MR t (joinr b) z)
      (fun a b c => concat_Ap (cd_assoc_rl@{Set} t c) (jglue a b))
      (fun a b d => concat_Ap (cd_assoc_rr@{Set} t d) (jglue a b))
      (S7RightRightMiddle.middle_r_glue_glue@{u} t) a b c d).
  Defined.

  Let U (a b s t : C) (z : J) :=
    transport (fun y => Gamma a b y z) (jglue s t) (face_y a b s z).
  Let cap (a b s t c : C) :=
    Join_ind2_from_left_overlap_r (Gamma a b) s
      (face_y a b) (face_z a b) (face_overlap a b) t c.
  Let boundary (a b s t c : C)
    : U a b s t (joinl c) = right_face a b t (joinl c)
    := (cap a b s t c)^ @ right_overlap a b t c.

  (** This is the last-left rectangle between the two chosen middle faces, transported to the last-right constructor. Its source and target retain both middle associators. *)
  Definition middle_pasting (a b s t c d : C)
    : U a b s t (joinr d) = right_face a b t (joinr d)
    := transport (fun z => U a b s t z = right_face a b t z)
      (jglue c d) (boundary a b s t c).

  Definition middle_pasting_eta (a b s t c d : C)
    : middle_pasting a b s t c d
      = eta_edge a b s t c d @ eta_right a b t c d.
  Proof.
    exact (transport_rectangle_boundary (Gamma a b)
      (jglue s t) (jglue c d)
      (fun y => face_z a b y c) (face_y a b s) (right_face a b t)
      (face_overlap a b s c) (right_overlap a b t c)
      (eta_face a b c d) (eta_face_transport@{u} a b c d)
      (eta_face_middle@{u} a b s c d) (eta_right a b t c d)
      (eta_face_middle_transport@{u} a b s c d)
      (eta_right_transport a b t c d)).
  Defined.

  Let left_beta (a b s : C) (z : J)
    : face_y a b s z = S7MiddleScalar.middle_l_glue@{u} cd_diamond_susp s a b z
    := Join_ind_FlFr_beta_jglue
      (fun x => mu (mu x (joinl s)) z)
      (fun x => mu x (mu (joinl s) z))
      (fun a => BM s (joinl a) z) (fun b => BM s (joinr b) z)
      (fun a b => S7MiddleScalar.middle_l_glue@{u} cd_diamond_susp s a b z) a b.
  Let left_cell (a b s t c d : C) :=
    transport_transport (Gamma a b) (jglue s t) (jglue c d)
      (face_y a b s (joinl c))
    @ ap (transport (fun y => Gamma a b y (joinr d)) (jglue s t))
      ((ap (transport (Gamma a b (joinl s)) (jglue c d))
          (left_beta a b s (joinl c))
        @ S7MiddleScalar.middle_l_glue_glue_from_diamond
          cd_diamond_susp s a b c d
          (S7MiddleScalar.diamond@{u} cd_diamond_susp s a b c d))
      @ (left_beta a b s (joinr d))^).

  (** Both side cubes occur with their original beta corrections. In particular, the right cube contains the checked rotation of the multiplication diamond. *)
  Definition middle_pasting_compute (a b s t c d : C)
    : middle_pasting a b s t c d
      = ((left_cell a b s t c d)^
        @ ap (transport (Gamma a b (joinr t)) (jglue c d))
            (boundary a b s t c)) @ right_cell a b t c d.
  Proof.
    lhs napply (transport_paths_FlFr_D
      (f:=U a b s t) (g:=right_face a b t) (jglue c d) _).
    exact ((inverse2 (transported_face_glue@{u} a b s t c d) @@ 1)
      @@ right_face_glue a b t c d).
  Defined.

  (** Attach the computed right-middle rectangle to the original expanded pasting. What remains is precisely its last-left overlap followed by the rotated-diamond cube, including the recursor beta corrections. *)
  Definition computed_pasting_right_factor (a b s t c d : C)
    : computed_pasting@{u} a b s t c d
        @ ((face_transport_compute@{u} a b s t (joinr d))^
          @ middle_pasting a b s t c d)
      = ap (transport (Gamma a b (joinr t)) (jglue c d))
          (right_overlap a b t c) @ right_cell a b t c d.
  Proof.
    lhs napply (1 @@ (1 @@ middle_pasting_eta a b s t c d)).
    lhs napply (1 @@ concat_p_pp _ _ _).
    lhs napply concat_p_pp.
    lhs napply (computed_pasting_eta_factor@{u} a b s t c d @@ 1).
    lhs napply (1 @@ eta_right_transport a b t c d).
    lhs napply concat_p_Vp.
    exact (1 @@ right_face_glue a b t c d).
  Defined.

  Local Opaque right_cell right_overlap.

  (** This is equivalent to the original [Mixed], not a replacement boundary condition. Both common right factors cancel before the existing transport-interchange expansion is used. No right-middle cube or overlap is unfolded. *)
  Definition equiv_mixed_middle_pasting (a b s t c d : C)
    : ((middle_pasting a b s t c d)^ @ middle_pasting a b s t North d
        = (middle_pasting a b North t c d)^
          @ middle_pasting a b North t North d)
      <~> Mixed@{u} a b s t c d.
  Proof.
    pose (P := fun s c =>
      ap (transport (Gamma a b (joinr t)) (jglue c d)) (cap a b s t c)
        @ left_cell a b s t c d).
    pose (R := fun c =>
      ap (transport (Gamma a b (joinr t)) (jglue c d))
        (right_overlap a b t c) @ right_cell a b t c d).
    assert (factor : forall s c,
      middle_pasting a b s t c d = (P s c)^ @ R c).
    { intros s0 c0.
      lhs napply (middle_pasting_compute a b s0 t c0 d).
      lhs napply ((1 @@ ap_pp _ _ _) @@ 1).
      lhs napply ((1 @@ (ap_V _ _ @@ 1)) @@ 1).
      lhs napply (concat_p_pp _ _ _ @@ 1).
      rhs napply (inv_pp _ _ @@ 1).
      apply concat_pp_p. }
    assert (cancel_right : forall s,
      (middle_pasting a b s t c d)^ @ middle_pasting a b s t North d
        = (R c)^ @ (P s c @ (P s North)^) @ R North).
    { intro s0.
      lhs napply (inverse2 (factor s0 c) @@ factor s0 North).
      lhs napply (inv_pp _ _ @@ 1).
      lhs napply ((1 @@ inv_V _) @@ 1).
      lhs napply concat_p_pp.
      exact (concat_pp_p _ _ _ @@ 1). }
    assert (expand : forall s,
      P s c @ (P s North)^
        = computed_pasting@{u} a b s t c d
          @ (computed_pasting@{u} a b s t North d)^).
    { intro s0.
      lhs_V napply (concat_pV_pp (P s0 c) (P s0 North)
        (face_transport_compute@{u} a b s0 t (joinr d))).
      exact (pasting_expansion@{u} a b s0 t c d
        @@ inverse2 (pasting_expansion@{u} a b s0 t North d)). }
    refine (equiv_mixed_expansion@{u} a b s t c d oE _).
    refine (equiv_concat_lr (expand s)^ (expand North) oE _).
    refine ((equiv_ap (concat_lr (R c)^ (R North)) _ _)^-1 oE _).
    exact (equiv_concat_lr (cancel_right s)^ (cancel_right North)).
  Defined.
End Comparison.
End S7DirectMiddle.
