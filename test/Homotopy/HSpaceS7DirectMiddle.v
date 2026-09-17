From HoTT Require Import Basics Types.Paths Types.Prod Types.Sigma Types.Universe.
From HoTT Require Import Pointed.Core Spaces.Spheres.
From HoTT Require Import Homotopy.CayleyDickson Homotopy.Suspension.
From HoTT Require Import Homotopy.HSpaceS1 Homotopy.HSpaceS3.
From HoTT Require Import Classes.interfaces.canonical_names.
From HoTT Require Import Homotopy.HSpaceS7.Direct.RightRightMiddle.
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

(** The whole right-middle comparison retains the constructor witnesses and the chosen mixed cube. These checks use the existing shared proof universe. *)
Section WholeMiddleChecks.
  Universe u.
  Context `{Univalence}.
  Local Existing Instances S7LeftScalar.circle_imaginaroid
    S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative
    S7LeftScalar.circle_commutative S7LeftScalar.circle_connected
    S7LeftScalar.circle_truncated.
  Local Notation C := (Sphere 1).
  Local Notation J := (Join@{Set Set Set} C C).
  Local Notation mu := (cd_op@{Set} (X:=psphere 1)).
  Local Notation MR := (S7RightRightMiddle.middle_r@{u}).

  Example eta_mr_joinl (t a c d : C)
    : D.eta_overlap_mr@{u} t c d (joinl a)
      = D.eta_overlap_l@{u} a c d (joinr t)
    := idpath.

  Example eta_mr_joinr (t b c d : C)
    : D.eta_overlap_mr@{u} t c d (joinr b)
      = D.eta_overlap_r@{u} b c d (joinr t)
    := idpath.

  Let right_beta (a b t : C) (z : J)
    : concat_Ap (fun x => MR t x z) (jglue a b)
      = S7RightRightMiddle.middle_r_glue@{u} t a b z
    := Join_ind_FlFr_beta_jglue
      (fun x => mu (mu x (joinr t)) z)
      (fun x => mu x (mu (joinr t) z))
      (fun a => MR t (joinl a) z) (fun b => MR t (joinr b) z)
      (fun a b => S7RightRightMiddle.middle_r_glue@{u} t a b z) a b.

  Example right_face_retained_cell (a b t c d : C)
    : apD (fun z => concat_Ap (fun x => MR t x z) (jglue a b)) (jglue c d)
      = (ap (transport (D.Gamma@{u} a b (joinr t)) (jglue c d))
          (right_beta a b t (joinl c))
        @ S7RightRightMiddle.middle_r_glue_glue@{u} t a b c d)
      @ (right_beta a b t (joinr d))^
    := D.right_face_glue@{u} a b t c d.

  Example balanced_cell_retains_diamond
    (D0 : CayleyDicksonDiamond (psphere 1)
      (@cds_negate (psphere 1) S7LeftScalar.circle_spheroid)) (s a b c d : C)
    : S7MiddleScalar.middle_l_glue_glue@{u} D0 s a b c d
      = S7MiddleScalar.middle_l_glue_glue_from_diamond D0 s a b c d
        (S7MiddleScalar.diamond@{u} D0 s a b c d)
    := idpath.

  Context (a b s t c d : C).
  Let E := D.equiv_mixed_middle_pasting@{u} a b s t c d.

  Example middle_pasting_roundtrip
    (q : (D.middle_pasting@{u} a b s t c d)^
          @ D.middle_pasting@{u} a b s t North d
        = (D.middle_pasting@{u} a b North t c d)^
          @ D.middle_pasting@{u} a b North t North d)
    : E^-1 (E q) = q
    := eissect E q.

  Example original_mixed_roundtrip (m : D.Mixed@{u} a b s t c d)
    : E (E^-1 m) = m
    := eisretr E m.
End WholeMiddleChecks.

(** The completed scalar square has no elementary surrogate edge or leftover composition adjustment, and uses the existing proof universe. *)
Section CompletedDiamondChecks.
  Universe u.
  Context `{Univalence}.
  Local Open Scope mc_mult_scope.
  Local Existing Instances S7LeftScalar.circle_imaginaroid
    S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative
    S7LeftScalar.circle_commutative S7LeftScalar.circle_distropp
    S7LeftScalar.circle_connected S7LeftScalar.circle_truncated.
  Local Notation C := (Sphere 1).
  Local Notation assoc := (simple_associativity (f:=sgop_s1)).
  Context (D0 : CayleyDicksonDiamond (psphere 1) (-)) (s a b c d r : C).
  Let Q := fun v : (C * C) * (C * C) =>
    zigzag@{Set Set Set} (fst (fst v)) (snd (fst v)) (fst (snd v))
      = zigzag (fst (fst v)) (snd (fst v)) (snd (snd v)).
  Let data (v : C * C) : sig Q :=
    (((a * fst v, (-snd v) * conj b), (conj a * snd v, fst v * b));
      @cd_op_diamond@{Set} (psphere 1) S7LeftScalar.circle_spheroid
        S7LeftScalar.circle_associative D0 a b (fst v) (snd v)).

  Example original_balanced_diagonal_square
    : S7MiddleScalar.diagonal_path D0 (a * s) (s * b) c d r
        @ ap (functor_join_filler_data (fun z : C => z * r) (fun z : C => z * r))
          (S7MiddleScalar.diamond_path@{u} D0 s a b c d)
      = (S7MiddleScalar.diamond_path@{u} D0 s a b (c * r) (d * r)
          @ ap data (path_prod' (assoc s c r) (assoc (conj s) d r)))
        @ S7MiddleScalar.diagonal_path D0 a b (s * c) (conj s * d) r
    := S7MiddleScalar.diamond_translate_square_postcompose@{u} D0 s a b c d r.
End CompletedDiamondChecks.

(** Packaging a filler change retains its specified boundary paths, not only its endpoint vertices. *)
Section FillerBoundaryCheck.
  Context {X C E : Type} {n e : X}
    (h : forall t, zigzag n t t = zigzag n t e)
    {f f' : X -> C} {g g' : X -> E}
    (pf : f == f') (pg : g == g') {t t' : X} (p_t : t = t')
    {c c' k k' : C} {d d' l l' : E}
    (p : f n = c) (q : f t = c') (r : g t = d) (s : g e = d')
    (p' : f' n = k) (q' : f' t' = k')
    (r' : g' t' = l) (s' : g' e = l').

  Example filler_change_keeps_boundaries
    : ap pr1 (join_zigzag_filler_change_path h pf pg p_t
        p q r s p' q' r' s')
      = path_prod'
        (path_prod' (p^ @ pf n @ p') (q^ @ (pf t @ ap f' p_t) @ q'))
        (path_prod' (r^ @ (pg t @ ap g' p_t) @ r') (s^ @ pg e @ s')).
  Proof.
    apply ap_pr1_path_sigma.
  Defined.
End FillerBoundaryCheck.
