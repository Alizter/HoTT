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

  Example last_face_retains_diagonal (a b s t c : C)
    : D.last_face_cell@{u} a b s t c
      = D.last_face_cell_from_diagonal@{u} a b s t c
        (cd_op_diamond_diagonal@{Set} (X:=psphere 1) a b s t c)
    := idpath.

  Example original_pasting_retains_diagonal (a b s t c d : C)
    : D.computed_pasting@{u} a b s t c d
      = D.computed_pasting_from_diagonal@{u} a b s t c d
        (cd_op_diamond_diagonal@{Set} (X:=psphere 1) a b s t c)
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

(** Checkpoint (A): decoding the unchanged middle constructor recovers an arbitrary balanced comparison, not just the selected diamond. The decoder is the inverse built from the actual conversion equivalences. *)
Section MiddleCubeDecoding.
  Context `{Univalence}.
  Local Open Scope mc_mult_scope.
  Local Open Scope path_scope.
  Local Existing Instances S7LeftScalar.circle_imaginaroid
    S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative
    S7LeftScalar.circle_commutative S7LeftScalar.circle_distropp.
  Local Notation C := (Sphere 1).
  Context (D0 : CayleyDicksonDiamond (psphere 1) (-)) (s a b c d : C).
  Let convert := S7MiddleScalar.middle_l_glue_glue_from_diamond D0 s a b c d.
  (** Read the small domain and codomain of the unchanged constructor without depending on its private scalar-boundary names. *)
  Let Input : Type0 := ltac:(let T := type of convert in
    lazymatch T with ?I -> _ => exact I end).
  Let Output : Type0 := ltac:(let T := type of convert in
    lazymatch T with _ -> ?O => exact O end).
  Let E := S7MiddleScalar.equiv_middle_l_glue_glue_from_diamond D0 s a b c d.
  Let decode_middle := E^-1.

  Example middle_equivalence_forward (beta : Input)
    : E beta = S7MiddleScalar.middle_l_glue_glue_from_diamond D0 s a b c d beta
    := idpath.

  Example decode_middle_roundtrip (beta : Input)
    : decode_middle
        (S7MiddleScalar.middle_l_glue_glue_from_diamond D0 s a b c d beta)
      = beta
    := eissect E beta.

  Example decode_selected_middle
    : decode_middle (S7MiddleScalar.middle_l_glue_glue@{u} D0 s a b c d)
      = S7MiddleScalar.diamond@{u} D0 s a b c d
    := eissect E (S7MiddleScalar.diamond@{u} D0 s a b c d).

  Example encode_middle_roundtrip (cube : Output)
    : convert (decode_middle cube) = cube := eisretr E cube.

  Example decode_middle_comparison {beta gamma : Input} (q : beta = gamma)
    : (equiv_ap E beta gamma)^-1 (ap convert q) = q
    := eissect (equiv_ap E beta gamma) q.

  Example encode_middle_comparison {beta gamma : Input} (q : E beta = E gamma)
    : ap convert ((equiv_ap E beta gamma)^-1 q) = q
    := eisretr (equiv_ap E beta gamma) q.
End MiddleCubeDecoding.

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

(** The completed square acts on the diagonal factor of the actual [AL] cap, inside the original expanded pasting. The last-right label remains arbitrary. *)
Section ActualCapChecks.
  Universe u.
  Context `{Univalence}.
  Local Open Scope mc_mult_scope.
  Local Existing Instances S7LeftScalar.circle_imaginaroid
    S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative
    S7LeftScalar.circle_commutative S7LeftScalar.circle_distropp
    S7LeftScalar.circle_connected S7LeftScalar.circle_truncated.
  Local Notation C := (Sphere 1).
  Local Notation assoc := (simple_associativity (f:=sgop_s1)).
  Context (s a b c d r e : C).
  Let rt := fun z : C => z * r.
  Let Q := fun v : (C * C) * (C * C) =>
    zigzag@{Set Set Set} (fst (fst v)) (snd (fst v)) (fst (snd v))
      = zigzag (fst (fst v)) (snd (fst v)) (snd (snd v)).
  Let data (v : C * C) : sig Q :=
    (((a * fst v, (-snd v) * conj b), (conj a * snd v, fst v * b));
      cd_op_diamond@{Set} (X:=psphere 1) a b (fst v) (snd v)).
  Let source := data ((s * c) * r, (conj s * d) * r).
  Let target := functor_join_filler_data rt rt (data (s * c, conj s * d)).
  Let alternate : source = target :=
    (S7MiddleScalar.diamond_path@{u} cd_diamond_susp s a b (c * r) (d * r)
      @ ap data (path_prod' (assoc s c r) (assoc (conj s) d r)))^
    @ (S7MiddleScalar.diagonal_path cd_diamond_susp (a * s) (s * b) c d r
      @ ap (functor_join_filler_data rt rt)
        (S7MiddleScalar.diamond_path@{u} cd_diamond_susp s a b c d)).
  Let pl := path_prod'
    (cd_diamond_translate_l_neg_unit (X:=psphere 1) a (s * c) r)
    (cd_diamond_translate_l_parameter North b North (conj s * d) r).
  Let pr := path_prod'
    (cd_diamond_translate_r_parameter (X:=psphere 1) a North North (conj s * d) r)
    (cd_diamond_translate_r_unit b (s * c) r).
  Let beta := transport_path_prod' Q pl pr source.2.

  Example original_cap_attachment
    (kappa : pr1_path alternate = path_prod' pl pr)
    : D.computed_pasting_from_diagonal@{u} a b (s * c) (conj s * d) r e
        (beta^ @ transport
          (fun p : source.1 = target.1 => transport Q p source.2 = target.2)
          kappa (pr2_path alternate))
      = D.computed_pasting@{u} a b (s * c) (conj s * d) r e
    := D.computed_pasting_balanced_diagonal@{u} s a b c d r e kappa.
End ActualCapChecks.

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

(** The actual inner diamond acts on the complete pasting ratios. Its geometric parameter and the selected middle-face row are independent, so the same square applies to the given row and the unit row. *)
Section InnerDiamondChecks.
  Universe u.
  Context `{Univalence}.
  Local Open Scope mc_mult_scope.
  Local Existing Instances S7LeftScalar.circle_imaginaroid
    S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative
    S7LeftScalar.circle_commutative S7LeftScalar.circle_distropp
    S7LeftScalar.circle_connected S7LeftScalar.circle_truncated.
  Local Notation C := (Sphere 1).
  Context (a b s t c d : C).
  Let c' := conj s * ((-d) * conj t).
  Let e := (s * t) * c.
  Let P := D.Gamma@{u} a b (joinr t).
  Let bottom := D.face_z@{u} a b (joinr t).
  Let span (v z : C) :=
    (transport_pp P (jglue c z) (jglue c' z)^ (bottom c)
      @ ap (transport P (jglue c' z)^)
        (D.computed_pasting@{u} a b v t c z
          @ (D.computed_pasting@{u} a b v t c' z)^))
    @ transport_Vp P (jglue c' z) (bottom c').

  Example changed_final_label (v : C)
    : span v d
      = transport2 P (cd_op_diamond_pullback@{Set} (X:=psphere 1) s t c d)
          (bottom c) @ span v e
    := D.computed_pasting_inner_diamond@{u} a b v s t c d.

  Example original_and_unit_row_difference
    : (span s d)^ @ span North d = (span s e)^ @ span North e
    := D.computed_pasting_inner_diamond_difference@{u}
      a b s North s t c d.
End InnerDiamondChecks.

(** The geometric parameter is independent of both rows. Its scalar inverse law changes the anchor, and associativity plus the other inverse law changes the right label; the entire dependent difference is transported along both paths. *)
Section PastingDifferenceChecks.
  Universe u.
  Context `{Univalence}.
  Local Open Scope mc_mult_scope.
  Local Open Scope path_scope.
  Local Existing Instances S7LeftScalar.circle_imaginaroid
    S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative
    S7LeftScalar.circle_commutative S7LeftScalar.circle_distropp
    S7LeftScalar.circle_connected S7LeftScalar.circle_truncated.
  Local Notation C := (Sphere 1).
  Context (a b v w t c d : C).
  Let P := D.Gamma@{u} a b (joinr t).
  Let bottom := D.face_z@{u} a b (joinr t).
  Let span (row k z : C) :=
    (transport_pp P (jglue c z) (jglue k z)^ (bottom c)
      @ ap (transport P (jglue k z)^)
        (D.computed_pasting@{u} a b row t c z
          @ (D.computed_pasting@{u} a b row t k z)^))
    @ transport_Vp P (jglue k z) (bottom k).

  Example whole_pasting_difference (k : C)
    : (span v k d)^ @ span w k d
      = ((transport_Vp P (jglue k d) (bottom k))^
        @ ap (transport P (jglue k d)^)
          ((D.computed_pasting@{u} a b v t k d
              @ (D.computed_pasting@{u} a b v t c d)^)
            @ (D.computed_pasting@{u} a b w t c d
              @ (D.computed_pasting@{u} a b w t k d)^)))
        @ transport_Vp P (jglue k d) (bottom k)
    := D.computed_pasting_span_difference@{u} a b v w t c k d.

  Example unit_anchor_difference
    : (span v North d)^ @ span w North d
      = (span v North ((-d) * c))^ @ span w North ((-d) * c)
    := D.computed_pasting_unit_anchor_difference@{u} a b v w t c d.

  Example unit_anchor_retains_scalar_transport
    : D.computed_pasting_unit_anchor_difference@{u} a b v w t c d
      = transport011
        (fun k z : C => (span v k d)^ @ span w k d
          = (span v k z)^ @ span w k z)
        (cds_conjug_left_inv (X:=psphere 1) ((-d) * conj t))
        (ap (.* c) ((simple_associativity (f:=sgop_s1) (-d) (conj t) t)^
          @ (ap ((-d) *.) (cds_conjug_left_inv t) @ right_identity (-d))))
        (D.computed_pasting_inner_diamond_difference@{u}
          a b v w ((-d) * conj t) t c d)
    := idpath.

  (** This also checks that substitution in the complete aligned difference retains the shared proof universe. The explicit source is the original span difference; its target is the expanded four-pasting expression from the theorem. *)
  Example aligned_whole_difference (k : C)
    : (span v k ((v * t) * c))^ @ span w k ((v * t) * c) = _
    := D.computed_pasting_aligned_difference@{u} a b v w t c k.
End PastingDifferenceChecks.

(** The aligned computation keeps the scalar boundary, the original multiplication square, and the chosen mixed recursor beta. *)
Section AlignedInnerChecks.
  Universe u.
  Context `{Univalence}.
  Local Open Scope mc_mult_scope.
  Local Open Scope path_scope.
  Local Existing Instances S7LeftScalar.circle_imaginaroid
    S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative
    S7LeftScalar.circle_commutative S7LeftScalar.circle_connected
    S7LeftScalar.circle_truncated.
  Local Notation C := (Sphere 1).
  Local Notation J := (Join@{Set Set Set} C C).
  Local Notation mu := (cd_op@{Set} (X:=psphere 1)).
  Local Notation assoc := (simple_associativity (f:=sgop_s1)).
  Local Notation comm := (commutativity (f:=sgop_s1)).
  Let W (s t : C) (z : J) := ap (fun y => mu y z) (jglue s t).
  Let bh0 (s c d : C) : ap (mu (joinl s)) (jglue c d) = _
    := Join_rec_beta_jglue _ _ _ c d.
  Let bh1 (t c d : C) : ap (mu (joinr t)) (jglue c d) = _
    := Join_rec_beta_jglue _ _ _ c d.
  Let bv0 (s t c : C) : W s t (joinl c) = _
    := Join_rec_beta_jglue _ _ _ s t.
  Let bv1 (s t d : C) : W s t (joinr d) = _
    := Join_rec_beta_jglue _ _ _ s t.
  Let square (s t c d : C)
    (delta : zigzag (s * c) ((-d) * conj t) (conj s * d)
      = zigzag (s * c) ((-d) * conj t) (c * t)) :=
    ((1 @@ bv1 s t d) @ ((bh0 s c d @@ 1)
      @ (delta @ (1 @@ bh1 t c d)^))) @ (bv0 s t c @@ 1)^.
  Let square_beta (s t c d : C)
    : concat_Ap (W s t) (jglue c d)
      = square s t c d (cd_op_diamond@{Set} (X:=psphere 1) s t c d).
  Proof.
    napply moveL_pV.
    exact (Join_rec2_beta_jglue_jglue J _ _ _ _ _ _ _ _
      (cd_op_diamond@{Set} (X:=psphere 1)) s t c d).
  Defined.

  Example right_product_keeps_original_square (a b s t c d : C)
    : D.right_product_cell@{u} a b s t c d
      = D.right_product_cell_from_square@{u} a b s t c d
        (square s t c d (cd_op_diamond@{Set} (X:=psphere 1) s t c d))
        (square_beta s t c d)
    := idpath.

  Context (a b s t c : C).
  Let e := (s * t) * c.
  Let boundary := ap (conj s *.) ((assoc s t c)^ @ ap (s *.) (comm t c))
    @ ((assoc (conj s) s (c * t)
      @ ap (.* (c * t)) (cds_conjug_left_inv s)) @ left_identity (c * t)).

  Example aligned_boundary_unchanged
    : S7MiddleScalar.inner_diamond_boundary s t c = boundary := idpath.

  Example aligned_scalar_attachment
    : path_prod' (assoc s North c) (assoc (conj s) (s * t) c)
        @ ap (fun v : C * C => (fst v * c, snd v * c))
          (path_prod' (right_identity s)
            ((assoc (conj s) s t @ ap (.* t) (cds_conjug_left_inv s))
              @ left_identity t))
      = path_prod' 1 (boundary @ comm c t)
    := S7MiddleScalar.aligned_boundary_coherence@{u} s t c.

  Example actual_aligned_diamond
    : cd_op_diamond@{Set} (X:=psphere 1) s t c e
      = diamond_v (s * c) ((-e) * conj t) boundary
    := S7MiddleScalar.inner_diamond_aligned@{u} s t c.

  Example actual_aligned_right_product
    : D.right_product_cell@{u} a b s t c e
      = D.right_product_cell_from_square@{u} a b s t c e
        (square s t c e (diamond_v (s * c) ((-e) * conj t) boundary))
        (square_beta s t c e @ ap (square s t c e)
          (S7MiddleScalar.inner_diamond_aligned@{u} s t c))
    := D.right_product_cell_aligned@{u} a b s t c.
End AlignedInnerChecks.

(** The aligned square uses the original cap labels and the original middle-cell label, with an arbitrary chosen diamond. The scalar correction is the boundary from the actual aligned inner computation, not a new identification of filler endpoints. *)
Section AlignedBalancedChecks.
  Universe u.
  Context `{Univalence}.
  Local Open Scope mc_mult_scope.
  Local Open Scope path_scope.
  Local Existing Instances S7LeftScalar.circle_imaginaroid
    S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative
    S7LeftScalar.circle_commutative S7LeftScalar.circle_distropp
    S7LeftScalar.circle_connected S7LeftScalar.circle_truncated.
  Local Notation C := (Sphere 1).
  Local Notation assoc := (simple_associativity (f:=sgop_s1)).
  Local Notation comm := (commutativity (f:=sgop_s1)).
  Context (D0 : CayleyDicksonDiamond (psphere 1) (-)) (s a b t c : C).
  Let Q := fun v : (C * C) * (C * C) =>
    zigzag@{Set Set Set} (fst (fst v)) (snd (fst v)) (fst (snd v))
      = zigzag (fst (fst v)) (snd (fst v)) (snd (snd v)).
  Let data (v : C * C) : sig Q :=
    (((a * fst v, (-snd v) * conj b), (conj a * snd v, fst v * b));
      @cd_op_diamond@{Set} (psphere 1) S7LeftScalar.circle_spheroid
        S7LeftScalar.circle_associative D0 a b (fst v) (snd v)).
  Let post : sig Q -> sig Q := functor_join_filler_data (.* c) (.* c).
  Let unit_labels := path_prod' (right_identity s)
    ((assoc (conj s) s t @ ap (.* t) (cds_conjug_left_inv s))
      @ left_identity t).
  Let reference := S7MiddleScalar.diamond_path@{u} D0 s a b North (s * t)
    @ ap data unit_labels.

  Example original_aligned_cap_middle_labels
    : S7MiddleScalar.diagonal_path D0 (a * s) (s * b) North (s * t) c
        @ ap post reference
      = (S7MiddleScalar.diamond_path@{u} D0 s a b c ((s * t) * c)
          @ ap data (path_prod' (idpath (s * c))
            (S7MiddleScalar.inner_diamond_boundary s t c @ comm c t)))
        @ S7MiddleScalar.diagonal_path D0 a b s t c
    := S7MiddleScalar.diamond_translate_square_aligned@{u} D0 s a b t c.
End AlignedBalancedChecks.
