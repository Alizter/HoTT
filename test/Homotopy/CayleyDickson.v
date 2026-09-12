From HoTT Require Import Basics.
From HoTT Require Import Classes.interfaces.abstract_algebra.
From HoTT Require Import Modalities.ReflectiveSubuniverse Truncations.Core.
From HoTT Require Import Pointed.Core Pointed.pSusp.
From HoTT Require Import Homotopy.HSpace.Core Homotopy.Suspension.
From HoTT Require Import Homotopy.Join.Core Homotopy.CayleyDickson.

Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.

(** The next diamond needs no algebra or diamond on the input. *)
Example double_diamond_without_algebra {X : pType} `{Negate X}
  : CayleyDicksonDiamond (pjoin X X) cd_negate := _.

(** The scalar boundary paths need neither a chosen diamond nor commutativity. *)
Section ScalarBoundaryPaths.
  Universe u.
  Context {X : pType@{u}} `{CayleyDicksonSpheroid X}
    `{!Associative hspace_op}.

  Example boundary_neg_unit (a c : X)
    : a * (c * -(- mon_unit)) = a * c
    := cd_diamond_map_l_neg_unit a c.

  Example boundary_neg_product (a b c d : X)
    : a * (c * -(conj c * conj a * d * conj b)) = (-d) * conj b
    := cd_diamond_map_l_parameter a b c d.

  Example boundary_unit (b c : X)
    : c * (mon_unit * b) = c * b := cd_diamond_map_r_unit b c.

  Example boundary_product (a b c d : X)
    : c * ((conj c * conj a * d * conj b) * b) = conj a * d
    := cd_diamond_map_r_parameter a b c d.
  (** Normalizing the parameter still needs no diamond. *)
  Context `{!Commutative (@hspace_op X _)}.

  Example parameter_diagonal_translation (a b c d r : X)
    : cd_diamond_parameter a b (c * r) (d * r)
      = cd_diamond_parameter a b c d
    := cd_diamond_parameter_translate@{u} a b c d r.
End ScalarBoundaryPaths.

(** The construction works for an arbitrary spheroid and an arbitrary chosen diamond, without commutativity or any further coherence hypotheses. *)
Section Spheroid.
  Universe u.
  Context {X : pType@{u}} `{CayleyDicksonSpheroid X}
    `{!Associative hspace_op} `{!CayleyDicksonDiamond X (-)}.

  Example doubled_hspace : IsHSpace@{u} (pjoin X X) := _.

  Example cd_op_ll (a b : X)
    : cd_op (joinl a) (joinl b) = joinl (a * b) := idpath.

  Example cd_op_lr (a b : X)
    : cd_op (joinl a) (joinr b) = joinr (conj a * b) := idpath.

  Example cd_op_rl (a b : X)
    : cd_op (joinr a) (joinl b) = joinr (b * a) := idpath.

  Example cd_op_rr (a b : X)
    : cd_op (joinr a) (joinr b) = joinl ((-b) * conj a) := idpath.

  (** The one-glue rules, used in the cancellation proof, do not depend on any computation rule for the diamond. *)
  Example cd_op_lg (a b c : X)
    : ap (cd_op (joinl a)) (jglue b c)
      = jglue (a * b) (conj a * c).
  Proof.
    exact (Join_rec_beta_jglue _ _ _ b c).
  Defined.

  Example cd_op_rg (a b c : X)
    : ap (cd_op (joinr a)) (jglue b c)
      = (jglue ((-c) * conj a) (b * a))^.
  Proof.
    exact (Join_rec_beta_jglue _ _ _ b c).
  Defined.

  Example cd_op_gl (a b c : X)
    : ap (fun z => cd_op z (joinl c)) (jglue a b)
      = jglue (a * c) (c * b).
  Proof.
    exact (Join_rec_beta_jglue _ _ _ a b).
  Defined.

  Example cd_op_gr (a b c : X)
    : ap (fun z => cd_op z (joinr c)) (jglue a b)
      = (jglue ((-c) * conj b) (conj a * c))^.
  Proof.
    exact (Join_rec_beta_jglue _ _ _ a b).
  Defined.

  Example doubled_left_identity : LeftIdentity cd_op pt := _.
  Example doubled_right_identity : RightIdentity cd_op pt := _.
  Example doubled_left_inverse : LeftInverse cd_op cd_conjugate pt := _.
  Example doubled_right_inverse : RightInverse cd_op cd_conjugate pt := _.
  Example doubled_factorneg_l : FactorNegLeft cd_negate cd_op := _.
  Example doubled_factorneg_r : FactorNegRight cd_negate cd_op := _.

  Example double_spheroid_from_associativity (a : Associative cd_op)
    : CayleyDicksonSpheroid (pjoin X X)
    := @cd_spheroid_of_associative X _ _ _ a.

  (** The conditional associator uses exactly the unit-based partial associators on both join factors. *)
  Example assoc_from_rectangle_joinl
    (h : forall a b u v, cd_associativity_rectangle a b u v)
    (a : X) (u v : pjoin X X)
    : cd_assoc_from_rectangle@{u} h (joinl a) u v
      = (cd_assoc_l a u v)^ := idpath.

  Example assoc_from_rectangle_joinr
    (h : forall a b u v, cd_associativity_rectangle a b u v)
    (b : X) (u v : pjoin X X)
    : cd_assoc_from_rectangle@{u} h (joinr b) u v
      = (cd_assoc_r b u v)^ := idpath.

  (** Simplifying the glue proof preserves the chosen inverse witnesses on points. *)
  Example doubled_left_inverse_joinl (a : X)
    : cd_op_conjugate_left_inverse (joinl a)
      = ap joinl (left_inverse a) := idpath.

  Example doubled_left_inverse_joinr (b : X)
    : cd_op_conjugate_left_inverse (joinr b)
      = ap joinl (right_inverse (-b)) := idpath.

  Example doubled_negate_involutive
    : Involutive (@cd_negate X _) := _.
  Example doubled_conjugate_involutive
    : Involutive (@cd_conjugate X _ _) := _.
  Example doubled_swapop
    : SwapOp (@cd_negate X _) (@cd_conjugate X _ _) := _.
  Example doubled_conjugate_unit
    : @IsUnitPreserving (pjoin X X) (pjoin X X) pt pt cd_conjugate := _.

  Example doubled_conjugate_glue (a b : X)
    : ap cd_conjugate (jglue a b) = jglue (conj a) (-b).
  Proof.
    apply functor_join_beta_jglue.
  Defined.

  Example doubled_negate_glue (a b : X)
    : ap cd_negate (jglue a b) = jglue (-a) (-b).
  Proof.
    apply functor_join_beta_jglue.
  Defined.

  (** A different explicitly supplied diamond is also supported; the laws must not silently select the ambient choice. *)
  Context (D : CayleyDicksonDiamond X (-)).

  Example chosen_diamond_path (t : X)
    : zigzag (-pt) t pt = zigzag (-pt) t t
    := @cd_diamond X (-) D t.

  Example chosen_diamond_hspace
    : @hspace_op (pjoin X X) (@hspace_cd@{u} X _ _ D)
      = @cd_op@{u} X _ _ D := idpath.

  Example chosen_diamond_left_inverse
    : LeftInverse (@cd_op X _ _ D) cd_conjugate pt
    := @cd_op_conjugate_left_inverse X _ _ D.

  Example chosen_diamond_right_inverse
    : RightInverse (@cd_op X _ _ D) cd_conjugate pt
    := @cd_op_conjugate_right_inverse X _ _ D.

  (** The two-glue computation exposes this supplied diamond, with all four one-glue beta paths retained. *)
  Example chosen_diamond_mixed_computation (a b c d : X)
    : let gl := Join_rec_beta_jglue
        (fun a => joinl (a * c)) (fun b => joinr (c * b))
        (fun a b => jglue (a * c) (c * b)) a b in
      let gr := Join_rec_beta_jglue
        (fun a => joinr (conj a * d)) (fun b => joinl ((-d) * conj b))
        (fun a b => (jglue ((-d) * conj b) (conj a * d))^) a b in
      let lg := Join_rec_beta_jglue
        (fun c => joinl (a * c)) (fun d => joinr (conj a * d))
        (fun c d => jglue (a * c) (conj a * d)) c d in
      let rg := Join_rec_beta_jglue
        (fun c => joinr (c * b)) (fun d => joinl ((-d) * conj b))
        (fun c d => (jglue ((-d) * conj b) (c * b))^) c d in
      concat_Ap (fun y => ap (fun x => @cd_op X _ _ D x y) (jglue a b))
        (jglue c d) @ (gl @@ 1)
      = (1 @@ gr) @ (lg @@ 1)
          @ (@cd_op_diamond X _ _ D a b c d @ (1 @@ rg)^).
  Proof.
    rhs napply concat_pp_p.
    exact (Join_rec2_beta_jglue_jglue _ _ _ _ _ _ _ _ _
      (@cd_op_diamond X _ _ D) a b c d).
  Defined.

  Context `{!Commutative (@hspace_op X _)} (a b c d : X).

  (** The complete postcomposition comparison needs no function extensionality, stays in one universe, and uses [D], not the ambient diamond. *)
  Check (@cd_op_diamond_normalize@{u} X _ _ D _ a b c d).

  Example right_translate_joinl_left (r x : X)
    : @cd_op_right_translate_joinl@{u} X _ _ D _ r (joinl x)
      = idpath := idpath.

  Example right_translate_joinl_right (r x : X)
    : @cd_op_right_translate_joinl@{u} X _ _ D _ r (joinr x)
      = ap joinr (commutativity r x) := idpath.

  Example right_translate_joinl_glue (r x y : X)
    : concat_Ap (@cd_op_right_translate_joinl X _ _ D _ r) (jglue x y)
      = (Join_rec_beta_jglue _ _
          (fun a b => jglue (a * r) (r * b)) x y @@ 1)
        @ ((join_natsq 1 (commutativity r y))^
          @ (1 @@ functor_join_beta_jglue (.* r) (.* r) x y)^).
  Proof.
    exact (Join_ind_FlFr_beta_jglue (fun z => @cd_op X _ _ D z (joinl r))
      (functor_join (.* r) (.* r)) _ _ _ x y).
  Defined.
  (** Translation uses the explicitly supplied diamond, without requiring truncation or connectedness. *)
  Check (fun r : X => @cd_op_diamond_translate@{u} X _ _ D _ a b c d r).

  (** The equivariance point homotopies compute to the exact four vertex paths chosen for the mixed comparison. *)
  Example diagonal_equivariance_ll (r : X)
    : @cd_op_diagonal_equivariance_joinl@{u} X _ _ D _ r a (joinl c)
      = ap joinl (cd_diamond_translate_l_neg_unit a c r) := idpath.

  Example diagonal_equivariance_lr (r : X)
    : @cd_op_diagonal_equivariance_joinl@{u} X _ _ D _ r a (joinr d)
      = ap joinr (cd_diamond_translate_r_parameter a mon_unit mon_unit d r)
    := idpath.

  Example diagonal_equivariance_rl (r : X)
    : @cd_op_diagonal_equivariance_joinr@{u} X _ _ D _ r b (joinl c)
      = ap joinr (cd_diamond_translate_r_unit b c r) := idpath.

  Example diagonal_equivariance_rr (r : X)
    : @cd_op_diagonal_equivariance_joinr@{u} X _ _ D _ r b (joinr d)
      = ap joinl (cd_diamond_translate_l_parameter mon_unit b mon_unit d r)
    := idpath.
  (** Removing irrelevant scalar labels still needs no extensionality. *)
  Context `{!IsConnected (0%trunc) X, !IsTrunc 1 X}.
  Check (fun r : X => @cd_op_diamond_diagonal@{u} X _ _ D _ _ _ a b c d r).

  (** The nullhomotopies are normalized by their actual unit values. Check that these comparisons at the unit cancel, rather than assuming equality with an arbitrary center. *)
  Example diagonal_l_parameter_at_unit (r : X)
    : cd_diamond_translate_l_parameter_independent mon_unit b mon_unit d r
      = 1.
  Proof.
    unfold cd_diamond_translate_l_parameter_independent; cbn.
    lhs napply concat_p_Vp.
    apply concat_pV.
  Defined.

  Example diagonal_r_parameter_at_unit (r : X)
    : cd_diamond_translate_r_parameter_independent a mon_unit mon_unit d r
      = 1.
  Proof.
    unfold cd_diamond_translate_r_parameter_independent; cbn.
    lhs napply concat_p_Vp.
    apply concat_pV.
  Defined.
End Spheroid.

(** The canonical diamond does not depend on an imaginaroid structure, or even on involutivity of negation. *)
Section SuspensionDiamond.
  Context {A : Type} `{Negate A}.

  Example suspension_diamond : CayleyDicksonDiamond (psusp A) (-) := _.

  Example suspension_diamond_north
    : cd_diamond (X := psusp A) North = diamond_v South North 1
    := idpath.

  Example suspension_diamond_south
    : cd_diamond (X := psusp A) South = diamond_h North South 1
    := idpath.

  Example suspension_diamond_merid (a : A)
    : apD (cd_diamond (X := psusp A)) (merid a)
      = diamond_twist (merid a).
  Proof.
    napply Susp_ind_beta_merid.
  Defined.
End SuspensionDiamond.

(** Imaginaroids still acquire the H-space structure by instance search. *)
Section Imaginaroid.
  Context {A : Type} `{CayleyDicksonImaginaroid A}
    `{!Associative hspace_op}.

  Example imaginaroid_double_hspace
    : IsHSpace (pjoin (psusp A) (psusp A)) := _.

  Example imaginaroid_double_hspace_name
    : IsHSpace (pjoin (psusp A) (psusp A)) := hspace_cdi_susp_assoc.

  (** The formerly judgmental double negation at the unit still reduces in the suspension instance. *)
  Example suspension_unit_normalization (a c : Susp A)
    : cd_diamond_map_l_neg_unit a c
      = ap (a *.) (hspace_right_identity c).
  Proof.
    unfold cd_diamond_map_l_neg_unit.
    apply concat_1p.
  Defined.

  Example imaginaroid_double_inverse (z : Join (Susp A) (Susp A))
    : cd_op (cd_conjugate z) z = joinl North.
  Proof.
    apply left_inverse.
  Defined.
End Imaginaroid.
