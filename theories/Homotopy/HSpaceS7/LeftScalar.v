From HoTT Require Import Basics.
Require Import Types.Paths Types.Prod Types.Universe.
Require Import Classes.interfaces.abstract_algebra.
Require Import Pointed.Core Spaces.Spheres Truncations.Connectedness.
Require Import Homotopy.HSpace.Core Homotopy.HSpaceS1 Homotopy.HSpaceS3.
Require Import Homotopy.CayleyDickson Homotopy.Suspension Homotopy.Join.Core.
Require Import Homotopy.Join.MapCoherence Homotopy.NullHomotopy.

Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.

(** * A first-left-scalar associator for the circle double *)

(** The multiplication and diamond are not changed. Left multiplication by [joinl s] is the join map with scalar maps [s *.] and [conj s *.]. We compare the actual mixed fillers under this map, then assemble the existing first-two-constructor associators. The final section proves the overlap with the fixed last-left associator and derives [loop_y_joinl] for the original corner loop witnesses. *)
Module S7LeftScalar.
Local Notation gassoc := (simple_associativity (f:=hspace_op)).
Local Notation gcomm := (commutativity (f:=hspace_op)).

(** Left scalar multiplication changes the two first-glue labels with opposite conjugation weights, leaving the diamond parameter unchanged. *)
Definition left_parameter
  {X : pType} `{CayleyDicksonSpheroid X}
  `{!Associative (@hspace_op X _)}
  `{!Commutative (@hspace_op X _)}
  (r a b c d : X)
  : cd_diamond_parameter (r * a) (conj r * b) c d
    = cd_diamond_parameter a b c d.
Proof.
  unfold cd_diamond_parameter.
  lhs rapply (ap011 (fun u v => conj c * u * d * v)
    (distropp r a) (distropp (conj r) b)).
  lhs rapply (ap (fun x => conj c * (conj a * conj r) * d * (conj b * x))
    (cds_conjug_inv r)).
  lhs rapply (ap (fun x => x * d * (conj b * r))
    (gassoc (conj c) (conj a) (conj r))).
  lhs rapply (ap (.* (conj b * r)) (gassoc (conj c * conj a) (conj r) d)^).
  lhs rapply (ap (fun x => (conj c * conj a) * x * (conj b * r))
    (gcomm (conj r) d)).
  lhs rapply (ap (.* (conj b * r)) (gassoc (conj c * conj a) d (conj r))).
  lhs rapply (gassoc (conj c * conj a * d) (conj r) (conj b * r))^.
  rapply (ap ((conj c * conj a * d) *.)).
  lhs rapply (gassoc (conj r) (conj b) r).
  lhs rapply (ap (.* r) (gcomm (conj r) (conj b))).
  lhs rapply (gassoc (conj b) (conj r) r)^.
  lhs rapply (ap (conj b *.) (left_inverse r)).
  apply right_identity.
Defined.

Local Definition left_map_l
  {X : pType} `{CayleyDicksonSpheroid X}
  `{!Associative (@hspace_op X _)}
  (r a c : X)
  : cd_diamond_map_l (r * a) c == fun x => r * cd_diamond_map_l a c x.
Proof.
  intro x; exact (gassoc r a (c * -x))^.
Defined.

Definition left_map_r
  {X : pType} `{CayleyDicksonSpheroid X}
  `{!Associative (@hspace_op X _)}
  `{!Commutative (@hspace_op X _)}
  (r b c : X)
  : cd_diamond_map_r (conj r * b) c
    == fun y => conj r * cd_diamond_map_r b c y.
Proof.
  intro y; unfold cd_diamond_map_r.
  lhs rapply (ap (c *.) (gassoc y (conj r) b)).
  lhs rapply (ap (fun x => c * (x * b)) (gcomm y (conj r))).
  lhs rapply (ap (c *.) (gassoc (conj r) y b)^).
  lhs rapply (gassoc c (conj r) (y * b)).
  lhs rapply (ap (.* (y * b)) (gcomm c (conj r))).
  exact (gassoc (conj r) c (y * b))^.
Defined.

(** The four boundary paths induced by this parameter comparison and these particular map homotopies. *)
Definition left_00
  {X : pType} `{CayleyDicksonSpheroid X}
  `{!Associative (@hspace_op X _)}
  (r a c : X) : (r * a) * c = r * (a * c)
  := (cd_diamond_map_l_neg_unit (r * a) c)^
    @ left_map_l r a c (-mon_unit)
    @ ap (r *.) (cd_diamond_map_l_neg_unit a c).
Definition left_01
  {X : pType} `{CayleyDicksonSpheroid X}
  `{!Associative (@hspace_op X _)}
  `{!Commutative (@hspace_op X _)}
  (r a b c d : X)
  : conj (r * a) * d = conj r * (conj a * d)
  := (cd_diamond_map_r_parameter (r * a) (conj r * b) c d)^
    @ (left_map_r r b c (cd_diamond_parameter (r * a) (conj r * b) c d)
      @ ap (fun t => conj r * cd_diamond_map_r b c t) (left_parameter r a b c d))
    @ ap (conj r *.) (cd_diamond_map_r_parameter a b c d).
Definition left_10
  {X : pType} `{CayleyDicksonSpheroid X}
  `{!Associative (@hspace_op X _)}
  `{!Commutative (@hspace_op X _)}
  (r b c : X) : c * (conj r * b) = conj r * (c * b)
  := (cd_diamond_map_r_unit (conj r * b) c)^
    @ left_map_r r b c mon_unit
    @ ap (conj r *.) (cd_diamond_map_r_unit b c).
Definition left_11
  {X : pType} `{CayleyDicksonSpheroid X}
  `{!Associative (@hspace_op X _)}
  `{!Commutative (@hspace_op X _)}
  (r a b c d : X)
  : (-d) * conj (conj r * b) = r * ((-d) * conj b)
  := (cd_diamond_map_l_parameter (r * a) (conj r * b) c d)^
    @ (left_map_l r a c (cd_diamond_parameter (r * a) (conj r * b) c d)
      @ ap (fun t => r * cd_diamond_map_l a c t) (left_parameter r a b c d))
    @ ap (r *.) (cd_diamond_map_l_parameter a b c d).

(** Naturality and composition of the supplied filler give its actual left-translation comparison. Neither connectedness nor truncation is used here. *)
Definition left_diamond
  {X : pType} `{CayleyDicksonSpheroid X}
  `{!Associative (@hspace_op X _)}
  `{!CayleyDicksonDiamond X (-)}
  `{!Commutative (@hspace_op X _)}
  (r a b c d : X)
  : transport011
      (fun x : X * X => fun y : X * X =>
        zigzag (fst x) (snd x) (fst y) = zigzag (fst x) (snd x) (snd y))
      (path_prod' (left_00 r a c) (left_11 r a b c d))
      (path_prod' (left_01 r a b c d) (left_10 r b c))
      (cd_op_diamond (r * a) (conj r * b) c d)
    = join_zigzag_filler (r *.) (conj r *.) 1 1 1 1 (cd_op_diamond a b c d).
Proof.
  rhs napply (join_zigzag_filler_compose
    (cd_diamond_map_l a c) (cd_diamond_map_r b c) (r *.) (conj r *.)).
  exact (join_zigzag_filler_change (fun t => (cd_diamond t)^)
    (left_map_l r a c) (left_map_r r b c) (left_parameter r a b c d)
    _ _ _ _ _ _ _ _).
Defined.

Local Set Universe Minimization ToSet.

(** The circle data are shared monomorphic instances: the carriers are small, and no auxiliary universe choices need to be repeated for each occurrence. Every result below states its [Univalence] and chosen-diamond inputs explicitly. *)
#[local] Monomorphic Instance circle_imaginaroid `{Univalence}
  : CayleyDicksonImaginaroid (Sphere 0) := cdi_s0.
#[local] Monomorphic Instance circle_spheroid `{Univalence}
  : CayleyDicksonSpheroid (psphere 1)
  := @cds_susp_cdi (Sphere 0) circle_imaginaroid.
#[local] Monomorphic Instance circle_associative `{Univalence}
  : Associative sgop_s1 := associative_sgop_s1.
#[local] Monomorphic Instance circle_commutative `{Univalence}
  : Commutative sgop_s1 := commutative_sgop_s1.
#[local] Monomorphic Instance circle_distropp `{Univalence}
  : DistrOpp sgop_s1 conj := cds_conjug_distr.
#[local] Monomorphic Instance circle_connected `{Univalence}
  : IsConnected (0%trunc) (psphere 1) := _.
#[local] Monomorphic Instance circle_truncated `{Univalence}
  : IsTrunc 1 (psphere 1) := _.

Local Notation C := (Sphere 1).
Local Notation J := (Join@{Set Set Set} C C).
Local Notation assoc := (simple_associativity (f:=sgop_s1)).
Local Notation comm := (commutativity (f:=sgop_s1)).

(** These are equalities of scalar paths, hence proposition-valued. Connectedness reduces them to their unit values. This is not a truncation argument about join-valued fillers. *)
Definition left_00_standard `{Univalence} (r a c : C)
  : left_00 (X:=psphere 1) r a c = (assoc r a c)^.
Proof.
  revert r a c.
  do 3 srapply (conn_point_elim (-1) (A:=psphere 1)).
  reflexivity.
Defined.

Definition left_01_standard `{Univalence} (r a b c d : C)
  : left_01 (X:=psphere 1) r a b c d
    = ap (.* d) (distropp r a)
      @ (ap (.* d) (comm (conj a) (conj r)) @ (assoc (conj r) (conj a) d)^).
Proof.
  revert r a b c d.
  do 5 srapply (conn_point_elim (-1) (A:=psphere 1)).
  reflexivity.
Defined.

Definition left_10_standard `{Univalence} (r b c : C)
  : left_10 (X:=psphere 1) r b c
    = assoc c (conj r) b
      @ (ap (.* b) (comm c (conj r)) @ (assoc (conj r) c b)^).
Proof.
  revert r b c.
  do 3 srapply (conn_point_elim (-1) (A:=psphere 1)).
  reflexivity.
Defined.

Definition left_11_standard `{Univalence} (r a b c d : C)
  : left_11 (X:=psphere 1) r a b c d
    = ap ((-d) *.) (distropp (conj r) b)
      @ (ap (fun x => (-d) * (conj b * x)) (cds_conjug_inv r)
        @ (assoc (-d) (conj b) r @ comm ((-d) * conj b) r)).
Proof.
  revert r a b c d.
  do 5 srapply (conn_point_elim (-1) (A:=psphere 1)).
  pose (s := cd_diamond_map_l_parameter (X:=psphere 1) North North North North).
  change ((s^ @ (1 @ 1)) @ ap idmap s
    = 1 @ (1 @ (assoc (-North) North North @ comm ((-North) * North) North))).
  lhs napply (concat_p1 s^ @@ 1).
  lhs napply (1 @@ ap_idmap s).
  lhs napply concat_Vp.
  rhs napply concat_1p.
  rhs napply concat_1p.
  assert (q : forall x : C, assoc x North North @ comm (x * North) North = 1).
  { srapply (conn_point_elim (-1) (A:=psphere 1)).
    reflexivity. }
  exact (q South)^.
Defined.

Local Opaque cd_diamond cd_op_diamond.
Local Notation mu :=
  (fun D0 => @cd_op@{Set} (psphere 1)
    circle_spheroid circle_associative D0).
Local Notation D :=
  (fun D0 => @cd_op_diamond@{Set} (psphere 1)
    circle_spheroid circle_associative D0).
Local Notation cd_assoc_first_ll :=
  (fun D0 => @cd_assoc_first_ll@{Set} (psphere 1)
    circle_spheroid circle_associative D0 circle_commutative).
Local Notation cd_assoc_first_lr :=
  (fun D0 => @cd_assoc_first_lr@{Set} (psphere 1)
    circle_spheroid circle_associative D0 circle_commutative).
Local Definition p00 `{Univalence} (s a c : C) := (assoc s a c)^.
Local Definition p01 `{Univalence} (s a d : C) := ap (.* d) (distropp s a)
  @ (ap (.* d) (comm (conj a) (conj s)) @ (assoc (conj s) (conj a) d)^).
Local Definition p10 `{Univalence} (s b c : C) := assoc c (conj s) b
  @ (ap (.* b) (comm c (conj s)) @ (assoc (conj s) c b)^).
Local Definition p11 `{Univalence} (s b d : C) := ap ((-d) *.) (distropp (conj s) b)
  @ (ap (fun x => (-d) * (conj b * x)) (cds_conjug_inv s)
    @ (assoc (-d) (conj b) s @ comm ((-d) * conj b) s)).

(** The same mixed comparison, now with exactly the scalar boundary witnesses of [cd_assoc_first_ll] and [cd_assoc_first_lr]. *)
Definition left_diamond_standard `{Univalence}
  `(D0 : CayleyDicksonDiamond (psphere 1) (-))
  (s a b c d : C)
  : transport011
      (fun x : C * C => fun y : C * C =>
        zigzag (fst x) (snd x) (fst y) = zigzag (fst x) (snd x) (snd y))
      (path_prod' (p00 s a c) (p11 s b d))
      (path_prod' (p01 s a d) (p10 s b c))
      (D D0 (s * a) (conj s * b) c d)
    = join_zigzag_filler (s *.) (conj s *.) 1 1 1 1 (D D0 a b c d).
Proof.
  lhs_V napply (ap011 (fun p q => transport011 _ p q (D D0 (s * a) (conj s * b) c d))
    (ap011 path_prod' (left_00_standard s a c) (left_11_standard s a b c d))
    (ap011 path_prod' (left_01_standard s a b c d) (left_10_standard s b c))).
  exact (left_diamond s a b c d).
Defined.

(** The two point clauses for the middle join glue. *)
Definition first_l_glue_l `{Univalence}
  `(D0 : CayleyDicksonDiamond (psphere 1) (-))
  (s a b c : C)
  : ap (fun y => mu D0 (mu D0 (joinl s) y) (joinl c)) (jglue a b)
      @ cd_assoc_first_lr D0 s b (joinl c)
    = cd_assoc_first_ll D0 s a (joinl c)
      @ ap (fun y => mu D0 (joinl s) (mu D0 y (joinl c))) (jglue a b).
Proof.
  lhs napply (ap_compose (mu D0 (joinl s)) (fun y => mu D0 y (joinl c)) (jglue a b) @@ 1).
  lhs napply (ap (ap (fun y => mu D0 y (joinl c)))
    (Join_rec_beta_jglue _ _ (fun a b => jglue (s * a) (conj s * b)) a b) @@ 1).
  lhs napply (Join_rec_beta_jglue _ _ (fun a b => jglue (a * c) (c * b))
    (s * a) (conj s * b) @@ 1).
  rhs napply (1 @@ ap_compose (fun y => mu D0 y (joinl c)) (mu D0 (joinl s)) (jglue a b)).
  rhs napply (1 @@ ap (ap (mu D0 (joinl s)))
    (Join_rec_beta_jglue _ _ (fun a b => jglue (a * c) (c * b)) a b)).
  rhs napply (1 @@ Join_rec_beta_jglue _ _
    (fun a b => jglue (s * a) (conj s * b)) (a * c) (c * b)).
  exact (join_natsq (p00 s a c) (p10 s b c))^.
Defined.

Definition first_l_glue_r `{Univalence}
  `(D0 : CayleyDicksonDiamond (psphere 1) (-))
  (s a b d : C)
  : ap (fun y => mu D0 (mu D0 (joinl s) y) (joinr d)) (jglue a b)
      @ cd_assoc_first_lr D0 s b (joinr d)
    = cd_assoc_first_ll D0 s a (joinr d)
      @ ap (fun y => mu D0 (joinl s) (mu D0 y (joinr d))) (jglue a b).
Proof.
  lhs napply (ap_compose (mu D0 (joinl s)) (fun y => mu D0 y (joinr d)) (jglue a b) @@ 1).
  lhs napply (ap (ap (fun y => mu D0 y (joinr d)))
    (Join_rec_beta_jglue _ _ (fun a b => jglue (s * a) (conj s * b)) a b) @@ 1).
  lhs napply (Join_rec_beta_jglue _ _
    (fun a b => (jglue ((-d) * conj b) (conj a * d))^)
    (s * a) (conj s * b) @@ 1).
  rhs napply (1 @@ ap_compose (fun y => mu D0 y (joinr d)) (mu D0 (joinl s)) (jglue a b)).
  rhs napply (1 @@ ap (ap (mu D0 (joinl s)))
    (Join_rec_beta_jglue _ _ (fun a b => (jglue ((-d) * conj b) (conj a * d))^) a b)).
  rhs napply (1 @@ ap_V (mu D0 (joinl s)) (jglue ((-d) * conj b) (conj a * d))).
  change (mu D0 (joinl s)) with
    (Join_rec (fun a => joinl (s * a)) (fun b => joinr (conj s * b))
      (fun a b => jglue (s * a) (conj s * b))).
  rhs tapply (1 @@ inverse2 (Join_rec_beta_jglue (P:=J) _ _
    (fun a b => jglue (s * a) (conj s * b)) ((-d) * conj b) (conj a * d))).
  exact (inverse_natural _ _ (join_natsq (p11 s b d) (p01 s a d))).
Defined.

(** Convert the chosen filler comparison using both mixed beta equations and the four actual side faces. The diamond constants stay opaque throughout this conversion. *)
Definition first_l_glue_glue `{Univalence}
  `(D0 : CayleyDicksonDiamond (psphere 1) (-))
  (s a b c d : C)
  : transport
      (fun z => ap (fun y => mu D0 (mu D0 (joinl s) y) z) (jglue a b)
          @ cd_assoc_first_lr D0 s b z
        = cd_assoc_first_ll D0 s a z
          @ ap (fun y => mu D0 (joinl s) (mu D0 y z)) (jglue a b))
      (jglue c d) (first_l_glue_l D0 s a b c) = first_l_glue_r D0 s a b d.
Proof.
  pose (rho := mu D0 (joinl s)).
  pose (f0 := mu D0 (joinl (s * a))).
  pose (f1 := mu D0 (joinr (conj s * b))).
  pose (g0 := mu D0 (joinl a)).
  pose (g1 := mu D0 (joinr b)).
  pose (W := fun a b z => ap (fun y => mu D0 y z) (jglue a b)).
  pose (U := fun z => ap (fun y => mu D0 (rho y) z) (jglue a b)).
  pose (V := fun z => ap (fun y => rho (mu D0 y z)) (jglue a b)).
  pose (brho := fun a b => Join_rec_beta_jglue _ _
    (fun a b => jglue (s * a) (conj s * b)) a b).
  pose (bh0 := fun a c d => Join_rec_beta_jglue _ _
    (fun c d => jglue (a * c) (conj a * d)) c d).
  pose (bh1 := fun b c d => Join_rec_beta_jglue _ _
    (fun c d => (jglue ((-d) * conj b) (c * b))^) c d).
  pose (bv0 := fun a b c => Join_rec_beta_jglue _ _
    (fun a b => jglue (a * c) (c * b)) a b).
  pose (bv1 := fun a b d => Join_rec_beta_jglue _ _
    (fun a b => (jglue ((-d) * conj b) (conj a * d))^) a b).
  pose (tF := fun z => ap_compose rho (fun y => mu D0 y z) (jglue a b)
    @ ap (ap (fun y => mu D0 y z)) (brho a b)).
  pose (tG := fun z => ap_compose (fun y => mu D0 y z) rho (jglue a b)).
  pose (bfh0 := bh0 (s * a) c d).
  pose (bfh1 := bh1 (conj s * b) c d).
  pose (bfv0 := tF (joinl c) @ bv0 (s * a) (conj s * b) c).
  pose (bfv1 := tF (joinr d) @ bv1 (s * a) (conj s * b) d).
  pose (bgh0 := (ap_compose g0 rho (jglue c d) @ ap (ap rho) (bh0 a c d))
    @ brho (a * c) (conj a * d)).
  pose (bgh1 := (ap_compose g1 rho (jglue c d) @ ap (ap rho) (bh1 b c d))
    @ (ap_V rho (jglue ((-d) * conj b) (c * b))
      @ inverse2 (brho ((-d) * conj b) (c * b)))).
  pose (bgv0 := (tG (joinl c) @ ap (ap rho) (bv0 a b c))
    @ brho (a * c) (c * b)).
  pose (bgv1 := (tG (joinr d) @ ap (ap rho) (bv1 a b d))
    @ (ap_V rho (jglue ((-d) * conj b) (conj a * d))
      @ inverse2 (brho ((-d) * conj b) (conj a * d)))).
  assert (BM : forall a b c d, concat_Ap (W a b) (jglue c d) @ (bv0 a b c @@ 1)
    = (1 @@ bv1 a b d) @ naturality_change (bh0 a c d) (bh1 b c d) (D D0 a b c d)).
  { intros a0 b0 c0 d0.
    nrefine (Join_rec2_beta_jglue_jglue J
      _ _ _ _ _ _ _ _ (D D0) a0 b0 c0 d0 @ _).
    exact (1 @@ concat_p_pp _ _ _). }
  assert (BF : concat_Ap U (jglue c d) @ (bfv0 @@ 1)
    = (1 @@ bfv1) @ naturality_change bfh0 bfh1 (D D0 (s * a) (conj s * b) c d)).
  { napply (mixed_beta_vertical (tF (joinl c)) (tF (joinr d))
      (bv0 (s * a) (conj s * b) c) (bv1 (s * a) (conj s * b) d) _ _
      _ (concat_Ap (W (s * a) (conj s * b)) (jglue c d)) _).
    - exact (concat_Ap_homotopic U (W (s * a) (conj s * b)) tF (jglue c d)).
    - exact (BM (s * a) (conj s * b) c d). }
  assert (BG : concat_Ap V (jglue c d) @ (bgv0 @@ 1)
    = (1 @@ bgv1) @ naturality_change bgh0 bgh1
      (join_zigzag_filler (s *.) (conj s *.) 1 1 1 1 (D D0 a b c d))).
  { napply (mixed_beta_compose
      (ap_compose g0 rho (jglue c d) @ ap (ap rho) (bh0 a c d))
      (tG (joinr d) @ ap (ap rho) (bv1 a b d))
      (tG (joinl c) @ ap (ap rho) (bv0 a b c))
      (ap_compose g1 rho (jglue c d) @ ap (ap rho) (bh1 b c d))
      _ _ _ _ _ (ap_naturality rho (D D0 a b c d)) _).
    - napply (mixed_beta_vertical (tG (joinl c)) (tG (joinr d))
        (ap (ap rho) (bv0 a b c)) (ap (ap rho) (bv1 a b d)) _ _
        _ (concat_Ap (fun z => ap rho (W a b z)) (jglue c d)) _).
      + exact (concat_Ap_homotopic V (fun z => ap rho (W a b z)) tG (jglue c d)).
      + exact (concat_Ap_postcompose_beta (W a b) rho (jglue c d)
          (bh0 a c d) (bv1 a b d) (bv0 a b c) (bh1 b c d) _ (BM a b c d)).
    - rhs napply (1 @@ ap (naturality_change _ _)
        (join_zigzag_filler_refl (s *.) (conj s *.) (D D0 a b c d))).
      exact (ap_pV_filler_beta rho
        (jglue (a * c) (conj a * d)) (jglue ((-d) * conj b) (conj a * d))
        (jglue (a * c) (c * b)) (jglue ((-d) * conj b) (c * b))
        (brho _ _) (brho _ _) (brho _ _) (brho _ _) (D D0 a b c d)). }
  pose (eh0 := (join_natsq (p00 s a c) (p01 s a d))^).
  pose (eh1 := inverse_natural _ _ (join_natsq (p11 s b d) (p10 s b c))).
  pose (ev0 := (join_natsq (p00 s a c) (p10 s b c))^).
  pose (ev1 := inverse_natural _ _ (join_natsq (p11 s b d) (p01 s a d))).
  assert (EH0 : concat_Ap (cd_assoc_first_ll D0 s a) (jglue c d)
    = naturality_change bfh0 bgh0 eh0).
  { lhs napply (Join_ind_FlFr_beta_jglue _ _ _ _ _ c d).
    rhs napply concat_pp_p.
    napply (ap (fun q => (bfh0 @@ 1) @ q)).
    lhs napply naturality_suffix.
    apply naturality_suffix. }
  assert (EH1 : concat_Ap (cd_assoc_first_lr D0 s b) (jglue c d)
    = naturality_change bfh1 bgh1 eh1).
  { lhs napply (Join_ind_FlFr_beta_jglue _ _ _ _ _ c d).
    rhs napply concat_pp_p.
    napply (ap (fun q => (bfh1 @@ 1) @ q)).
    lhs napply naturality_suffix.
    lhs napply naturality_suffix.
    lhs napply naturality_suffix.
    exact (ap (fun q => eh1 @ (1 @@ q)^) (concat_pp_p _ _ _)). }
  assert (EV0 : first_l_glue_l D0 s a b c = naturality_change bfv0 bgv0 ev0).
  { lhs napply naturality_prefix.
    lhs napply naturality_prefix.
    rhs napply concat_pp_p.
    napply (ap (fun q => (bfv0 @@ 1) @ q)).
    lhs napply naturality_suffix.
    apply naturality_suffix. }
  assert (EV1 : first_l_glue_r D0 s a b d = naturality_change bfv1 bgv1 ev1).
  { lhs napply naturality_prefix.
    lhs napply naturality_prefix.
    rhs napply concat_pp_p.
    napply (ap (fun q => (bfv1 @@ 1) @ q)).
    lhs napply naturality_suffix.
    lhs napply naturality_suffix.
    lhs napply naturality_suffix.
    exact (ap (fun q => ev1 @ (1 @@ q)^) (concat_pp_p _ _ _)). }
  refine (ap (transport _ (jglue c d)) EV0 @ _ @ EV1^).
  napply (transport_naturality_square_beta U V
    (cd_assoc_first_ll D0 s a) (cd_assoc_first_lr D0 s b)
    (jglue c d) bfh0 bfh1 bfv0 bfv1 bgh0 bgh1 bgv0 bgv1
    _ _ eh0 eh1 ev0 ev1 BF BG EH0 EH1).
  exact (join_zigzag_filler_cube (p00 s a c) (p11 s b d) (p01 s a d) (p10 s b c)
    _ _ (left_diamond_standard D0 s a b c d)).
Defined.

Definition first_l_glue `{Univalence}
  `(D0 : CayleyDicksonDiamond (psphere 1) (-))
  (s a b : C) : forall z : J,
  ap (fun y => mu D0 (mu D0 (joinl s) y) z) (jglue a b) @ cd_assoc_first_lr D0 s b z
    = cd_assoc_first_ll D0 s a z @ ap (fun y => mu D0 (joinl s) (mu D0 y z)) (jglue a b).
Proof.
  snapply Join_ind.
  - exact (first_l_glue_l D0 s a b).
  - exact (first_l_glue_r D0 s a b).
  - exact (first_l_glue_glue D0 s a b).
Defined.

(** Both later arguments are arbitrary. Unlike the unit-based [cd_assoc_l], this associator computes to the existing scalar-normalized [cd_assoc_first_ll] and [cd_assoc_first_lr] rows. *)
Definition first_l `{Univalence}
  `(D0 : CayleyDicksonDiamond (psphere 1) (-))
  (s : C) : forall y z : J,
  mu D0 (mu D0 (joinl s) y) z = mu D0 (joinl s) (mu D0 y z).
Proof.
  intros y z; revert y.
  snapply Join_ind_FlFr.
  - exact (fun a => cd_assoc_first_ll D0 s a z).
  - exact (fun b => cd_assoc_first_lr D0 s b z).
  - exact (fun a b => first_l_glue D0 s a b z).
Defined.

Local Opaque first_l_glue_glue.
Local Notation AL :=
  (fun D0 => @cd_assoc_last_joinl@{Set} (psphere 1)
    circle_spheroid circle_associative D0 circle_commutative circle_connected circle_truncated).
Local Notation T :=
  (fun D0 => @cd_assoc_last_transport@{Set} (psphere 1)
    circle_spheroid circle_associative D0 circle_commutative circle_connected circle_truncated).
Local Notation qll :=
  (fun D0 => @cd_assoc_last_joinl_first_ll@{Set} (psphere 1)
    circle_spheroid circle_associative D0 circle_commutative circle_connected circle_truncated).
Local Notation qlr :=
  (fun D0 => @cd_assoc_last_joinl_first_lr@{Set} (psphere 1)
    circle_spheroid circle_associative D0 circle_commutative circle_connected circle_truncated).
Local Notation mll :=
  (fun D0 => @cd_assoc_last_transport_loop_ll@{Set} (psphere 1)
    circle_spheroid circle_associative D0 circle_commutative circle_connected circle_truncated).
Local Notation mlr :=
  (fun D0 => @cd_assoc_last_transport_loop_lr@{Set} (psphere 1)
    circle_spheroid circle_associative D0 circle_commutative circle_connected circle_truncated).

(** ** Agreement with the fixed last-left associator *)

(** Normalize only the scalar coefficient paths. Their comparisons are proposition-valued and have reflexive unit computations. *)
Definition overlap_scalar_l `{Univalence} (s a c : C)
  : (cd_diamond_translate_l_neg_unit (X:=psphere 1) s a c)^
    = (assoc s a c)^.
Proof.
  revert s a c.
  do 3 srapply (conn_point_elim (-1) (A:=psphere 1)).
  reflexivity.
Defined.

Definition overlap_scalar_r `{Univalence} (s b c : C)
  : (comm c (conj s * b)
      @ (cd_diamond_translate_r_parameter (X:=psphere 1)
        s North North b c)^) @ ap (conj s *.) (comm c b)^
    = assoc c (conj s) b
      @ (ap (.* b) (comm c (conj s)) @ (assoc (conj s) c b)^).
Proof.
  revert s b c.
  do 3 srapply (conn_point_elim (-1) (A:=psphere 1)).
  reflexivity.
Defined.

(** The join-map comparison retains exactly [qll] and [qlr], including their triangle witnesses. All the recursor templates specialize definitionally to the existing translation, equivariance row, and first-left associator. No diamond computation or join-valued truncation is needed for this overlap. *)
Definition overlap_glue `{Univalence}
  `(D0 : CayleyDicksonDiamond (psphere 1) (-))
  (s a b c : C)
  : concat_Ap (fun y => AL D0 (joinl s) y c) (jglue a b)
      @ (qll D0 s a c @@ 1)
    = (1 @@ qlr D0 s b c) @ first_l_glue_l D0 s a b c.
Proof.
  lhs tapply (JoinMapCoherence.translation_comparison
    (North : C) (North : C)
    (sgop_s1 s) (fun x => sgop_s1 x c) (sgop_s1 (conj s))
    (sgop_s1 c) (fun x => sgop_s1 x c)
    (comm c)
    (fun a => cd_diamond_translate_l_neg_unit (X:=psphere 1) s a c)
    (fun b => cd_diamond_translate_r_parameter (X:=psphere 1)
      s North North b c)
    (fun a => (assoc s a c)^)
    (fun b => assoc c (conj s) b
      @ (ap (.* b) (comm c (conj s)) @ (assoc (conj s) c b)^))
    (fun a => overlap_scalar_l s a c)
    (fun b => overlap_scalar_r s b c) a b).
  napply whiskerL.
  exact (Join_ind_FlFr_beta_jglue _ _ _ _ _ a b).
Defined.


Definition overlap `{Univalence}
  `(D0 : CayleyDicksonDiamond (psphere 1) (-))
  (s : C) (y : J) (c : C)
  : AL D0 (joinl s) y c = first_l D0 s y (joinl c).
Proof.
  revert y; snapply Join_ind.
  - exact (fun a => qll D0 s a c).
  - exact (fun b => qlr D0 s b c).
  - intros a b.
    nrefine (equiv_naturality_transport2 _ _ (jglue a b) _ _ _).
    rhs napply (1 @@ Join_ind_FlFr_beta_jglue _ _ _ _ _ a b).
    exact (overlap_glue D0 s a b c).
Defined.

Definition row_loop `{Univalence}
  `(D0 : CayleyDicksonDiamond (psphere 1) (-))
  (s d : C) (y : J) {c : C} (p : c = c)
  : ap (T D0 (joinl s) y d) p = 1.
Proof.
  pose (K := fun c => ap (transport _ (jglue c d)) (overlap D0 s y c)
    @ apD (first_l D0 s y) (jglue c d)).
  exact (ap_loop_nullhomotopic K p).
Defined.

Local Opaque ap_loop_nullhomotopic.

Definition row_loop_l `{Univalence}
  `(D0 : CayleyDicksonDiamond (psphere 1) (-))
  (s a d : C) {c : C} (p : c = c)
  : row_loop D0 s d (joinl a) p
    = mll D0 s a d c p
  := idpath.

Definition row_loop_r `{Univalence}
  `(D0 : CayleyDicksonDiamond (psphere 1) (-))
  (s b d : C) {c : C} (p : c = c)
  : row_loop D0 s d (joinr b) p
    = mlr D0 s b d c p
  := idpath.

(** OPEN 1 of the S7 outline, now proved for any supplied circle diamond and every scalar loop. *)
Definition loop_y_joinl `{Univalence}
  `(D0 : CayleyDicksonDiamond (psphere 1) (-))
  (s a b d : C) {c : C} (p : c = c)
  : transport (fun y => ap (T D0 (joinl s) y d) p = 1) (jglue a b)
      (mll D0 s a d c p) = mlr D0 s b d c p.
Proof.
  lhs_V napply (ap (transport (fun y => ap (T D0 (joinl s) y d) p = 1)
    (jglue a b)) (row_loop_l D0 s a d p)).
  rhs_V napply (row_loop_r D0 s b d p).
  exact (apD (fun y => row_loop D0 s d y p) (jglue a b)).
Defined.
End S7LeftScalar.
