From HoTT Require Import Basics.
Require Import Types.Paths Types.Prod Types.Universe.
Require Import Classes.interfaces.abstract_algebra.
Require Import Pointed.Core Pointed.pSusp Spaces.Spheres Truncations.Connectedness.
Require Import Homotopy.HSpace.Core Homotopy.HSpaceS1.
Require Homotopy.HSpaceS3.
Require Import Homotopy.CayleyDickson Homotopy.Suspension Homotopy.Join.Core.
Require Import Homotopy.Join.SuspDiamond Homotopy.Join.MapCoherence.
Require Import Homotopy.NullHomotopy Homotopy.HSpaceS7.LeftScalar.

Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.

(** * First-right scalar actions and the actual turned diamond *)
Module S7RightScalar.
Local Opaque cds_factorneg_l.
Section Scalars.
  Context {X : pType} `{CayleyDicksonSpheroid X}
    `{!Associative (@hspace_op X _)}
    `{!Commutative (@hspace_op X _)}.
  Local Notation assoc := (simple_associativity (f:=hspace_op)).
  Local Notation comm := (commutativity (f:=hspace_op)).

  Definition parameter_swap (a b c d : X)
    : cd_diamond_parameter (-b) a c d = -cd_diamond_parameter a b c d.
  Proof.
    unfold cd_diamond_parameter.
    lhs rapply (ap (fun x => conj c * x * d * conj a) (swapop b)).
    lhs rapply (ap (fun x => x * d * conj a) (factorneg_r (conj c) (conj b))).
    lhs rapply (ap (.* conj a) (factorneg_l (conj c * conj b) d)).
    lhs rapply (factorneg_l (conj c * conj b * d) (conj a)).
    napply (ap (-)).
    lhs rapply (ap (.* conj a) (assoc (conj c) (conj b) d)^).
    lhs rapply (assoc (conj c) (conj b * d) (conj a))^.
    lhs rapply (ap (conj c *.) (comm (conj b * d) (conj a))).
    lhs rapply (ap (fun x => conj c * (conj a * x)) (comm (conj b) d)).
    lhs rapply (ap (conj c *.) (assoc (conj a) d (conj b))).
    lhs rapply (assoc (conj c) (conj a * d) (conj b)).
    exact (ap (.* conj b) (assoc (conj c) (conj a) d)).
  Defined.

  (** Left multiplication by a right-copy scalar exchanges the two labels. Its diamond parameter is the negation of the old parameter. *)
  Definition parameter (s a b c d : X)
    : cd_diamond_parameter ((-b) * conj s) (a * s) c d
      = -cd_diamond_parameter a b c d.
  Proof.
    lhs rapply (ap011 (fun x y => cd_diamond_parameter x y c d)
      (comm (-b) (conj s))
      (comm a s @ ap (.* a) (cds_conjug_inv s)^)).
    exact (S7LeftScalar.left_parameter (conj s) (-b) a c d
      @ parameter_swap a b c d).
  Defined.

  (** These compare the two maps after the actual turn, not just their endpoint values. *)
  Definition map_l (s a c : X)
    : (fun t => cd_diamond_map_l a c t * s)
      == (fun t => cd_diamond_map_r (a * s) c (-t)).
  Proof.
    intro t; unfold cd_diamond_map_l, cd_diamond_map_r.
    lhs rapply (ap (.* s) (comm a (c * -t))).
    lhs rapply (assoc (c * -t) a s)^.
    exact (assoc c (-t) (a * s))^.
  Defined.

  Definition map_r (s b c : X)
    : (fun t => (-cd_diamond_map_r b c t) * conj s)
      == (fun t => cd_diamond_map_l ((-b) * conj s) c (-t)).
  Proof.
    intro t; unfold cd_diamond_map_l, cd_diamond_map_r.
    rhs rapply (ap (fun x => ((-b) * conj s) * (c * x)) (cds_negate_inv t)).
    rhs rapply (assoc (-b) (conj s) (c * t))^.
    rhs rapply (ap ((-b) *.) (comm (conj s) (c * t))).
    rhs rapply (assoc (-b) (c * t) (conj s)).
    napply (ap (.* conj s)).
    rhs rapply (comm (-b) (c * t)).
    rhs rapply (factorneg_r (c * t) b).
    exact (ap (-) (assoc c t b)).
  Defined.
End Scalars.

Section Suspension.
  Universe u.
  Context {A : Type@{u}} `{CayleyDicksonImaginaroid A}
    `{!Associative (@hspace_op (psusp A) _)}
    `{!Commutative (@hspace_op (psusp A) _)}.
  Local Existing Instances negate_susp conjugate_susp cdi_susp_hspace.
  Local Notation X := (psusp A).
  (** Fix the scalar operation and the universe choices of the derived spheroid. The same boundary witnesses are used throughout the comparison. *)
  Local Instance scalar_op : SgOp X := @hspace_op X (@cdi_susp_hspace A H).
  Local Notation conj := (conjugate_susp A cdi_negate).
  Local Notation cds_susp_cdi :=
    (@cds_susp_cdi@{u u u u u u u u u u u u u u u u u u u u u} A).
  Local Notation cd_diamond_map_l := (cd_diamond_map_l (H:=cds_susp_cdi _)).
  Local Notation cd_diamond_map_r := (cd_diamond_map_r (H:=cds_susp_cdi _)).
  Local Notation cd_diamond_parameter := (cd_diamond_parameter (H:=cds_susp_cdi _)).
  Local Notation cd_diamond_map_l_neg_unit := (cd_diamond_map_l_neg_unit (H:=cds_susp_cdi _)).
  Local Notation cd_diamond_map_l_parameter := (cd_diamond_map_l_parameter (H:=cds_susp_cdi _)).
  Local Notation cd_diamond_map_r_unit := (cd_diamond_map_r_unit (H:=cds_susp_cdi _)).
  Local Notation cd_diamond_map_r_parameter := (cd_diamond_map_r_parameter (H:=cds_susp_cdi _)).
  Local Notation cd_op_diamond := (cd_op_diamond (H:=cds_susp_cdi _)).
  Local Notation cd_op_diamond_V := (cd_op_diamond_V (H:=cds_susp_cdi _)).
  Local Notation parameter := (parameter (H:=cds_susp_cdi _)).
  Local Notation map_l := (map_l (H:=cds_susp_cdi _)).
  Local Notation map_r := (map_r (H:=cds_susp_cdi _)).

  Definition e00 (s a c : X)
    : (a * c) * s = c * (a * s)
    := (ap (.* s) (cd_diamond_map_l_neg_unit a c))^
      @ map_l s a c South @ cd_diamond_map_r_unit (a * s) c.
  Definition e01 (s a b c d : X)
    : (-(conj a * d)) * conj s = (-d) * conj (a * s)
    := (ap (fun t => (-t) * conj s) (cd_diamond_map_r_parameter a b c d))^
      @ map_r s b c (cd_diamond_parameter a b c d)
      @ (ap (cd_diamond_map_l ((-b) * conj s) c) (parameter s a b c d)^
        @ cd_diamond_map_l_parameter ((-b) * conj s) (a * s) c d).
  Definition e10 (s b c : X)
    : (-(c * b)) * conj s = ((-b) * conj s) * c
    := (ap (fun t => (-t) * conj s) (cd_diamond_map_r_unit b c))^
      @ map_r s b c North @ cd_diamond_map_l_neg_unit ((-b) * conj s) c.
  Definition e11 (s a b c d : X)
    : ((-d) * conj b) * s = conj ((-b) * conj s) * d
    := (ap (.* s) (cd_diamond_map_l_parameter a b c d))^
      @ map_l s a c (cd_diamond_parameter a b c d)
      @ (ap (cd_diamond_map_r (a * s) c) (parameter s a b c d)^
        @ cd_diamond_map_r_parameter ((-b) * conj s) (a * s) c d).

  (** This compares the actual multiplication fillers. The right-copy left action turns the inverse of the old filler, and its four boundary comparisons run from the translated vertices to the new multiplication vertices. The circle specialization below compares them with the original associator's scalar witnesses. *)
  Definition diamond (s a b c d : X)
    : transport011
        (fun x : X * X => fun y : X * X =>
          zigzag (fst x) (snd x) (fst y) = zigzag (fst x) (snd x) (snd y))
        (path_prod' (e10 s b c) (e01 s a b c d))
        (path_prod' (e00 s a c) (e11 s a b c d))
        (join_diamond_turn (.* s) (fun t => (-t) * conj s)
          (cd_op_diamond a b c d)^)
      = (cd_op_diamond ((-b) * conj s) (a * s) c d)^.
  Proof.
    lhs napply (ap (transport011
      (fun x : X * X => fun y : X * X =>
        zigzag (fst x) (snd x) (fst y) = zigzag (fst x) (snd x) (snd y))
      (path_prod' (e10 s b c) (e01 s a b c d))
      (path_prod' (e00 s a c) (e11 s a b c d)))
      (ap (join_diamond_turn (.* s) (fun t => (-t) * conj s))
        (cd_op_diamond_V a b c d))).
    rhs napply (cd_op_diamond_V ((-b) * conj s) (a * s) c d).
    unfold e00, e01, e10, e11.
    lhs napply (join_diamond_turn_compare
      (cd_diamond_map_l a c) (cd_diamond_map_r b c)
      (.* s) (fun t => (-t) * conj s) (-) (-)
      (cd_diamond_map_l ((-b) * conj s) c) (cd_diamond_map_r (a * s) c)
      (map_l s a c) (map_r s b c) _ _ _ _ _ _ _ _
      (cd_diamond_susp (cd_diamond_parameter a b c d))
      (cd_diamond_susp (-cd_diamond_parameter a b c d))
      (diamond_susp_turn (-) (cd_diamond_parameter a b c d))).
    (** The reindexing argument has a free parameter path and free endpoint witnesses; it does not eliminate a fixed diamond. *)
    assert (R : forall (t t' : X) (p : t = t')
      (q : cd_diamond_map_l ((-b) * conj s) c t' = (-d) * conj (a * s))
      (r : cd_diamond_map_r (a * s) c t' = conj ((-b) * conj s) * d),
      join_zigzag_filler (cd_diamond_map_l ((-b) * conj s) c)
        (cd_diamond_map_r (a * s) c)
        (cd_diamond_map_l_neg_unit ((-b) * conj s) c)
        (ap (cd_diamond_map_l ((-b) * conj s) c) p @ q)
        (cd_diamond_map_r_unit (a * s) c)
        (ap (cd_diamond_map_r (a * s) c) p @ r) (cd_diamond_susp t)
      = join_zigzag_filler (cd_diamond_map_l ((-b) * conj s) c)
        (cd_diamond_map_r (a * s) c)
        (cd_diamond_map_l_neg_unit ((-b) * conj s) c) q
        (cd_diamond_map_r_unit (a * s) c) r (cd_diamond_susp t')).
    { intros t t' p q r; destruct p.
      exact (ap011 (fun q r => join_zigzag_filler
        (cd_diamond_map_l ((-b) * conj s) c) (cd_diamond_map_r (a * s) c)
        (cd_diamond_map_l_neg_unit ((-b) * conj s) c) q
        (cd_diamond_map_r_unit (a * s) c) r (cd_diamond_susp t))
        (concat_1p q) (concat_1p r)). }
    exact (R _ _ (parameter s a b c d)^ _ _).
  Defined.
End Suspension.

Local Set Universe Minimization ToSet.
Local Existing Instances S7LeftScalar.circle_imaginaroid
  S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative
  S7LeftScalar.circle_commutative S7LeftScalar.circle_distropp
  S7LeftScalar.circle_connected S7LeftScalar.circle_truncated.
Local Notation C := (Sphere 1).
Local Notation J := (Join@{Set Set Set} C C).
Local Notation assoc := (simple_associativity (f:=sgop_s1)).
Local Notation comm := (commutativity (f:=sgop_s1)).

Local Notation conj := (conjugate_susp (Sphere 0) HSpaceS3.negate_s0).
Local Notation swapop := (cds_swapop (X:=psphere 1)).
Local Notation factorneg_l :=
  (@cds_factorneg_l (psphere 1) S7LeftScalar.circle_spheroid).

Local Notation p00 := (fun s a c => @cd_assoc_ll_scalar_r@{Set} (psphere 1)
  S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative
  S7LeftScalar.circle_commutative a c s).
Local Notation p01 := (fun s a d => @cd_assoc_lr_scalar_r@{Set} (psphere 1)
  S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative
  S7LeftScalar.circle_commutative a d s).
Local Notation p10 := (fun s b c => @cd_assoc_rl_scalar_r@{Set} (psphere 1)
  S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative
  S7LeftScalar.circle_commutative b c s).
Local Notation p11 := (fun s b d => @cd_assoc_rr_scalar_r@{Set} (psphere 1)
  S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative
  S7LeftScalar.circle_commutative b d s).

Definition standard_00 `{Univalence} (s a c : C)
  : (e00 s a c)^ = p00 s a c.
Proof.
  revert s a c.
  do 3 srapply (conn_point_elim (-1) (A:=psphere 1)).
  reflexivity.
Defined.

(** The following unit calculations concern scalar paths only. In particular, the right-unit path at [South] is not reflexivity. *)
Local Definition comm_unit `{Univalence} (x : C)
  : comm x North = rightidentity_s1 x.
Proof.
  revert x; srapply (conn_point_elim (-1) (A:=psphere 1)).
  reflexivity.
Defined.

Definition assoc_unit `{Univalence} (x : C)
  : assoc x North North = (rightidentity_s1 (x * North))^.
Proof.
  revert x; srapply (conn_point_elim (-1) (A:=psphere 1)).
  reflexivity.
Defined.

Definition distropp_unit `{Univalence} (x : C)
  : cds_conjug_distr (X:=psphere 1) x North
    = ap (conj : C -> C) (rightidentity_s1 x).
Proof.
  revert x; srapply (conn_point_elim (-1) (A:=psphere 1)).
  reflexivity.
Defined.

Definition factorneg_r_unit (x : C)
  : HSpaceS3.factorneg_r_s1 North x = 1.
Proof.
  unfold HSpaceS3.factorneg_r_s1.
  lhs napply (ap_idmap _ @@ 1).
  apply concat_pV.
Defined.

Local Definition left_parameter_unit `{Univalence} (a b c d : C)
  : S7LeftScalar.left_parameter (X:=psphere 1) North a b c d = 1.
Proof.
  revert a b c d.
  do 4 srapply (conn_point_elim (-1) (A:=psphere 1)).
  reflexivity.
Defined.

Local Transparent cds_factorneg_l.
Definition factorneg_l_unit `{Univalence}
  : factorneg_l (North : C) North = rightidentity_s1 South.
Proof.
  pose (ec := isequiv_adjointify (conj : C -> C) conj
    (cds_conjug_inv (X:=psphere 1)) (cds_conjug_inv (X:=psphere 1))).
  nrefine (@equiv_inj _ _ (ap (conj : C -> C))
    (@isequiv_ap C C (conj : C -> C) ec _ _) _ _ _).
  unfold cds_factorneg_l.
  lhs napply ap_equiv_inj.
  change (cds_conjug_distr (X:=psphere 1) South North
    @ (((1 @ HSpaceS3.factorneg_r_s1 North North) @ 1) @ 1)
    = ap (conj : C -> C) (rightidentity_s1 South)).
  lhs napply (1 @@ (((1 @@ factorneg_r_unit North) @@ 1) @@ 1)).
  lhs napply concat_p1.
  exact (distropp_unit South).
Defined.

Local Opaque cds_factorneg_l.

Definition right_unit_south
  : rightidentity_s1 South = merid (South : Sphere 0).
Proof.
  change (transport (fun x : C => x * North = x)
    (merid South) 1 = merid South).
  lhs napply (transport_paths_FlFr
    (f:=fun x : C => x * North) (g:=idmap) (merid South) 1).
  lhs napply ((inverse2 (Susp_rec_beta_merid South) @@ 1) @@ 1).
  lhs napply concat_1p.
  apply ap_idmap.
Defined.

Local Definition map_r_unit `{Univalence}
  : map_r (X:=psphere 1) North North North North = 1.
Proof.
  change (((((ap (.* North)
    ((1 @ (HSpaceS3.factorneg_r_s1 North North)^) @ (comm South North)^)
      @ (assoc South North North)^) @ 1)
      @ ((assoc South North North)^)^) @ 1) = 1).
  rewrite factorneg_r_unit, comm_unit, assoc_unit, right_unit_south.
  rewrite concat_1p, ap_V, (Susp_rec_beta_merid South).
  reflexivity.
Defined.

Local Definition parameter_unit `{Univalence}
  : parameter (X:=psphere 1) North North North North North
    = merid (North : Sphere 0).
Proof.
  change (ap011 (fun x y : C => sgop_s1 (sgop_s1 (conj x) North) (conj y))
      (comm South North) (idpath (North : C))
    @ (S7LeftScalar.left_parameter (X:=psphere 1) North South North North North
      @ (1 @ (ap (fun x : C => sgop_s1 (sgop_s1 x North) North)
          (HSpaceS3.factorneg_r_s1 North North)
        @ (ap (fun x : C => sgop_s1 x North) (factorneg_l (North : C) North)
          @ (factorneg_l (North : C) North @ 1)))))
    = merid (North : Sphere 0)).
  rewrite left_parameter_unit, factorneg_r_unit, factorneg_l_unit,
    comm_unit, right_unit_south.
  rewrite ap011_is_ap.
  rewrite (Susp_rec_beta_merid South).
  rewrite !concat_1p, !concat_p1.
  rewrite (ap_compose conj
    (fun x : C => sgop_s1 (sgop_s1 x North) North) (merid South)).
  rewrite (functor_susp_beta_merid HSpaceS3.negate_s0 South).
  rewrite (ap_compose (fun x : C => sgop_s1 x North)
    (fun x : C => sgop_s1 x North) (merid North)).
  rewrite (Susp_rec_beta_merid North).
  rewrite (Sph1_rec_beta_loop _ North (s1_turn North)).
  apply concat_pV_p.
Defined.

Definition map_l_parameter_unit `{Univalence}
  : cd_diamond_map_l_parameter (X:=psphere 1) North North North North
    = (merid (South : Sphere 0))^.
Proof.
  change (((ap idmap (HSpaceS3.factorneg_r_s1 North North)
    @ HSpaceS3.factorneg_r_s1 North North) @ 1)
    @ (factorneg_l (North : C) North)^ = (merid (South : Sphere 0))^).
  rewrite factorneg_r_unit, factorneg_l_unit, right_unit_south.
  apply concat_1p.
Defined.

Definition standard_01 `{Univalence} (s a b c d : C)
  : (e01 s a b c d)^ = p01 s a d.
Proof.
  revert s a b c d.
  do 5 srapply (conn_point_elim (-1) (A:=psphere 1)).
  change ((e01 North North North North North)^ = p01 North North North).
  change (((1 @ map_r (X:=psphere 1) North North North North) @
    (ap (-) (parameter (X:=psphere 1) North North North North North)^
      @ cd_diamond_map_l_parameter (X:=psphere 1) North North North North))^
    = p01 North North North).
  rewrite map_r_unit, parameter_unit, map_l_parameter_unit.
  rewrite ap_V.
  rewrite (ap_compose (conjugate_susp (Sphere 0) HSpaceS3.negate_s0)
    (susp_neg (Sphere 0)) (merid North)).
  rewrite functor_susp_beta_merid, (Susp_rec_beta_merid South), inv_V.
  unfold cd_assoc_lr_scalar_r.
  change ((1 @ ((merid (South : Sphere 0)) @ (merid South)^))^
    = (factorneg_l (North : C) North @ 1) @ (factorneg_l (North : C) North)^).
  rewrite !concat_p1, !concat_pV.
  reflexivity.
Defined.

Definition standard_10 `{Univalence} (s b c : C)
  : (e10 s b c)^ = p10 s b c.
Proof.
  revert s b c.
  do 3 srapply (conn_point_elim (-1) (A:=psphere 1)).
  change (((1 @ map_r (X:=psphere 1) North North North North) @ 1)^
    = p10 North North North).
  rewrite map_r_unit.
  unfold cd_assoc_rl_scalar_r.
  change (1 = ap (fun x : C => sgop_s1 x North) (factorneg_l (North : C) North)
    @ ((factorneg_l (North : C) North @ 1) @ (factorneg_l (North : C) North)^)).
  rewrite factorneg_l_unit, right_unit_south, (Susp_rec_beta_merid South).
  rewrite concat_p1, concat_pV.
  reflexivity.
Defined.

Local Definition map_l_unit `{Univalence}
  : map_l (X:=psphere 1) North North North North = 1.
Proof.
  change (ap (fun x : C => sgop_s1 x North) (rightidentity_s1 South)^
    @ ((assoc South North North)^ @ 1) = 1).
  rewrite assoc_unit, right_unit_south, ap_V, (Susp_rec_beta_merid South).
  reflexivity.
Defined.

Definition standard_11 `{Univalence} (s a b c d : C)
  : (e11 s a b c d)^ = p11 s b d.
Proof.
  revert s a b c d.
  do 5 srapply (conn_point_elim (-1) (A:=psphere 1)).
  change (((ap (fun x : C => sgop_s1 x North)
      (cd_diamond_map_l_parameter (X:=psphere 1) North North North North))^
    @ map_l (X:=psphere 1) North North North North
    @ (ap (fun x : C => sgop_s1 x North)
      (parameter (X:=psphere 1) North North North North North)^ @ 1))^
    = p11 North North North).
  rewrite map_l_parameter_unit, map_l_unit, parameter_unit.
  rewrite !ap_V, (Susp_rec_beta_merid South), (Susp_rec_beta_merid North).
  unfold cd_assoc_rr_scalar_r.
  change (((1 @ 1) @ ((s1_turn North)^ @ 1))^
    = ap (fun x : C => sgop_s1 x North)
        (cds_conjug_distr (X:=psphere 1) South North)
      @ (1 @ (1 @ (ap (fun x : C => sgop_s1 x North)
        (HSpaceS3.factorneg_r_s1 North North)
      @ (factorneg_l (North : C) North
        @ ((1 @ (factorneg_l (North : C) North)^)
          @ ap (fun x : C => sgop_s1 x North) (factorneg_l (North : C) North)^)))))).
  rewrite distropp_unit, factorneg_r_unit, factorneg_l_unit, right_unit_south.
  rewrite functor_susp_beta_merid, !ap_V,
    (Susp_rec_beta_merid North), (Susp_rec_beta_merid South).
  rewrite !concat_p1, !concat_1p, !concat_pV, inv_V.
  symmetry; apply concat_p1.
Defined.

Local Opaque parameter_unit map_l_unit map_r_unit map_l_parameter_unit.
Local Opaque standard_00 standard_01 standard_10 standard_11.
Local Opaque cd_op_diamond associative_sgop_s1 commutative_sgop_s1.
Local Opaque sgop_s1 conjugate_susp negate_susp.
Local Notation mu := (@cd_op@{Set} (psphere 1)
  S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative cd_diamond_susp).
Local Notation D := (@cd_op_diamond@{Set} (psphere 1)
  S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative cd_diamond_susp).
Local Notation first_rl := (@cd_assoc_first_rl@{Set} (psphere 1)
  S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative cd_diamond_susp
  S7LeftScalar.circle_commutative).
Local Notation first_rr := (@cd_assoc_first_rr@{Set} (psphere 1)
  S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative cd_diamond_susp
  S7LeftScalar.circle_commutative).

Definition diamond_standard `{Univalence} (s a b c d : C)
  : transport011
      (fun x : C * C => fun y : C * C =>
        zigzag (fst x) (snd x) (fst y) = zigzag (fst x) (snd x) (snd y))
      (path_prod' (p10 s b c) (p01 s a d))
      (path_prod' (p11 s b d) (p00 s a c))
      (D ((-b) * conj s) (a * s) c d)
    = (join_diamond_turn (.* s) (fun t => (-t) * conj s) (D a b c d)^)^.
Proof.
  lhs_V napply (ap011 (fun p q => transport011 _ p q
    (D ((-b) * conj s) (a * s) c d))
    (ap011 path_prod' (standard_10 s b c) (standard_01 s a b c d))
    (ap011 path_prod' (standard_11 s a b c d) (standard_00 s a c))).
  lhs_V napply (ap (transport011
    (fun x : C * C => fun y : C * C =>
      zigzag (fst x) (snd x) (fst y) = zigzag (fst x) (snd x) (snd y))
    (path_prod' (e10 s b c)^ (e01 s a b c d)^)
    (path_prod' (e11 s a b c d)^ (e00 s a c)^))
    (inv_V (D ((-b) * conj s) (a * s) c d))).
  exact (join_zigzag_filler_transport_inverse
    (e10 s b c) (e01 s a b c d) (e00 s a c) (e11 s a b c d)
    _ _ (diamond s a b c d)).
Defined.

Definition first_r_glue_l `{Univalence} (s a b c : C)
  : ap (fun y => mu (mu (joinr s) y) (joinl c)) (jglue a b)
      @ first_rr s b (joinl c)
    = first_rl s a (joinl c)
      @ ap (fun y => mu (joinr s) (mu y (joinl c))) (jglue a b).
Proof.
  nrefine (naturality_change _ _
    (inverse_natural _ _ (join_natsq (p10 s b c) (p00 s a c)))).
  - exact (((ap_compose (mu (joinr s)) (fun y => mu y (joinl c)) (jglue a b)
      @ ap (ap (fun y => mu y (joinl c))) (Join_rec_beta_jglue (P:=J) _ _
        (fun a b => (jglue ((-b) * conj s) (a * s))^) a b))
      @ ap_V (fun y => mu y (joinl c)) (jglue ((-b) * conj s) (a * s)))
      @ inverse2 (Join_rec_beta_jglue _ _
        (fun a b => jglue (a * c) (c * b)) ((-b) * conj s) (a * s))).
  - exact ((ap_compose (fun y => mu y (joinl c)) (mu (joinr s)) (jglue a b)
      @ ap (ap (mu (joinr s))) (Join_rec_beta_jglue _ _
        (fun a b => jglue (a * c) (c * b)) a b))
      @ Join_rec_beta_jglue (P:=J) _ _
        (fun a b => (jglue ((-b) * conj s) (a * s))^) (a * c) (c * b)).
Defined.

Definition first_r_glue_r `{Univalence} (s a b d : C)
  : ap (fun y => mu (mu (joinr s) y) (joinr d)) (jglue a b)
      @ first_rr s b (joinr d)
    = first_rl s a (joinr d)
      @ ap (fun y => mu (joinr s) (mu y (joinr d))) (jglue a b).
Proof.
  pose (brho := fun a b : C => Join_rec_beta_jglue (P:=J) _ _
    (fun a b => (jglue ((-b) * conj s) (a * s))^) a b).
  nrefine (naturality_change _ _ (join_natsq (p01 s a d) (p11 s b d))^).
  - exact (((ap_compose (mu (joinr s)) (fun y => mu y (joinr d)) (jglue a b)
      @ ap (ap (fun y => mu y (joinr d))) (brho a b))
      @ ap_V (fun y => mu y (joinr d)) (jglue ((-b) * conj s) (a * s)))
      @ (inverse2 (Join_rec_beta_jglue _ _
        (fun a b => (jglue ((-d) * conj b) (conj a * d))^)
        ((-b) * conj s) (a * s))
        @ inv_V (jglue ((-d) * conj (a * s)) (conj ((-b) * conj s) * d)))).
  - exact ((ap_compose (fun y => mu y (joinr d)) (mu (joinr s)) (jglue a b)
      @ ap (ap (mu (joinr s))) (Join_rec_beta_jglue _ _
        (fun a b => (jglue ((-d) * conj b) (conj a * d))^) a b))
      @ ((ap_V (mu (joinr s)) (jglue ((-d) * conj b) (conj a * d))
        @ inverse2 (brho ((-d) * conj b) (conj a * d)))
        @ inv_V (jglue ((-(conj a * d)) * conj s) (((-d) * conj b) * s)))).
Defined.

(** Convert the actual turned filler, including both reversed-glue computations and the four original side witnesses. *)
Definition first_r_glue_glue `{Univalence} (s a b c d : C)
  : transport
      (fun z => ap (fun y => mu (mu (joinr s) y) z) (jglue a b)
          @ first_rr s b z
        = first_rl s a z
          @ ap (fun y => mu (joinr s) (mu y z)) (jglue a b))
      (jglue c d) (first_r_glue_l s a b c) = first_r_glue_r s a b d.
Proof.
  pose (rho := mu (joinr s)).
  pose (A := (-b) * conj s).
  pose (B := a * s).
  pose (g0 := mu (joinl a)).
  pose (g1 := mu (joinr b)).
  pose (W := fun a b z => ap (fun y => mu y z) (jglue a b)).
  pose (U := fun z => ap (fun y => mu (rho y) z) (jglue a b)).
  pose (V := fun z => ap (fun y => rho (mu y z)) (jglue a b)).
  pose (brho := fun a b : C => Join_rec_beta_jglue (P:=J) _ _
    (fun a b => (jglue ((-b) * conj s) (a * s))^) a b).
  pose (bh0 := fun a c d : C => Join_rec_beta_jglue _ _
    (fun c d => jglue (a * c) (conj a * d)) c d).
  pose (bh1 := fun b c d : C => Join_rec_beta_jglue _ _
    (fun c d => (jglue ((-d) * conj b) (c * b))^) c d).
  pose (bv0 := fun a b c : C => Join_rec_beta_jglue _ _
    (fun a b => jglue (a * c) (c * b)) a b).
  pose (bv1 := fun a b d : C => Join_rec_beta_jglue _ _
    (fun a b => (jglue ((-d) * conj b) (conj a * d))^) a b).
  pose (tF := fun z => (ap_compose rho (fun y => mu y z) (jglue a b)
    @ ap (ap (fun y => mu y z)) (brho a b))
    @ ap_V (fun y => mu y z) (jglue A B)).
  pose (tG := fun z => ap_compose (fun y => mu y z) rho (jglue a b)).
  pose (bfh0 := bh1 B c d).
  pose (bfh1 := bh0 A c d).
  pose (bfv0 := tF (joinl c) @ inverse2 (bv0 A B c)).
  pose (bfv1 := tF (joinr d)
    @ (inverse2 (bv1 A B d) @ inv_V (jglue ((-d) * conj B) (conj A * d)))).
  pose (bgh0 := (ap_compose g0 rho (jglue c d) @ ap (ap rho) (bh0 a c d))
    @ brho (a * c) (conj a * d)).
  pose (bgh1 := (ap_compose g1 rho (jglue c d) @ ap (ap rho) (bh1 b c d))
    @ ((ap_V rho (jglue ((-d) * conj b) (c * b))
      @ inverse2 (brho ((-d) * conj b) (c * b)))
      @ inv_V (jglue ((-(c * b)) * conj s) (((-d) * conj b) * s)))).
  pose (bgv0 := (tG (joinl c) @ ap (ap rho) (bv0 a b c))
    @ brho (a * c) (c * b)).
  pose (bgv1 := (tG (joinr d) @ ap (ap rho) (bv1 a b d))
    @ ((ap_V rho (jglue ((-d) * conj b) (conj a * d))
      @ inverse2 (brho ((-d) * conj b) (conj a * d)))
      @ inv_V (jglue ((-(conj a * d)) * conj s) (((-d) * conj b) * s)))).
  pose (cf := (1 @@ inv_V (jglue ((-d) * conj B) (conj A * d)))^
    @ (inverse_natural (jglue (A * c) (conj A * d))
      (jglue ((-d) * conj B) (c * B))^ (D A B c d))^).
  pose (dg := join_diamond_turn (fun t : C => t * s)
    (fun t : C => (-t) * conj s) (D a b c d)^).
  pose (cg := (1 @@ inv_V
      (jglue ((-(conj a * d)) * conj s) (((-d) * conj b) * s)))^
    @ (inverse_natural (jglue ((-(c * b)) * conj s) (((-d) * conj b) * s))
      (jglue ((-(conj a * d)) * conj s) ((a * c) * s))^ dg^)^).
  assert (BM : forall a b c d, concat_Ap (W a b) (jglue c d) @ (bv0 a b c @@ 1)
    = (1 @@ bv1 a b d) @ naturality_change (bh0 a c d) (bh1 b c d) (D a b c d)).
  { intros a0 b0 c0 d0.
    nrefine (Join_rec2_beta_jglue_jglue J
      _ _ _ _ _ _ _ _ D a0 b0 c0 d0 @ _).
    exact (1 @@ concat_p_pp _ _ _). }
  assert (BF : concat_Ap U (jglue c d) @ (bfv0 @@ 1)
    = (1 @@ bfv1) @ naturality_change bfh0 bfh1 cf).
  { napply (mixed_beta_vertical (tF (joinl c)) (tF (joinr d))
      (inverse2 (bv0 A B c))
      (inverse2 (bv1 A B d) @ inv_V (jglue ((-d) * conj B) (conj A * d)))
      _ _ _ (concat_Ap (fun z => (W A B z)^) (jglue c d)) _).
    - exact (concat_Ap_homotopic U (fun z => (W A B z)^) tF (jglue c d)).
    - lhs napply (concat_Ap_inverse (W A B) (jglue c d) @@ 1).
      exact (inverse_mixed_beta (bh0 A c d) (bv1 A B d)
        (bv0 A B c) (bh1 B c d) _ _ (BM A B c d)). }
  assert (BG : concat_Ap V (jglue c d) @ (bgv0 @@ 1)
    = (1 @@ bgv1) @ naturality_change bgh0 bgh1 cg).
  { napply (mixed_beta_compose
      (ap_compose g0 rho (jglue c d) @ ap (ap rho) (bh0 a c d))
      (tG (joinr d) @ ap (ap rho) (bv1 a b d))
      (tG (joinl c) @ ap (ap rho) (bv0 a b c))
      (ap_compose g1 rho (jglue c d) @ ap (ap rho) (bh1 b c d))
      _ _ _ _ _ (ap_naturality rho (D a b c d)) _).
    - napply (mixed_beta_vertical (tG (joinl c)) (tG (joinr d))
        (ap (ap rho) (bv0 a b c)) (ap (ap rho) (bv1 a b d)) _ _
        _ (concat_Ap (fun z => ap rho (W a b z)) (jglue c d)) _).
      + exact (concat_Ap_homotopic V (fun z => ap rho (W a b z)) tG (jglue c d)).
      + exact (concat_Ap_postcompose_beta (W a b) rho (jglue c d)
          (bh0 a c d) (bv1 a b d) (bv0 a b c) (bh1 b c d) _ (BM a b c d)).
    - lhs_V napply (ap (fun h => ap_naturality rho h
        @ (brho (a * c) (c * b) @@ 1)) (inv_V (D a b c d))).
      exact (turn_filler_beta rho
        (jglue (a * c) (c * b)) (jglue ((-d) * conj b) (c * b))
        (jglue (a * c) (conj a * d)) (jglue ((-d) * conj b) (conj a * d))
        (brho _ _) (brho _ _) (brho _ _) (brho _ _) (D a b c d)^). }
  pose (eh0 := inverse_natural _ _ (join_natsq (p01 s a d) (p00 s a c))).
  pose (eh1 := (join_natsq (p10 s b c) (p11 s b d))^).
  pose (ev0 := inverse_natural _ _ (join_natsq (p10 s b c) (p00 s a c))).
  pose (ev1 := (join_natsq (p01 s a d) (p11 s b d))^).
  assert (EH0 : concat_Ap (first_rl s a) (jglue c d)
    = naturality_change bfh0 bgh0 eh0).
  { lhs napply (Join_ind_FlFr_beta_jglue _ _ _ _ _ c d).
    rhs napply concat_pp_p.
    napply (ap (fun q => (bfh0 @@ 1) @ q)).
    lhs napply naturality_suffix.
    apply naturality_suffix. }
  assert (EH1 : concat_Ap (first_rr s b) (jglue c d)
    = naturality_change bfh1 bgh1 eh1).
  { lhs napply (Join_ind_FlFr_beta_jglue _ _ _ _ _ c d).
    rhs napply concat_pp_p.
    napply (ap (fun q => (bfh1 @@ 1) @ q)).
    do 4 (lhs napply naturality_suffix).
    napply (ap (fun q => eh1 @ (1 @@ q)^)).
    unfold bgh1; rewrite !concat_p_pp.
    reflexivity. }
  assert (EV0 : first_r_glue_l s a b c = naturality_change bfv0 bgv0 ev0).
  { reflexivity. }
  assert (EV1 : first_r_glue_r s a b d = naturality_change bfv1 bgv1 ev1).
  { reflexivity. }
  refine (ap (transport _ (jglue c d)) EV0 @ _ @ EV1^).
  napply (transport_naturality_square_beta U V
    (first_rl s a) (first_rr s b) (jglue c d)
    bfh0 bfh1 bfv0 bfv1 bgh0 bgh1 bgv0 bgv1
    cf cg eh0 eh1 ev0 ev1 BF BG EH0 EH1).
  exact (join_zigzag_filler_cube_inverse (p10 s b c) (p01 s a d)
    (p11 s b d) (p00 s a c) _ _ (diamond_standard s a b c d)).
Defined.

Definition first_r_glue `{Univalence} (s a b : C) : forall z : J,
  ap (fun y => mu (mu (joinr s) y) z) (jglue a b) @ first_rr s b z
    = first_rl s a z @ ap (fun y => mu (joinr s) (mu y z)) (jglue a b).
Proof.
  snapply Join_ind.
  - exact (first_r_glue_l s a b).
  - exact (first_r_glue_r s a b).
  - exact (first_r_glue_glue s a b).
Defined.

(** This right-copy associator retains both original constructor rows definitionally. *)
Definition first_r `{Univalence} (s : C) (y z : J)
  : mu (mu (joinr s) y) z = mu (joinr s) (mu y z).
Proof.
  revert y; snapply Join_ind_FlFr.
  - exact (fun a => first_rl s a z).
  - exact (fun b => first_rr s b z).
  - exact (fun a b => first_r_glue s a b z).
Defined.

Local Opaque first_r_glue_glue.
Local Transparent associative_sgop_s1 commutative_sgop_s1.
Local Transparent sgop_s1 conjugate_susp negate_susp.

Definition overlap_scalar_l `{Univalence} (s a c : C)
  : comm c (a * s) @ (cd_diamond_translate_r_unit (X:=psphere 1) s a c)^
    = p00 s a c.
Proof.
  revert s a c.
  do 3 srapply (conn_point_elim (-1) (A:=psphere 1)).
  reflexivity.
Defined.

Definition overlap_scalar_r `{Univalence} (s b c : C)
  : (cd_diamond_translate_l_parameter (X:=psphere 1) North s North b c)^
      @ ap (fun t : C => (-t) * conj s) (comm c b)^
    = p10 s b c.
Proof.
  revert s b c.
  do 3 srapply (conn_point_elim (-1) (A:=psphere 1)).
  change ((cd_diamond_translate_l_parameter (X:=psphere 1)
    North North North North North)^ @ 1 = p10 North North North).
  assert (L : cd_diamond_translate_l_parameter (X:=psphere 1)
    North North North North North = 1).
  { pose (z := cd_diamond_map_l_normalize (X:=psphere 1) North North North).
    assert (Z : z = (merid (South : Sphere 0))^).
    { assert (LU : forall x : C, leftidentity_s1 x = 1).
      { srapply (conn_point_elim (-1) (A:=psphere 1)); reflexivity. }
      change ((ap idmap (rightidentity_s1 South)^ @ 1)
        @ (ap (fun x : C => sgop_s1 x North) (ap idmap (leftidentity_s1 South)))^
        = (merid (South : Sphere 0))^).
      rewrite LU, ap_idmap, right_unit_south, !concat_p1.
      reflexivity. }
    change (((cd_diamond_map_l_parameter (X:=psphere 1) North North North North)^
      @ ((z @ (assoc South North North
        @ ap (fun x : C => sgop_s1 x North) z^)) @ 1))
      @ ap (fun x : C => sgop_s1 x North)
        (cd_diamond_map_l_parameter (X:=psphere 1) North North North North) = 1).
    rewrite Z, assoc_unit, map_l_parameter_unit.
    rewrite !ap_V, !inv_V, (Susp_rec_beta_merid South).
    rewrite !concat_p1, concat_pV.
    reflexivity. }
  rewrite L.
  rhs_V napply (standard_10 North North North).
  change (1 = ((1 @ map_r (X:=psphere 1) North North North North) @ 1)^).
  rewrite map_r_unit; reflexivity.
Defined.

Local Opaque associative_sgop_s1 commutative_sgop_s1.
Local Opaque sgop_s1 conjugate_susp negate_susp.
Local Notation AL := (@cd_assoc_last_joinl@{Set} (psphere 1)
  S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative cd_diamond_susp
  S7LeftScalar.circle_commutative S7LeftScalar.circle_connected S7LeftScalar.circle_truncated).
Local Notation T := (@cd_assoc_last_transport@{Set} (psphere 1)
  S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative cd_diamond_susp
  S7LeftScalar.circle_commutative S7LeftScalar.circle_connected S7LeftScalar.circle_truncated).
Local Notation qrl := (@cd_assoc_last_joinl_first_rl@{Set} (psphere 1)
  S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative cd_diamond_susp
  S7LeftScalar.circle_commutative S7LeftScalar.circle_connected S7LeftScalar.circle_truncated).
Local Notation qrr := (@cd_assoc_last_joinl_first_rr@{Set} (psphere 1)
  S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative cd_diamond_susp
  S7LeftScalar.circle_commutative S7LeftScalar.circle_connected S7LeftScalar.circle_truncated).
Local Notation mrl := (@cd_assoc_last_transport_loop_rl@{Set} (psphere 1)
  S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative cd_diamond_susp
  S7LeftScalar.circle_commutative S7LeftScalar.circle_connected S7LeftScalar.circle_truncated).
Local Notation mrr := (@cd_assoc_last_transport_loop_rr@{Set} (psphere 1)
  S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative cd_diamond_susp
  S7LeftScalar.circle_commutative S7LeftScalar.circle_connected S7LeftScalar.circle_truncated).

(** Agreement on the last-left restriction, using the original two triangle witnesses. *)
Definition overlap_glue `{Univalence} (s a b c : C)
  : concat_Ap (fun y => AL (joinr s) y c) (jglue a b) @ (qrl s a c @@ 1)
    = (1 @@ qrr s b c) @ first_r_glue_l s a b c.
Proof.
  pose (v := JoinMapCoherence.translation_turn_comparison
    (North : C) (North : C)
    (fun x : C => sgop_s1 x s) (fun x : C => sgop_s1 (-x) (conj s))
    (fun x : C => sgop_s1 x c) (sgop_s1 c) (fun x : C => sgop_s1 x c)
    (comm c)
    (fun b => cd_diamond_translate_l_parameter (X:=psphere 1) North s North b c)
    (fun a => cd_diamond_translate_r_unit (X:=psphere 1) s a c)
    (fun a => p00 s a c) (fun b => p10 s b c)
    (fun a => overlap_scalar_l s a c) (fun b => overlap_scalar_r s b c) a b).
  lhs exact v.
  napply whiskerL.
  exact (Join_ind_FlFr_beta_jglue _ _ _ _ _ a b).
Defined.

Definition overlap `{Univalence} (s : C) (y : J) (c : C)
  : AL (joinr s) y c = first_r s y (joinl c).
Proof.
  revert y; snapply Join_ind.
  - exact (fun a => qrl s a c).
  - exact (fun b => qrr s b c).
  - intros a b.
    nrefine (equiv_naturality_transport2 _ _ (jglue a b) _ _ _).
    rhs napply (1 @@ Join_ind_FlFr_beta_jglue _ _ _ _ _ a b).
    exact (overlap_glue s a b c).
Defined.

Definition row_loop `{Univalence} (s d : C) (y : J) {c : C} (p : c = c)
  : ap (T (joinr s) y d) p = 1.
Proof.
  pose (K := fun c => ap (transport _ (jglue c d)) (overlap s y c)
    @ apD (first_r s y) (jglue c d)).
  exact (ap_loop_nullhomotopic K p).
Defined.

Local Opaque ap_loop_nullhomotopic.

Definition row_loop_l `{Univalence} (s a d : C) {c : C} (p : c = c)
  : row_loop s d (joinl a) p = mrl s a d p := idpath.
Definition row_loop_r `{Univalence} (s b d : C) {c : C} (p : c = c)
  : row_loop s d (joinr b) p = mrr s b d p := idpath.

(** OPEN 2, with the actual suspension diamond and the original corner loop proofs. The scalar loop is arbitrary. *)
Definition loop_y_joinr `{Univalence} (s a b d : C) {c : C} (p : c = c)
  : transport (fun y => ap (T (joinr s) y d) p = 1) (jglue a b)
      (mrl s a d p) = mrr s b d p.
Proof.
  exact (apD (fun y => row_loop s d y p) (jglue a b)).
Defined.
End S7RightScalar.
