From HoTT Require Import Basics.
Require Import Types.Paths Types.Universe.
Require Import Classes.interfaces.canonical_names.
Require Import Pointed.Core Spaces.Spheres.
Require Import Homotopy.HSpaceS1 Homotopy.HSpaceS3.
Require Import Homotopy.Suspension Homotopy.CayleyDickson.
Require Import Homotopy.Join.Core Homotopy.Join.SuspDiamond.
Require Import Homotopy.HSpaceS7.LeftScalar Homotopy.HSpaceS7.RightScalar.

Local Set Universe Minimization ToSet.
Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.

(** * Canonical diamond rotation for the right-right comparison *)

(** The scalar maps reverse both pairs of rectangle vertices. The meridian calculation below retains the actual mapped filler and both selected pole comparisons. Applying this geometry to [eta_associator] with its prescribed overlap computations remains a separate step. *)
Module S7RightRight.
Section Circle.
Context `{Univalence}.
Local Existing Instances S7LeftScalar.circle_imaginaroid
  S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative
  S7LeftScalar.circle_commutative.
Local Notation C := (Sphere 1).
Local Notation conj := (conjugate_susp (Sphere 0) negate_s0).
Local Notation neg := (negate_susp (Sphere 0) negate_s0).
Local Notation L := (fun u z : C => sgop_s1 (neg u) z).
Local Notation R := (fun u z : C => sgop_s1 u z).

Definition rot_p (u : C) : L u South = u
  := factorneg_r (neg u) North
    @ ap neg (rightidentity_s1 (neg u)) @ cds_negate_inv u.
Definition rot_s (u : C) : R u (conj u) = North
  := @cds_conjug_right_inv (psphere 1) S7LeftScalar.circle_spheroid u.
Definition rot_q (u : C) : L u (conj u) = South
  := @cds_factorneg_l (psphere 1) S7LeftScalar.circle_spheroid
      u (conj u) @ ap neg (rot_s u).
Definition rot_r (u : C) : R u North = u := rightidentity_s1 u.
Let rotation_map (u : C)
  (h : zigzag South (conj u) North = zigzag South (conj u) (conj u))
  := join_zigzag_filler (L u) (R u)
    (rot_p u) (rot_q u) (rot_r u) (rot_s u) h.
Definition Rotation (u : C)
  := rotation_map u (diamond_susp (conj u))
    = join_diamond_rotate (diamond_susp u).

Definition rotation_north : Rotation North
  := join_zigzag_filler_rotate_v (L North) (R North)
    South North North (rot_p North) (rot_q North)
    (rot_r North) (rot_s North) 1.

Local Definition rot_s_south : rot_s South = (merid North)^.
Proof.
  lhs_V napply (apD rot_s (merid (South : Sphere 0))).
  lhs napply (transport_paths_Fl
    (f:=fun u : C => sgop_s1 u (conj u)) (merid South) 1).
  lhs napply concat_p1.
  napply inverse2.
  lhs_V napply (ap011_diag (fun x y : C => sgop_s1 y (conj x))
    (merid South)).
  lhs napply (ap011_is_ap (fun x y : C => sgop_s1 y (conj x))).
  lhs napply (functor_susp_beta_merid negate_s0 South @@ 1).
  lhs napply (1 @@ Susp_rec_beta_merid South).
  apply concat_p1.
Defined.

Local Definition distropp_south_south
  : conjugate_s1_distropp South South
    = (merid South)^ @ merid North.
Proof.
  lhs_V napply (apD (fun x : C => conjugate_s1_distropp x South)
    (merid (South : Sphere 0))).
  lhs napply (transport_paths_FlFr
    (f:=fun x : C => conj (sgop_s1 x South))
    (g:=fun x : C => sgop_s1 (conj South) (conj x))
    (merid South) _).
  lhs napply ((inverse2 (ap_compose (fun x : C => sgop_s1 x South)
    conj (merid South)) @@ 1) @@ 1).
  lhs napply ((inverse2 (ap (ap conj)
    (Susp_rec_beta_merid South)) @@ 1) @@ 1).
  lhs napply (concat_1p _ @@ 1).
  exact (inverse2 S7RightScalar.right_unit_south
    @@ functor_susp_beta_merid negate_s0 South).
Defined.

Local Definition rot_p_south : rot_p South = 1.
Proof.
  change ((factorneg_r_s1 North North @ 1) @ 1 = 1).
  lhs napply ((S7RightScalar.factorneg_r_unit North @@ 1) @@ 1).
  reflexivity.
Defined.

Local Definition rot_q_south : rot_q South = 1.
Proof.
  unfold rot_q.
  lhs napply (1 @@ ap (ap neg) rot_s_south).
  pose (ec := isequiv_adjointify (conj : C -> C) conj
    (cds_conjug_inv (X:=psphere 1)) (cds_conjug_inv (X:=psphere 1))).
  nrefine (@equiv_inj _ _ (ap (conj : C -> C))
    (@isequiv_ap C C (conj : C -> C) ec _ _) _ _ _).
  lhs napply ap_pp.
  unfold cds_factorneg_l.
  lhs napply (ap_equiv_inj _ _ @@ 1).
  change (((rightidentity_s1 South)^
    @ (((1 @ factorneg_r_s1 North South)
      @ (ap neg (conjugate_s1_distropp South South))^) @ 1))
    @ ap conj (ap neg (merid North)^) = 1).
  rewrite S7RightScalar.factorneg_r_unit, distropp_south_south,
    S7RightScalar.right_unit_south.
  rewrite !concat_1p, !concat_p1, ap_pp, !ap_V.
  rewrite (ap_compose conj (susp_neg (Sphere 0)) (merid South)),
    (ap_compose conj (susp_neg (Sphere 0)) (merid North)).
  rewrite !functor_susp_beta_merid, !Susp_rec_beta_merid, !inv_V.
  rewrite ap_V, functor_susp_beta_merid, inv_V, inv_pV.
  exact ((concat_V_pp _ _ @@ 1) @ concat_Vp _).
Defined.

Definition rotation_south : Rotation South
  := join_zigzag_filler_rotate_h (L South) (R South)
    South North South (rot_p South) (rot_q South)
    (rot_r South) (rot_s South) (rot_p_south @ rot_q_south^).

(** Rotation of the chosen suspension diamond, not merely its boundary. *)
Definition rotation : forall u : C, Rotation u.
Proof.
  snapply Susp_ind.
  - exact rotation_north.
  - exact rotation_south.
  - intro a.
    pose (Q := fun u : C => zigzag South u North = zigzag South u u).
    pose (rot := fun u (h : Q u) => join_diamond_rotate h).
    assert (E : forall (b : Sphere 0) (q : North = South :> C),
      q = merid b -> apD diamond_susp q = diamond_twist q).
    { intro b; snapply paths_ind_r.
      exact (Susp_ind_beta_merid _ _ _ _ b). }
    unfold Rotation.
    lhs napply (transport_paths_FlFr_D (merid a) _).
    lhs napply concat_pp_p.
    apply moveR_Vp; symmetry.
    lhs napply (apD_composeD rotation_map
      (fun u : C => diamond_susp (conj u)) (merid a) @@ 1).
    lhs napply (ap (ap01D1 rotation_map (merid a))
      (apD_compose conj diamond_susp (merid a)) @@ 1).
    lhs napply (ap (ap01D1 rotation_map (merid a))
      (1 @@ E (negate_s0 a) (ap conj (merid a))
        (functor_susp_beta_merid negate_s0 a)) @@ 1).
    rhs napply (1 @@ apD_composeD rot diamond_susp (merid a)).
    rhs napply (1 @@ ap (ap01D1 rot (merid a))
      (apD_compose idmap diamond_susp (merid a))).
    rhs napply (1 @@ ap (ap01D1 rot (merid a))
      (1 @@ E a (ap idmap (merid a)) (ap_idmap _))).
    exact (join_zigzag_filler_rotate_twist (merid a) conj idmap
      L R rot_p rot_q rot_r rot_s 1 (rot_p_south @ rot_q_south^)).
Defined.
End Circle.
End S7RightRight.
