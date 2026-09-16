From HoTT Require Import Basics.
Require Import Types.Paths Types.Prod Types.Universe.
Require Import Classes.interfaces.abstract_algebra.
Require Import Pointed.Core Spaces.Spheres Truncations.Connectedness.
Require Import Homotopy.HSpace.Core Homotopy.HSpaceS1 Homotopy.HSpaceS3.
Require Import Homotopy.CayleyDickson Homotopy.Suspension.
Require Import Homotopy.Join.Core Homotopy.Join.SuspDiamond.
Require Import Homotopy.HSpaceS7.LeftScalar Homotopy.HSpaceS7.RightScalar.
Require Import Homotopy.HSpaceS7.Direct.RightRightScalars.
Require Import Homotopy.HSpaceS7.Direct.RightRight.

Local Set Universe Minimization ToSet.
Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.

Module S7RightRightMiddle.
Section Circle.
Context `{Univalence}.
Local Existing Instances S7LeftScalar.circle_imaginaroid
  S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative
  S7LeftScalar.circle_commutative S7LeftScalar.circle_connected
  S7LeftScalar.circle_truncated.
Local Notation C := (Sphere 1).
Local Notation J := (Join@{Set Set Set} C C).
Local Notation mu := (cd_op@{Set} (X:=psphere 1)).
Local Notation D := (cd_op_diamond@{Set} (X:=psphere 1)).
Local Notation assoc := (simple_associativity (f:=sgop_s1)).
Local Notation comm := (commutativity (f:=sgop_s1)).
Local Notation conj := (conjugate_susp (Sphere 0) negate_s0).
Local Notation neg := (negate_susp (Sphere 0) negate_s0).
Local Notation factorneg_l :=
  (@cds_factorneg_l (psphere 1) S7LeftScalar.circle_spheroid).

Let A (t b : C) := (-t) * conj b.
Let B (t a : C) := conj a * t.
Let E (t d : C) := (-d) * conj t.
Let F (t c : C) := c * t.
Let u (t a b c d : C) := cd_diamond_parameter (A t b) (B t a) c d.
Let v (t a b c d : C) := cd_diamond_parameter a b (E t d) (F t c).
Let par (t a b c d : C) : v t a b c d = conj (u t a b c d)
  := ap (cd_diamond_parameter a b (E t d)) (comm c t)
    @ S7RightRightScalars.parameter t a b c d.
Let f (t b c : C) := cd_diamond_map_l (A t b) c.
Let g (t a c : C) := cd_diamond_map_r (B t a) c.
Let f' (t a d : C) := cd_diamond_map_l a (E t d).
Let g' (t b d : C) := cd_diamond_map_r b (E t d).
Let p' (t a d : C) := cd_diamond_map_l_neg_unit a (E t d).
Let q' (t a b c d : C)
  := ap (f' t a d) (par t a b c d)^
    @ cd_diamond_map_l_parameter a b (E t d) (F t c).
Let r' (t b d : C) := cd_diamond_map_r_unit b (E t d).
Let s' (t a b c d : C)
  := ap (g' t b d) (par t a b c d)^
    @ cd_diamond_map_r_parameter a b (E t d) (F t c).

Definition e11 (t a b c d : C)
  := (cd_diamond_map_l_parameter (A t b) (B t a) c d)^
    @ (ap (f t b c) (S7RightRight.rot_p (u t a b c d)))^
    @ S7RightRightScalars.map_l t a b c d South @ p' t a d.
Definition e00 (t a b c d : C)
  := (cd_diamond_map_l_neg_unit (A t b) c)^
    @ (ap (f t b c) (S7RightRight.rot_q (u t a b c d)))^
    @ S7RightRightScalars.map_l t a b c d (conj (u t a b c d))
    @ q' t a b c d.
Definition e01 (t a b c d : C)
  := (cd_diamond_map_r_parameter (A t b) (B t a) c d)^
    @ (ap (g t a c) (S7RightRight.rot_r (u t a b c d)))^
    @ S7RightRightScalars.map_r t a b c d North @ r' t b d.
Definition e10 (t a b c d : C)
  := (cd_diamond_map_r_unit (B t a) c)^
    @ (ap (g t a c) (S7RightRight.rot_s (u t a b c d)))^
    @ S7RightRightScalars.map_r t a b c d (conj (u t a b c d))
    @ s' t a b c d.

Definition diamond_rotated (t a b c d : C)
  : transport011
      (fun x : C * C => fun y : C * C =>
        zigzag (fst x) (snd x) (fst y) = zigzag (fst x) (snd x) (snd y))
      (path_prod' (e11 t a b c d) (e00 t a b c d))
      (path_prod' (e01 t a b c d) (e10 t a b c d))
      (join_diamond_rotate (D (A t b) (B t a) c d)^)
    = (D a b (E t d) (F t c))^.
Proof.
  pose (Q := fun (x : C * C) (y : C * C) =>
    zigzag (fst x) (snd x) (fst y) = zigzag (fst x) (snd x) (snd y)).
  lhs napply (ap (transport011 Q
    (path_prod' (e11 t a b c d) (e00 t a b c d))
    (path_prod' (e01 t a b c d) (e10 t a b c d)))
    (ap join_diamond_rotate
      (cd_op_diamond_V (X:=psphere 1) (A t b) (B t a) c d))).
  rhs napply (cd_op_diamond_V (X:=psphere 1) a b (E t d) (F t c)).
  lhs napply (join_diamond_rotate_compare (f t b c) (g t a c)
    (fun z : C => (-u t a b c d) * z) (fun z : C => u t a b c d * z)
    (f' t a d) (g' t b d)
    (S7RightRightScalars.map_l (X:=psphere 1) t a b c d)
    (S7RightRightScalars.map_r (X:=psphere 1) t a b c d)
    (S7RightRight.rot_p _) (S7RightRight.rot_q _)
    (S7RightRight.rot_r _) (S7RightRight.rot_s _)
    _ _ _ _ (p' t a d) (q' t a b c d) (r' t b d) (s' t a b c d)
    (diamond_susp (u t a b c d)) (diamond_susp (conj (u t a b c d)))
    (S7RightRight.rotation _)).
  assert (R : forall (z z' : C) (e : z = z')
    (q : f' t a d z' = (-(F t c)) * conj b)
    (s : g' t b d z' = conj a * (F t c)),
    join_zigzag_filler (f' t a d) (g' t b d)
      (p' t a d) (ap (f' t a d) e @ q)
      (r' t b d) (ap (g' t b d) e @ s) (diamond_susp z)
    = join_zigzag_filler (f' t a d) (g' t b d)
      (p' t a d) q (r' t b d) s (diamond_susp z')).
  { intros z z' e q s; destruct e.
    exact (ap011 (fun q s => join_zigzag_filler (f' t a d) (g' t b d)
      (p' t a d) q (r' t b d) s (diamond_susp z))
      (concat_1p q) (concat_1p s)). }
  exact (R _ _ (par t a b c d)^ _ _).
Defined.

Let p00 (t b c : C) := cd_assoc_rl_scalar_r t c b.
Let p01 (t b d : C) := cd_assoc_rr_scalar_r t d b.
Let p10 (t a c : C)
  := assoc c (conj a) t @ (ap (.* t) (comm c (conj a))
    @ (assoc (conj a) c t)^).
Let p11 (t a d : C)
  := ap ((-d) *.) (distropp (conj a) t)
    @ (ap (fun x : C => (-d) * (conj t * x)) (cds_conjug_inv a)
      @ (assoc (-d) (conj t) a @ comm ((-d) * conj t) a)).

Local Definition factorneg_l_north_south
  : @cds_factorneg_l (psphere 1) S7LeftScalar.circle_spheroid
      North South = (merid North)^.
Proof.
  lhs_V napply (apD (@cds_factorneg_l (psphere 1)
    S7LeftScalar.circle_spheroid North)
    (merid (North : Sphere 0))).
  lhs napply (transport_paths_FlFr (f:=idmap) (g:=neg) (merid North) _).
  rewrite S7RightScalar.factorneg_l_unit, S7RightScalar.right_unit_south.
  rewrite ap_idmap, (ap_compose conj (susp_neg (Sphere 0)) (merid North)),
    functor_susp_beta_merid, Susp_rec_beta_merid.
  apply concat_pp_V.
Defined.

Local Definition map_l_south_unit
  : S7RightRightScalars.map_l (X:=psphere 1)
      North North North North North South = 1.
Proof.
  unfold S7RightRightScalars.map_l.
  change (ap neg (factorneg_l (North : C) South
      @ (factorneg_r_s1 North South)^)
    @ ((ap idmap (factorneg_l (North : C) North)^ @ (1 @ 1))
      @ (ap (.* North) (cd_diamond_map_l_parameter (X:=psphere 1)
          North North North North)
        @ (ap (.* North) (1 @ (1 @ (assoc South North North @ 1))) @ 1)))
    = 1).
  rewrite factorneg_l_north_south, S7RightScalar.factorneg_r_unit,
    S7RightScalar.factorneg_l_unit, S7RightScalar.right_unit_south,
    S7RightScalar.map_l_parameter_unit, S7RightScalar.assoc_unit.
  rewrite !concat_p1, !concat_1p, ap_idmap, !ap_V.
  rewrite (ap_compose conj (susp_neg (Sphere 0)) (merid North)),
    functor_susp_beta_merid, !Susp_rec_beta_merid, inv_V.
  rewrite !concat_p1.
  apply concat_pV.
Defined.

Local Definition rot_p_north
  : S7RightRight.rot_p North = (merid North)^.
Proof.
  change ((factorneg_r_s1 North North @ ap neg (rightidentity_s1 South)) @ 1
    = (merid North)^).
  rewrite S7RightScalar.factorneg_r_unit, S7RightScalar.right_unit_south,
    concat_1p, concat_p1.
  rewrite (ap_compose conj (susp_neg (Sphere 0)) (merid South)),
    functor_susp_beta_merid, Susp_rec_beta_merid.
  reflexivity.
Defined.

Definition standard_11 (t a b c d : C)
  : e11 t a b c d = p11 t a d.
Proof.
  revert t a b c d.
  do 5 srapply (conn_point_elim (-1) (A:=psphere 1)).
  change ((((cd_diamond_map_l_parameter (X:=psphere 1)
    North North North North)^ @ (ap neg (S7RightRight.rot_p North))^)
    @ S7RightRightScalars.map_l (X:=psphere 1)
      North North North North North South) @ 1
    = 1 @ (1 @ (assoc South North North @ 1))).
  rewrite map_l_south_unit, rot_p_north, S7RightScalar.map_l_parameter_unit,
    S7RightScalar.assoc_unit.
  rewrite ap_V, (ap_compose conj (susp_neg (Sphere 0)) (merid North)),
    functor_susp_beta_merid, Susp_rec_beta_merid, !inv_V, !concat_p1.
  apply concat_pV.
Defined.

Definition standard_01 (t a b c d : C)
  : e01 t a b c d = p01 t b d.
Proof.
  revert t a b c d.
  do 5 srapply (conn_point_elim (-1) (A:=psphere 1)).
  unfold e01, S7RightRightScalars.map_r.
  Show.
Abort.
End Circle.
End S7RightRightMiddle.
