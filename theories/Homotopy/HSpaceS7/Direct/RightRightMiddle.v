From HoTT Require Import Basics.
Require Import Types.Paths Types.Prod Types.Universe.
Require Import Classes.interfaces.abstract_algebra.
Require Import Pointed.Core Spaces.Spheres Truncations.Connectedness.
Require Import Homotopy.HSpace.Core Homotopy.HSpaceS1 Homotopy.HSpaceS3.
Require Import Homotopy.CayleyDickson Homotopy.Suspension.
Require Import Homotopy.Join.Core Homotopy.Join.SuspDiamond.
Require Import Homotopy.Join.MapCoherence.
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
(** Share the distributivity witness too: comparing it with a separately instantiated [conjugate_s1_distropp] unfolds the large circle truncation proof during elaboration. *)
Local Existing Instances S7LeftScalar.circle_imaginaroid
  S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative
  S7LeftScalar.circle_commutative S7LeftScalar.circle_distropp
  S7LeftScalar.circle_connected S7LeftScalar.circle_truncated.
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
  lhs napply ((inverse2 (ap_idmap _) @@
    (S7RightScalar.factorneg_l_unit @ S7RightScalar.right_unit_south))
    @@ negate_susp_beta_merid North).
  apply concat_pp_V.
Defined.

Local Definition p11_unit : p11 North North North = 1.
Proof.
  unfold p11.
  lhs napply (1 @@ (1 @@ (S7RightScalar.assoc_unit South @@ 1))).
  reflexivity.
Defined.

Local Definition map_l_south_unit
  : S7RightRightScalars.map_l (X:=psphere 1)
      North North North North North South = 1.
Proof.
  unfold S7RightRightScalars.map_l.
  lhs napply (ap (ap neg)
    (factorneg_l_north_south @@ inverse2
      (S7RightScalar.factorneg_r_unit South)) @@ 1).
  lhs napply (ap (ap neg) (concat_p1 _) @@ 1).
  lhs napply ((ap_V neg _
    @ inverse2 (negate_susp_beta_merid North) @ inv_V _) @@ 1).
  unfold RightRightScalars.S7RightRightScalars.map_l_linear.
  lhs napply (1 @@ ((concat_p1 _ @ ap_idmap _
    @ inverse2 (S7RightScalar.factorneg_l_unit
      @ S7RightScalar.right_unit_south)) @@ 1)).
  lhs napply (1 @@ (1 @@
    ((ap (ap (fun x : C => x * North)) S7RightScalar.map_l_parameter_unit
      @ ap_V _ _ @ inverse2 (Susp_rec_beta_merid South)) @@ 1))).
  lhs napply (1 @@ (1 @@ (1 @@
    (ap (ap (fun x : C => x * North)) p11_unit @@ 1)))).
  lhs napply (1 @@ concat_p1 _).
  apply concat_pV.
Defined.

(** The unit map comparison is a family of loops in the circle. Its equality to the constant family is a proposition, so the South computation determines the whole family. *)
Local Definition map_l_unit (z : C)
  : S7RightRightScalars.map_l (X:=psphere 1)
      North North North North North z = 1.
Proof.
  revert z; srapply (conn_point_elim (-1) (A:=Build_pType C South)).
  exact map_l_south_unit.
Defined.

Local Definition map_r_north_unit
  : S7RightRightScalars.map_r (X:=psphere 1)
      North North North North North North = p01 North North North.
Proof.
  unfold S7RightRightScalars.map_r,
    RightRightScalars.S7RightRightScalars.map_r_linear.
  do 2 (lhs napply concat_1p).
  lhs napply concat_p1.
  lhs napply (ap_homotopic_id rightidentity_s1).
  exact (concat_p1 _ @ concat_1p _).
Defined.

Local Definition rot_p_north
  : S7RightRight.rot_p North = (merid North)^.
Proof.
  unfold S7RightRight.rot_p.
  lhs napply ((S7RightScalar.factorneg_r_unit North
    @@ ap (ap neg) S7RightScalar.right_unit_south) @@ 1).
  lhs napply (concat_1p _ @@ 1).
  lhs napply concat_p1.
  exact (negate_susp_beta_merid South).
Defined.

Definition standard_11 (t a b c d : C)
  : e11 t a b c d = p11 t a d.
Proof.
  revert t a b c d.
  do 5 srapply (conn_point_elim (-1) (A:=psphere 1)).
  unfold e11.
  lhs napply (((inverse2 S7RightScalar.map_l_parameter_unit
    @@ inverse2 (ap (ap neg) rot_p_north)) @@ map_l_unit South) @@ 1).
  lhs napply (((inv_V _ @@ inverse2
    (ap_V neg _ @ inverse2 (negate_susp_beta_merid North) @ inv_V _))
    @@ 1) @@ 1).
  do 2 (lhs napply concat_p1).
  exact (concat_pV _ @ p11_unit^).
Defined.

Definition standard_01 (t a b c d : C)
  : e01 t a b c d = p01 t b d.
Proof.
  revert t a b c d.
  do 5 srapply (conn_point_elim (-1) (A:=psphere 1)).
  unfold e01.
  lhs napply concat_p1.
  lhs napply concat_1p.
  exact map_r_north_unit.
Defined.
Local Opaque cds_factorneg_l.
Let rt (x : C) := x * North.
Let ell := merid (North : Sphere 0) @ (merid South)^.

Local Definition p01_unit : p01 North North North = ell.
Proof.
  unfold p01, cd_assoc_rr_scalar_r.
  pose (q := factorneg_l (North : C) North).
  pose (bq := S7RightScalar.factorneg_l_unit @ S7RightScalar.right_unit_south).
  pose (brq := ap (ap rt) bq @ Susp_rec_beta_merid South).
  lhs napply (1 @@ (1 @@ (1 @@
    (ap (ap rt) (S7RightScalar.factorneg_r_unit North) @@ 1)))).
  do 3 (lhs napply (1 @@ concat_1p _)).
  lhs napply (1 @@ (1 @@ (concat_1p _ @@ 1))).
  lhs napply (1 @@ (1 @@ (1 @@ (ap_V rt q @ inverse2 brq)))).
  lhs napply (1 @@ (1 @@ concat_p1 _)).
  lhs napply (1 @@ concat_pV q).
  lhs napply concat_p1.
  lhs napply (ap (ap rt) (S7RightScalar.distropp_unit South
    @ ap (ap conj) S7RightScalar.right_unit_south
    @ functor_susp_beta_merid negate_s0 South)).
  exact (Susp_rec_beta_merid North).
Defined.

Local Definition parameter_unit : par North North North North North = ell.
Proof.
  unfold par, S7RightRightScalars.parameter.
  lhs napply concat_1p.
  lhs napply concat_p1.
  pose (q := factorneg_l (North : C) North).
  pose (bq := S7RightScalar.factorneg_l_unit @ S7RightScalar.right_unit_south).
  pose (brq := ap (ap rt) bq @ Susp_rec_beta_merid South).
  lhs napply (ap (ap (fun z : C => rt (rt (rt z))))
    (concat_p1 _ @ S7RightScalar.distropp_unit South
      @ ap (ap conj) S7RightScalar.right_unit_south
      @ functor_susp_beta_merid negate_s0 South) @@ 1).
  lhs napply ((ap_compose rt (fun z : C => rt (rt z)) (merid North)
    @ ap (ap (fun z : C => rt (rt z))) (Susp_rec_beta_merid North)
    @ ap_homotopic_id (fun z => rightidentity_s1 (rt z) @ rightidentity_s1 z) ell
    @ concat_p1 _ @ concat_1p _) @@ 1).
  lhs napply (1 @@ (ap (ap (fun z : C => rt (rt (rt z))))
    (S7RightScalar.factorneg_r_unit North) @@ 1)).
  lhs napply (1 @@ concat_1p _).
  lhs napply (1 @@ ((ap (ap (fun z : C => rt (rt z))) bq
    @ ap_compose rt rt (merid South)
    @ ap (ap rt) (Susp_rec_beta_merid South)) @@ 1)).
  lhs napply (1 @@ concat_1p _).
  lhs napply (1 @@ (brq @@ 1)).
  lhs napply (1 @@ concat_1p _).
  rhs_V napply concat_p1.
  napply whiskerL.
  lhs napply (1 @@ ((((1 @@ inverse2 (S7RightScalar.factorneg_r_unit North))
    @@ inverse2 (ap (ap idmap) (S7RightScalar.factorneg_r_unit North)))
    @@ inverse2 (ap_idmap q)) @@ inverse2 brq)).
  lhs napply (1 @@ (concat_p1 _ @ concat_1p _)).
  apply concat_pV.
Defined.
Local Definition rot_q_north : S7RightRight.rot_q North = merid South.
Proof.
  unfold S7RightRight.rot_q.
  lhs napply concat_p1.
  exact (S7RightScalar.factorneg_l_unit @ S7RightScalar.right_unit_south).
Defined.

Definition standard_10 (t a b c d : C)
  : e10 t a b c d = p10 t a c.
Proof.
  revert t a b c d.
  do 5 srapply (conn_point_elim (-1) (A:=psphere 1)).
  unfold e10.
  lhs napply (concat_1p _ @@ 1).
  lhs napply ((map_r_north_unit @ p01_unit) @@ 1).
  lhs napply (1 @@ (ap (ap rt) (inverse2 parameter_unit) @@ 1)).
  lhs napply (1 @@ (ap_V rt ell @@ 1)).
  lhs napply (1 @@ (inverse2 (ap_homotopic_id rightidentity_s1 ell
    @ concat_p1 _ @ concat_1p _) @@ 1)).
  lhs napply (1 @@ concat_p1 _).
  apply concat_pV.
Defined.

Definition standard_00 (t a b c d : C)
  : e00 t a b c d = p00 t b c.
Proof.
  revert t a b c d.
  do 5 srapply (conn_point_elim (-1) (A:=psphere 1)).
  unfold e00.
  lhs napply ((concat_1p _ @@ 1) @@ 1).
  lhs napply ((inverse2 (ap (ap neg) rot_q_north
    @ negate_susp_beta_merid South) @@ map_l_unit North) @@ 1).
  lhs napply ((inv_V _ @@ 1) @@ 1).
  lhs napply (concat_p1 _ @@ 1).
  lhs napply (1 @@ (ap (ap neg) (inverse2 parameter_unit)
    @@ S7RightScalar.map_l_parameter_unit)).
  lhs napply (1 @@ (ap_V neg ell @@ 1)).
  lhs napply (1 @@ (inverse2 (ap_pV neg (merid North) (merid South)
    @ (negate_susp_beta_merid North
      @@ inverse2 (negate_susp_beta_merid South))) @@ 1)).
  lhs napply (1 @@ (inverse2 (1 @@ inv_V _) @@ 1)).
  lhs napply (1 @@ (inv_pp _ _ @@ 1)).
  lhs napply (1 @@ ((1 @@ inv_V _) @@ 1)).
  lhs napply (1 @@ concat_pp_p _ _ _).
  lhs napply (1 @@ (1 @@ concat_pV _)).
  lhs napply (1 @@ concat_p1 _).
  lhs napply concat_pV.
  unfold p00, cd_assoc_rl_scalar_r.
  symmetry.
  lhs napply (ap (ap rt) (S7RightScalar.factorneg_l_unit
    @ S7RightScalar.right_unit_south) @@ 1).
  lhs napply (Susp_rec_beta_merid South @@ 1).
  lhs napply concat_1p.
  lhs napply (concat_p1 _ @@ 1).
  apply concat_pV.
Defined.

Local Opaque cd_diamond cd_op_diamond.
Local Notation first_lr := (@cd_assoc_first_lr@{Set} (psphere 1)
  S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative cd_diamond_susp
  S7LeftScalar.circle_commutative).
Local Notation first_rr := (@cd_assoc_first_rr@{Set} (psphere 1)
  S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative cd_diamond_susp
  S7LeftScalar.circle_commutative).
Local Notation rl := (@cd_assoc_rl@{Set} (psphere 1)
  S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative cd_diamond_susp
  S7LeftScalar.circle_commutative).
Local Notation rr := (@cd_assoc_rr@{Set} (psphere 1)
  S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative cd_diamond_susp
  S7LeftScalar.circle_commutative).

Definition diamond_standard (t a b c d : C)
  : transport011
      (fun x : C * C => fun y : C * C =>
        zigzag (fst x) (snd x) (fst y) = zigzag (fst x) (snd x) (snd y))
      (path_prod' (p11 t a d) (p00 t b c))
      (path_prod' (p01 t b d) (p10 t a c))
      (join_diamond_rotate (D (A t b) (B t a) c d)^)
    = (D a b (E t d) (F t c))^.
Proof.
  lhs_V napply (ap011 (fun p q => transport011 _ p q
    (join_diamond_rotate (D (A t b) (B t a) c d)^))
    (ap011 path_prod' (standard_11 t a b c d) (standard_00 t a b c d))
    (ap011 path_prod' (standard_01 t a b c d) (standard_10 t a b c d))).
  exact (diamond_rotated t a b c d).
Defined.

(** The mixed comparison uses the original right-middle scalar associators on both last-input constructors. *)
Definition middle_r_glue_glue (t a b c d : C)
  : transport
      (fun z => ap (fun x => mu (mu x (joinr t)) z) (jglue a b)
          @ first_rr b t z
        = first_lr a t z
          @ ap (fun x => mu x (mu (joinr t) z)) (jglue a b))
      (jglue c d) (concat_Ap (rl t c) (jglue a b))
    = concat_Ap (rr t d) (jglue a b).
Proof.
  pose (R := fun x => mu x (joinr t)).
  pose (L := mu (joinr t)).
  pose (W := fun a b z => ap (fun x => mu x z) (jglue a b)).
  pose (U := fun z => ap (fun x => mu (R x) z) (jglue a b)).
  pose (V := fun z => ap (fun x => mu x (L z)) (jglue a b)).
  pose (bh0 := fun a c d : C =>
    (Join_rec_beta_jglue (P:=J) _ _
      (fun c d => jglue (a * c) (conj a * d)) c d
      : ap (mu (joinl a)) (jglue c d) = jglue (a * c) (conj a * d))).
  pose (bh1 := fun b c d : C =>
    (Join_rec_beta_jglue (P:=J) _ _
      (fun c d : C => (jglue (sgop_s1 (neg d) (conj b)) (sgop_s1 c b))^) c d
      : ap (mu (joinr b)) (jglue c d)
        = (jglue (sgop_s1 (neg d) (conj b)) (sgop_s1 c b))^)).
  pose (bv0 := fun a b c : C => Join_rec_beta_jglue _ _
    (fun a b => jglue (a * c) (c * b)) a b).
  pose (bv1 := fun a b d : C => Join_rec_beta_jglue _ _
    (fun a b => (jglue ((-d) * conj b) (conj a * d))^) a b).
  pose (tF := fun z => (ap_compose R (fun x => mu x z) (jglue a b)
    @ ap (ap (fun x => mu x z)) (bv1 a b t))
    @ ap_V (fun x => mu x z) (jglue (A t b) (B t a))).
  pose (bfh0 := bh1 (B t a) c d).
  pose (bfh1 := bh0 (A t b) c d).
  pose (bfv0 := tF (joinl c) @ inverse2 (bv0 (A t b) (B t a) c)).
  pose (bfv1 := tF (joinr d) @ (inverse2 (bv1 (A t b) (B t a) d)
    @ inv_V (jglue ((-d) * conj (B t a)) (conj (A t b) * d)))).
  pose (bgh0 := (ap_compose L (mu (joinl a)) (jglue c d)
    @ ap (ap (mu (joinl a))) (bh1 t c d))
    @ (ap_V (mu (joinl a)) (jglue (E t d) (F t c))
      @ inverse2 (bh0 a (E t d) (F t c)))).
  pose (bgh1 := (ap_compose L (mu (joinr b)) (jglue c d)
    @ ap (ap (mu (joinr b))) (bh1 t c d))
    @ (ap_V (mu (joinr b)) (jglue (E t d) (F t c))
      @ (inverse2 (bh1 b (E t d) (F t c))
        @ inv_V (jglue ((-(F t c)) * conj b) (E t d * b))))).
  pose (bgv0 := bv1 a b (F t c)).
  pose (bgv1 := bv0 a b (E t d)).
  pose (cf := (1 @@ inv_V (jglue ((-d) * conj (B t a)) (conj (A t b) * d)))^
    @ (inverse_natural (jglue (A t b * c) (conj (A t b) * d))
      (jglue ((-d) * conj (B t a)) (c * B t a))^ (D (A t b) (B t a) c d))^).
  pose (cg := inverse_natural (jglue (a * E t d) (E t d * b))
      (jglue ((-(F t c)) * conj b) (conj a * F t c))^ (D a b (E t d) (F t c))^
    @ (1 @@ inv_V (jglue ((-(F t c)) * conj b) (E t d * b)))).
  assert (BM : forall a b c d,
    concat_Ap (W a b) (jglue c d) @ (bv0 a b c @@ 1)
      = (1 @@ bv1 a b d) @ naturality_change
        (bh0 a c d) (bh1 b c d) (D a b c d)).
  { intros a0 b0 c0 d0.
    refine (Join_rec2_beta_jglue_jglue J
      _ _ _ _ _ _ _ _ D a0 b0 c0 d0 @ _).
    exact (1 @@ concat_p_pp _ _ _). }
  assert (BF : concat_Ap U (jglue c d) @ (bfv0 @@ 1)
    = (1 @@ bfv1) @ naturality_change bfh0 bfh1 cf).
  { napply (mixed_beta_vertical (tF (joinl c)) (tF (joinr d))
      (inverse2 (bv0 (A t b) (B t a) c))
      (inverse2 (bv1 (A t b) (B t a) d)
        @ inv_V (jglue ((-d) * conj (B t a)) (conj (A t b) * d)))
      _ _ _ (concat_Ap (fun z => (W (A t b) (B t a) z)^) (jglue c d)) _).
    - exact (concat_Ap_homotopic U (fun z => (W (A t b) (B t a) z)^)
        tF (jglue c d)).
    - lhs napply (concat_Ap_inverse (W (A t b) (B t a)) (jglue c d) @@ 1).
      exact (inverse_mixed_beta (bh0 (A t b) c d) (bv1 (A t b) (B t a) d)
        (bv0 (A t b) (B t a) c) (bh1 (B t a) c d) _ _
        (BM (A t b) (B t a) c d)). }
  assert (BG : concat_Ap V (jglue c d) @ (bgv0 @@ 1)
    = (1 @@ bgv1) @ naturality_change bgh0 bgh1 cg).
  { napply (concat_Ap_precompose_beta (W a b) L (jglue c d)
      (jglue (E t d) (F t c))^ (bh1 t c d)
      (ap_V (mu (joinl a)) (jglue (E t d) (F t c))
        @ inverse2 (bh0 a (E t d) (F t c)))
      bgv1 bgv0
      (ap_V (mu (joinr b)) (jglue (E t d) (F t c))
        @ (inverse2 (bh1 b (E t d) (F t c))
          @ inv_V (jglue ((-(F t c)) * conj b) (E t d * b)))) cg).
    lhs napply (concat_Ap_V (W a b) (jglue (E t d) (F t c)) @@ 1).
    napply (mixed_beta_horizontal
      (ap_V (mu (joinl a)) (jglue (E t d) (F t c)))
      (ap_V (mu (joinr b)) (jglue (E t d) (F t c)))
      (inverse2 (bh0 a (E t d) (F t c)))
      (inverse2 (bh1 b (E t d) (F t c))
        @ inv_V (jglue ((-(F t c)) * conj b) (E t d * b)))
      bgv0 bgv1 _ cg).
    exact (inverse_horizontal_mixed_beta (bh0 a (E t d) (F t c))
      (bv1 a b (F t c)) (bv0 a b (E t d)) (bh1 b (E t d) (F t c))
      _ _ (BM a b (E t d) (F t c))). }
  pose (eh0 := inverse_natural _ _ (join_natsq (p11 t a d) (p10 t a c))).
  pose (eh1 := (join_natsq (p00 t b c) (p01 t b d))^).
  pose (ev0 := inverse_natural _ _ (join_natsq (p00 t b c) (p10 t a c))).
  pose (ev1 := (join_natsq (p11 t a d) (p01 t b d))^).
  assert (EH0 : concat_Ap (first_lr a t) (jglue c d)
    = naturality_change bfh0 bgh0 eh0).
  { lhs napply (Join_ind_FlFr_beta_jglue _ _ _ _ _ c d).
    rhs napply concat_pp_p.
    napply (ap (fun q => (bfh0 @@ 1) @ q)).
    do 3 (lhs napply naturality_suffix).
    napply (ap (fun q => eh0 @ (1 @@ q)^)).
    apply concat_pp_p. }
  assert (EH1 : concat_Ap (first_rr b t) (jglue c d)
    = naturality_change bfh1 bgh1 eh1).
  { lhs napply (Join_ind_FlFr_beta_jglue _ _ _ _ _ c d).
    rhs napply concat_pp_p.
    napply (ap (fun q => (bfh1 @@ 1) @ q)).
    do 4 (lhs napply naturality_suffix).
    napply (ap (fun q => eh1 @ (1 @@ q)^)).
    lhs napply concat_pp_p.
    apply concat_pp_p. }
  assert (EV0 : concat_Ap (rl t c) (jglue a b)
    = naturality_change bfv0 bgv0 ev0).
  { lhs napply (Join_ind_FFlFr_beta_jglue R
      (fun x => mu x (joinl c)) (fun x => mu x (joinr (F t c)))
      _ _ _ a b).
    do 3 (lhs napply naturality_prefix).
    lhs napply (1 @@ (inverse_natural_moves _ _ _ @@ 1)).
    exact (concat_p_pp (bfv0 @@ 1) ev0 (1 @@ bgv0)^). }
  assert (EV1 : concat_Ap (rr t d) (jglue a b)
    = naturality_change bfv1 bgv1 ev1).
  { lhs napply (Join_ind_FFlFr_beta_jglue R
      (fun x => mu x (joinr d)) (fun x => mu x (joinl (E t d)))
      _ _ _ a b).
    do 2 (lhs napply naturality_prefix).
    lhs napply (1 @@ naturality_prefix _ _ _ _).
    lhs napply naturality_prefix.
    exact (concat_p_pp (bfv1 @@ 1) ev1 (1 @@ bgv1)^). }
  refine (ap (transport _ (jglue c d)) EV0 @ _ @ EV1^).
  napply (transport_naturality_square_beta U V
    (first_lr a t) (first_rr b t) (jglue c d)
    bfh0 bfh1 bfv0 bfv1 bgh0 bgh1 bgv0 bgv1
    cf cg eh0 eh1 ev0 ev1 BF BG EH0 EH1).
  exact (join_zigzag_filler_cube_rotate (p11 t a d) (p00 t b c)
    (p01 t b d) (p10 t a c) _ _ (diamond_standard t a b c d)).
Defined.

Definition middle_r_glue (t a b : C)
  : forall z : J,
    ap (fun x => mu (mu x (joinr t)) z) (jglue a b) @ first_rr b t z
    = first_lr a t z @ ap (fun x => mu x (mu (joinr t) z)) (jglue a b).
Proof.
  snapply Join_ind.
  - intro c; exact (concat_Ap (rl t c) (jglue a b)).
  - intro d; exact (concat_Ap (rr t d) (jglue a b)).
  - exact (middle_r_glue_glue t a b).
Defined.

Definition middle_r (t : C) (x z : J)
  : mu (mu x (joinr t)) z = mu x (mu (joinr t) z).
Proof.
  revert x; snapply Join_ind_FlFr.
  - exact (fun a => first_lr a t z).
  - exact (fun b => first_rr b t z).
  - exact (fun a b => middle_r_glue t a b z).
Defined.

(** Both column comparisons compute to reflexivity on the first-input constructors. *)
Definition middle_r_joinl (t c : C) (x : J)
  : middle_r t x (joinl c) = rl t c x.
Proof.
  revert x; snapply Join_ind.
  - reflexivity.
  - reflexivity.
  - intros a b.
    nrefine (equiv_naturality_transport2
      (fun x => middle_r t x (joinl c)) (rl t c) (jglue a b) 1 1 _).
    lhs napply concat_p1.
    rhs napply concat_1p.
    exact (Join_ind_FlFr_beta_jglue _ _ _ _ _ a b).
Defined.

Definition middle_r_joinr (t d : C) (x : J)
  : middle_r t x (joinr d) = rr t d x.
Proof.
  revert x; snapply Join_ind.
  - reflexivity.
  - reflexivity.
  - intros a b.
    nrefine (equiv_naturality_transport2
      (fun x => middle_r t x (joinr d)) (rr t d) (jglue a b) 1 1 _).
    lhs napply concat_p1.
    rhs napply concat_1p.
    exact (Join_ind_FlFr_beta_jglue _ _ _ _ _ a b).
Defined.

Local Notation AL := (@cd_assoc_last_joinl@{Set} (psphere 1)
  S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative cd_diamond_susp
  S7LeftScalar.circle_commutative S7LeftScalar.circle_connected
  S7LeftScalar.circle_truncated).
Local Notation qlr := (@cd_assoc_last_joinl_first_lr@{Set} (psphere 1)
  S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative cd_diamond_susp
  S7LeftScalar.circle_commutative S7LeftScalar.circle_connected
  S7LeftScalar.circle_truncated).
Local Notation qrr := (@cd_assoc_last_joinl_first_rr@{Set} (psphere 1)
  S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative cd_diamond_susp
  S7LeftScalar.circle_commutative S7LeftScalar.circle_connected
  S7LeftScalar.circle_truncated).

(** The last-left overlap retains the two original triangle comparisons. *)
Definition overlap_glue (t a b c : C)
  : concat_Ap (fun x => AL x (joinr t) c) (jglue a b)
      @ (qlr a t c @@ 1)
    = (1 @@ qrr b t c) @ concat_Ap (rl t c) (jglue a b).
Proof.
  exact (JoinMapCoherence.translated_turn_parameter_comparison
    (North : C) sgop_s1 (fun a d => sgop_s1 (conj a) d)
    (fun b c => sgop_s1 c b) (fun b d => sgop_s1 (neg d) (conj b)) D
    t (fun x => sgop_s1 x c) (sgop_s1 c) (fun x => sgop_s1 x c) (comm c)
    (fun b => cd_diamond_translate_l_parameter (X:=psphere 1) North b North t c)
    (fun a => cd_diamond_translate_r_parameter (X:=psphere 1) a North North t c)
    (fun a => p10 t a c) (fun b => p00 t b c)
    (fun a => S7LeftScalar.overlap_scalar_r a t c)
    (fun b => S7RightScalar.overlap_scalar_r b t c) a b).
Defined.

Definition overlap (t : C) (x : J) (c : C)
  : AL x (joinr t) c = middle_r t x (joinl c).
Proof.
  revert x; snapply Join_ind.
  - exact (fun a => qlr a t c).
  - exact (fun b => qrr b t c).
  - intros a b.
    nrefine (equiv_naturality_transport2
      (fun x => AL x (joinr t) c) (fun x => middle_r t x (joinl c))
      (jglue a b) _ _ _).
    rhs napply (1 @@ Join_ind_FlFr_beta_jglue _ _ _ _ _ a b).
    exact (overlap_glue t a b c).
Defined.
End Circle.
End S7RightRightMiddle.
