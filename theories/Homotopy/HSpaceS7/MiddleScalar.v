From HoTT Require Import Basics.
Require Import Types.Paths Types.Prod Types.Universe.
Require Import Classes.interfaces.abstract_algebra.
Require Import Pointed.Core Spaces.Spheres Truncations.Connectedness.
Require Import Homotopy.HSpace.Core Homotopy.HSpaceS1.
Require Import Homotopy.CayleyDickson Homotopy.Suspension Homotopy.Join.Core.
Require Import Homotopy.Join.MapCoherence Homotopy.NullHomotopy.
Require Import Homotopy.HSpaceS7.LeftScalar Homotopy.HSpaceS7.Balanced.

Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.

(** * Middle scalar associativity with the original corner witnesses *)

Module S7MiddleScalar.
Local Set Universe Minimization ToSet.
Local Existing Instances S7LeftScalar.circle_imaginaroid
  S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative
  S7LeftScalar.circle_commutative S7LeftScalar.circle_distropp
  S7LeftScalar.circle_connected S7LeftScalar.circle_truncated.
Local Notation C := (Sphere 1).
Local Notation J := (Join@{Set Set Set} C C).
Local Notation assoc := (simple_associativity (f:=sgop_s1)).
Local Notation comm := (commutativity (f:=sgop_s1)).

(** Use the unmodified right translation, whose right label is [s * b], rather than replacing it by [b * s]. *)
Definition parameter `{Univalence} (s a b c d : C)
  : cd_diamond_parameter (X:=psphere 1) (a * s) (s * b) c d
    = cd_diamond_parameter a b (s * c) (conj s * d)
  := ap (fun t => cd_diamond_parameter (a * s) t c d) (comm s b)
    @ cd_diamond_parameter_balanced s a b c d.

Definition map_r `{Univalence} (s b c : C)
  : cd_diamond_map_r (X:=psphere 1) (s * b) c
    == cd_diamond_map_r b (s * c)
  := fun t => ap (fun b => cd_diamond_map_r b c t) (comm s b)
    @ cd_diamond_map_r_balanced s b c t.

Local Definition p00 `{Univalence} (s a c : C) := (assoc a s c)^.
Local Definition p01 `{Univalence} (s a d : C)
  := ap (.* d) (distropp a s)
    @ (ap (.* d) (comm (conj s) (conj a))
      @ (assoc (conj a) (conj s) d)^).
Local Definition p10 `{Univalence} (s b c : C)
  := assoc c s b @ ap (.* b) (comm c s).
Local Definition p11 `{Univalence} (s b d : C)
  := (factorneg_l d (conj (s * b))
    @ ap (-) (ap (d *.) (distropp s b)
      @ (ap (d *.) (comm (conj b) (conj s))
        @ (assoc d (conj s) (conj b)
          @ ap (.* conj b) (comm d (conj s))))))
    @ (factorneg_l (conj s * d) (conj b))^.

Local Notation e00 := (cd_balanced_00 (X:=psphere 1)).
Local Definition e01 `{Univalence} (s a b c d : C)
  := (cd_diamond_map_r_parameter (X:=psphere 1) (a * s) (s * b) c d)^
    @ (map_r s b c (cd_diamond_parameter (a * s) (s * b) c d)
      @ ap (cd_diamond_map_r b (s * c)) (parameter s a b c d))
    @ cd_diamond_map_r_parameter a b (s * c) (conj s * d).
Local Definition e10 `{Univalence} (s b c : C)
  := (cd_diamond_map_r_unit (X:=psphere 1) (s * b) c)^
    @ map_r s b c North @ cd_diamond_map_r_unit b (s * c).
Local Definition e11 `{Univalence} (s a b c d : C)
  := (cd_diamond_map_l_parameter (X:=psphere 1) (a * s) (s * b) c d)^
    @ (cd_diamond_map_l_balanced s a c
        (cd_diamond_parameter (a * s) (s * b) c d)
      @ ap (cd_diamond_map_l a (s * c)) (parameter s a b c d))
    @ cd_diamond_map_l_parameter a b (s * c) (conj s * d).

Definition standard_00 `{Univalence} (s a c : C)
  : e00 s a c = p00 s a c.
Proof.
  revert s a c.
  do 3 srapply (conn_point_elim (-1) (A:=psphere 1)).
  reflexivity.
Defined.

Definition standard_01 `{Univalence} (s a b c d : C)
  : e01 s a b c d = p01 s a d.
Proof.
  revert s a b c d.
  do 5 srapply (conn_point_elim (-1) (A:=psphere 1)).
  reflexivity.
Defined.

Definition standard_10 `{Univalence} (s b c : C)
  : e10 s b c = p10 s b c.
Proof.
  revert s b c.
  do 3 srapply (conn_point_elim (-1) (A:=psphere 1)).
  reflexivity.
Defined.

Definition standard_11 `{Univalence} (s a b c d : C)
  : e11 s a b c d = p11 s b d.
Proof.
  revert s a b c d.
  do 5 srapply (conn_point_elim (-1) (A:=psphere 1)).
  pose (q := cd_diamond_map_l_parameter (X:=psphere 1)
    North North North North).
  change ((q^ @ (1 @ 1)) @ q = p11 North North North).
  lhs napply (concat_p1 q^ @@ 1).
  lhs napply concat_Vp.
  unfold p11.
  rhs napply (concat_p1 _ @@ 1).
  symmetry; apply concat_pV.
Defined.

Local Opaque cd_diamond cd_op_diamond.
Local Notation mu :=
  (fun D0 => @cd_op@{Set} (psphere 1)
    S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative D0).
Local Notation D :=
  (fun D0 => @cd_op_diamond@{Set} (psphere 1)
    S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative D0).
Local Notation first_ll :=
  (fun D0 => @cd_assoc_first_ll@{Set} (psphere 1)
    S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative D0
    S7LeftScalar.circle_commutative).
Local Notation first_rl :=
  (fun D0 => @cd_assoc_first_rl@{Set} (psphere 1)
    S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative D0
    S7LeftScalar.circle_commutative).

Definition diamond `{Univalence}
  `(D0 : CayleyDicksonDiamond (psphere 1) (-)) (s a b c d : C)
  : transport011
      (fun x : C * C => fun y : C * C =>
        zigzag (fst x) (snd x) (fst y)
          = zigzag (fst x) (snd x) (snd y))
      (path_prod' (p00 s a c) (p11 s b d))
      (path_prod' (p01 s a d) (p10 s b c))
      (cd_op_diamond (a * s) (s * b) c d)
    = cd_op_diamond a b (s * c) (conj s * d).
Proof.
  lhs_V napply (ap011 (fun p q => transport011 _ p q
    (cd_op_diamond (X:=psphere 1) (a * s) (s * b) c d))
    (ap011 path_prod' (standard_00 s a c) (standard_11 s a b c d))
    (ap011 path_prod' (standard_01 s a b c d) (standard_10 s b c))).
  exact (join_zigzag_filler_change (fun t => (cd_diamond t)^)
    (cd_diamond_map_l_balanced s a c) (map_r s b c)
    (parameter s a b c d) _ _ _ _ _ _ _ _).
Defined.

Local Opaque associative_sgop_s1 commutative_sgop_s1 cds_factorneg_l.

(** The two vertical faces retain the old scalar associativity paths. *)
Definition middle_l_glue_l `{Univalence}
  `(D0 : CayleyDicksonDiamond (psphere 1) (-)) (s a b c : C)
  : ap (fun x => mu D0 (mu D0 x (joinl s)) (joinl c)) (jglue a b)
      @ first_rl D0 b s (joinl c)
    = first_ll D0 a s (joinl c)
      @ ap (fun x => mu D0 x (mu D0 (joinl s) (joinl c))) (jglue a b).
Proof.
  lhs napply (ap_compose (fun x => mu D0 x (joinl s))
    (fun x => mu D0 x (joinl c)) (jglue a b) @@ 1).
  lhs napply (ap (ap (fun x => mu D0 x (joinl c)))
    (Join_rec_beta_jglue _ _ (fun a b => jglue (a * s) (s * b)) a b) @@ 1).
  lhs napply (Join_rec_beta_jglue _ _
    (fun a b => jglue (a * c) (c * b)) (a * s) (s * b) @@ 1).
  rhs napply (1 @@ Join_rec_beta_jglue _ _
    (fun a b => jglue (a * (s * c)) ((s * c) * b)) a b).
  exact (join_natsq (p00 s a c) (p10 s b c))^.
Defined.

Definition middle_l_glue_r `{Univalence}
  `(D0 : CayleyDicksonDiamond (psphere 1) (-)) (s a b d : C)
  : ap (fun x => mu D0 (mu D0 x (joinl s)) (joinr d)) (jglue a b)
      @ first_rl D0 b s (joinr d)
    = first_ll D0 a s (joinr d)
      @ ap (fun x => mu D0 x (mu D0 (joinl s) (joinr d))) (jglue a b).
Proof.
  lhs napply (ap_compose (fun x => mu D0 x (joinl s))
    (fun x => mu D0 x (joinr d)) (jglue a b) @@ 1).
  lhs napply (ap (ap (fun x => mu D0 x (joinr d)))
    (Join_rec_beta_jglue _ _ (fun a b => jglue (a * s) (s * b)) a b) @@ 1).
  lhs napply (Join_rec_beta_jglue _ _
    (fun a b => (jglue ((-d) * conj b) (conj a * d))^)
    (a * s) (s * b) @@ 1).
  rhs napply (1 @@ Join_rec_beta_jglue _ _
    (fun a b => (jglue ((-(conj s * d)) * conj b)
      (conj a * (conj s * d)))^) a b).
  exact (inverse_natural _ _ (join_natsq (p11 s b d) (p01 s a d))).
Defined.

(** The mixed comparison is the balanced diamond, converted using the specified computations of all four sides. *)
Definition middle_l_glue_glue `{Univalence}
  `(D0 : CayleyDicksonDiamond (psphere 1) (-)) (s a b c d : C)
  : transport
      (fun z => ap (fun x => mu D0 (mu D0 x (joinl s)) z) (jglue a b)
          @ first_rl D0 b s z
        = first_ll D0 a s z
          @ ap (fun x => mu D0 x (mu D0 (joinl s) z)) (jglue a b))
      (jglue c d) (middle_l_glue_l D0 s a b c)
    = middle_l_glue_r D0 s a b d.
Proof.
  pose (R := fun x => mu D0 x (joinl s)).
  pose (L := mu D0 (joinl s)).
  pose (W := fun a b z => ap (fun x => mu D0 x z) (jglue a b)).
  pose (U := fun z => ap (fun x => mu D0 (R x) z) (jglue a b)).
  pose (V := fun z => ap (fun x => mu D0 x (L z)) (jglue a b)).
  pose (bh0 := fun a c d => Join_rec_beta_jglue _ _
    (fun c d => jglue (a * c) (conj a * d)) c d).
  pose (bh1 := fun b c d => Join_rec_beta_jglue _ _
    (fun c d => (jglue ((-d) * conj b) (c * b))^) c d).
  pose (bv0 := fun a b c => Join_rec_beta_jglue _ _
    (fun a b => jglue (a * c) (c * b)) a b).
  pose (bv1 := fun a b d => Join_rec_beta_jglue _ _
    (fun a b => (jglue ((-d) * conj b) (conj a * d))^) a b).
  pose (tF := fun z => ap_compose R (fun x => mu D0 x z) (jglue a b)
    @ ap (ap (fun x => mu D0 x z)) (bv0 a b s)).
  pose (bfh0 := bh0 (a * s) c d).
  pose (bfh1 := bh1 (s * b) c d).
  pose (bfv0 := tF (joinl c) @ bv0 (a * s) (s * b) c).
  pose (bfv1 := tF (joinr d) @ bv1 (a * s) (s * b) d).
  pose (bgh0 := (ap_compose L (mu D0 (joinl a)) (jglue c d)
    @ ap (ap (mu D0 (joinl a))) (bh0 s c d))
    @ bh0 a (s * c) (conj s * d)).
  pose (bgh1 := (ap_compose L (mu D0 (joinr b)) (jglue c d)
    @ ap (ap (mu D0 (joinr b))) (bh0 s c d))
    @ bh1 b (s * c) (conj s * d)).
  pose (bgv0 := bv0 a b (s * c)).
  pose (bgv1 := bv1 a b (conj s * d)).
  assert (BM : forall a b c d,
    concat_Ap (W a b) (jglue c d) @ (bv0 a b c @@ 1)
      = (1 @@ bv1 a b d) @ naturality_change
        (bh0 a c d) (bh1 b c d) (D D0 a b c d)).
  { intros a0 b0 c0 d0.
    refine (Join_rec2_beta_jglue_jglue J
      _ _ _ _ _ _ _ _ (D D0) a0 b0 c0 d0 @ _).
    exact (1 @@ concat_p_pp _ _ _). }
  assert (BF : concat_Ap U (jglue c d) @ (bfv0 @@ 1)
      = (1 @@ bfv1) @ naturality_change bfh0 bfh1
        (D D0 (a * s) (s * b) c d)).
  { napply (mixed_beta_vertical (tF (joinl c)) (tF (joinr d))
      (bv0 (a * s) (s * b) c) (bv1 (a * s) (s * b) d) _ _
      _ (concat_Ap (W (a * s) (s * b)) (jglue c d)) _).
    - exact (concat_Ap_homotopic U (W (a * s) (s * b)) tF (jglue c d)).
    - exact (BM (a * s) (s * b) c d). }
  assert (BG : concat_Ap V (jglue c d) @ (bgv0 @@ 1)
      = (1 @@ bgv1) @ naturality_change bgh0 bgh1
        (D D0 a b (s * c) (conj s * d))).
  { exact (concat_Ap_precompose_beta (W a b) L (jglue c d)
      (jglue (s * c) (conj s * d)) (bh0 s c d)
      (bh0 a (s * c) (conj s * d)) (bv1 a b (conj s * d))
      (bv0 a b (s * c)) (bh1 b (s * c) (conj s * d))
      _ (BM a b (s * c) (conj s * d))). }
  pose (eh0 := (join_natsq (p00 s a c) (p01 s a d))^).
  pose (eh1 := inverse_natural _ _ (join_natsq (p11 s b d) (p10 s b c))).
  pose (ev0 := (join_natsq (p00 s a c) (p10 s b c))^).
  pose (ev1 := inverse_natural _ _ (join_natsq (p11 s b d) (p01 s a d))).
  assert (EH0 : concat_Ap (first_ll D0 a s) (jglue c d)
    = naturality_change bfh0 bgh0 eh0).
  { lhs napply (Join_ind_FlFr_beta_jglue _ _ _ _ _ c d).
    rhs napply concat_pp_p.
    napply (ap (fun q => (bfh0 @@ 1) @ q)).
    lhs napply naturality_suffix.
    apply naturality_suffix. }
  assert (EH1 : concat_Ap (first_rl D0 b s) (jglue c d)
    = naturality_change bfh1 bgh1 eh1).
  { lhs napply (Join_ind_FlFr_beta_jglue _ _ _ _ _ c d).
    rhs napply concat_pp_p.
    napply (ap (fun q => (bfh1 @@ 1) @ q)).
    lhs napply naturality_suffix.
    apply naturality_suffix. }
  assert (EV0 : middle_l_glue_l D0 s a b c
    = naturality_change bfv0 bgv0 ev0).
  { lhs napply naturality_prefix.
    lhs napply naturality_prefix.
    exact (concat_p_pp (bfv0 @@ 1) ev0 (1 @@ bgv0)^). }
  assert (EV1 : middle_l_glue_r D0 s a b d
    = naturality_change bfv1 bgv1 ev1).
  { lhs napply naturality_prefix.
    lhs napply naturality_prefix.
    exact (concat_p_pp (bfv1 @@ 1) ev1 (1 @@ bgv1)^). }
  refine (ap (transport _ (jglue c d)) EV0 @ _ @ EV1^).
  napply (transport_naturality_square_beta U V
    (first_ll D0 a s) (first_rl D0 b s) (jglue c d)
    bfh0 bfh1 bfv0 bfv1 bgh0 bgh1 bgv0 bgv1
    _ _ eh0 eh1 ev0 ev1 BF BG EH0 EH1).
  exact (join_zigzag_filler_cube (p00 s a c) (p11 s b d)
    (p01 s a d) (p10 s b c) _ _ (diamond D0 s a b c d)).
Defined.

Definition middle_l_glue `{Univalence}
  `(D0 : CayleyDicksonDiamond (psphere 1) (-)) (s a b : C)
  : forall z : J,
    ap (fun x => mu D0 (mu D0 x (joinl s)) z) (jglue a b)
      @ first_rl D0 b s z
    = first_ll D0 a s z
      @ ap (fun x => mu D0 x (mu D0 (joinl s) z)) (jglue a b).
Proof.
  snapply Join_ind.
  - exact (middle_l_glue_l D0 s a b).
  - exact (middle_l_glue_r D0 s a b).
  - exact (middle_l_glue_glue D0 s a b).
Defined.

(** This choice of middle associator computes to the old constructor rows. It is built from the balanced diamond, rather than identifying arbitrary choices with [cd_assoc_middle_joinl]. *)
Definition middle_l `{Univalence}
  `(D0 : CayleyDicksonDiamond (psphere 1) (-)) (s : C) (x z : J)
  : mu D0 (mu D0 x (joinl s)) z = mu D0 x (mu D0 (joinl s) z).
Proof.
  revert x; snapply Join_ind_FlFr.
  - exact (fun a => first_ll D0 a s z).
  - exact (fun b => first_rl D0 b s z).
  - exact (fun a b => middle_l_glue D0 s a b z).
Defined.

Local Opaque middle_l_glue_glue.
Local Notation AL :=
  (fun D0 => @cd_assoc_last_joinl@{Set} (psphere 1)
    S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative D0
    S7LeftScalar.circle_commutative S7LeftScalar.circle_connected
    S7LeftScalar.circle_truncated).
Local Notation T :=
  (fun D0 => @cd_assoc_last_transport@{Set} (psphere 1)
    S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative D0
    S7LeftScalar.circle_commutative S7LeftScalar.circle_connected
    S7LeftScalar.circle_truncated).
Local Notation qll :=
  (fun D0 => @cd_assoc_last_joinl_first_ll@{Set} (psphere 1)
    S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative D0
    S7LeftScalar.circle_commutative S7LeftScalar.circle_connected
    S7LeftScalar.circle_truncated).
Local Notation qrl :=
  (fun D0 => @cd_assoc_last_joinl_first_rl@{Set} (psphere 1)
    S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative D0
    S7LeftScalar.circle_commutative S7LeftScalar.circle_connected
    S7LeftScalar.circle_truncated).
Local Notation mll :=
  (fun D0 => @cd_assoc_last_transport_loop_ll@{Set} (psphere 1)
    S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative D0
    S7LeftScalar.circle_commutative S7LeftScalar.circle_connected
    S7LeftScalar.circle_truncated).
Local Notation mrl :=
  (fun D0 => @cd_assoc_last_transport_loop_rl@{Set} (psphere 1)
    S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative D0
    S7LeftScalar.circle_commutative S7LeftScalar.circle_connected
    S7LeftScalar.circle_truncated).

Local Transparent associative_sgop_s1 commutative_sgop_s1.

Definition overlap_scalar_l `{Univalence} (s a c : C)
  : (cd_diamond_translate_l_neg_unit (X:=psphere 1) a s c)^
    = p00 s a c.
Proof.
  revert s a c.
  do 3 srapply (conn_point_elim (-1) (A:=psphere 1)).
  reflexivity.
Defined.

Definition overlap_scalar_r `{Univalence} (s b c : C)
  : comm c (s * b) @ (cd_diamond_translate_r_unit (X:=psphere 1) b s c)^
    = p10 s b c.
Proof.
  revert s b c.
  do 3 srapply (conn_point_elim (-1) (A:=psphere 1)).
  reflexivity.
Defined.

Local Opaque associative_sgop_s1 commutative_sgop_s1.

Definition overlap_glue `{Univalence}
  `(D0 : CayleyDicksonDiamond (psphere 1) (-)) (s a b c : C)
  : concat_Ap (fun x => AL D0 x (joinl s) c) (jglue a b)
      @ (qll D0 a s c @@ 1)
    = (1 @@ qrl D0 b s c) @ middle_l_glue_l D0 s a b c.
Proof.
  lhs tapply (JoinMapCoherence.translated_composite_comparison
    (North : C) (North : C)
    (fun x => sgop_s1 x s) (fun x => sgop_s1 x c)
    (fun x => sgop_s1 x (s * c))
    (sgop_s1 s) (sgop_s1 c) (fun x => sgop_s1 x c) (sgop_s1 (s * c))
    (comm c)
    (fun a => cd_diamond_translate_l_neg_unit (X:=psphere 1) a s c)
    (fun b => cd_diamond_translate_r_unit (X:=psphere 1) b s c)
    (fun a => p00 s a c) (fun b => p10 s b c)
    (fun a => overlap_scalar_l s a c)
    (fun b => overlap_scalar_r s b c) a b).
  napply whiskerL.
  exact (Join_ind_FlFr_beta_jglue _ _ _ _ _ a b).
Defined.

Definition overlap `{Univalence}
  `(D0 : CayleyDicksonDiamond (psphere 1) (-)) (s : C) (x : J) (c : C)
  : AL D0 x (joinl s) c = middle_l D0 s x (joinl c).
Proof.
  revert x; snapply Join_ind.
  - exact (fun a => qll D0 a s c).
  - exact (fun b => qrl D0 b s c).
  - intros a b.
    nrefine (equiv_naturality_transport2 _ _ (jglue a b) _ _ _).
    rhs napply (1 @@ Join_ind_FlFr_beta_jglue _ _ _ _ _ a b).
    exact (overlap_glue D0 s a b c).
Defined.

Definition column_loop `{Univalence}
  `(D0 : CayleyDicksonDiamond (psphere 1) (-))
  (s d : C) (x : J) {c : C} (p : c = c)
  : ap (T D0 x (joinl s) d) p = 1.
Proof.
  pose (K := fun c => ap (transport _ (jglue c d)) (overlap D0 s x c)
    @ apD (middle_l D0 s x) (jglue c d)).
  exact (ap_loop_nullhomotopic K p).
Defined.

Local Opaque ap_loop_nullhomotopic.

Definition column_loop_l `{Univalence}
  `(D0 : CayleyDicksonDiamond (psphere 1) (-))
  (s a d : C) {c : C} (p : c = c)
  : column_loop D0 s d (joinl a) p = mll D0 a s d c p
  := idpath.

Definition column_loop_r `{Univalence}
  `(D0 : CayleyDicksonDiamond (psphere 1) (-))
  (s b d : C) {c : C} (p : c = c)
  : column_loop D0 s d (joinr b) p = mrl D0 b s d c p
  := idpath.

(** OPEN 3, for any supplied circle diamond and any scalar loop. *)
Definition loop_x_joinl `{Univalence}
  `(D0 : CayleyDicksonDiamond (psphere 1) (-))
  (a b s d : C) {c : C} (p : c = c)
  : transport (fun x => ap (T D0 x (joinl s) d) p = 1) (jglue a b)
      (mll D0 a s d c p) = mrl D0 b s d c p.
Proof.
  exact (apD (fun x => column_loop D0 s d x p) (jglue a b)).
Defined.
End S7MiddleScalar.
