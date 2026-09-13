From HoTT Require Import Basics.
Require Import Types.Paths Types.Prod.
Require Import Classes.interfaces.abstract_algebra.
Require Import Pointed.Core.
Require Import Modalities.ReflectiveSubuniverse Truncations.Core.
Require Import Homotopy.HSpace.Core Homotopy.CayleyDickson.
Require Import Homotopy.Join.Core Homotopy.Join.Rec2.

Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.

(** * Moving scalars between the two inputs of the double *)

Section Balanced.
  Context {X : pType} `{CayleyDicksonSpheroid X}
    `{!Associative (@hspace_op X _)}
    `{!Commutative (@hspace_op X _)}.

  Local Notation assoc := (simple_associativity (f:=hspace_op)).
  Local Notation comm := (commutativity (f:=hspace_op)).

  (** The two changes of labels have the same diamond parameter. No symmetry of the diamond is required. *)
  Definition cd_diamond_parameter_balanced (s a b c d : X)
    : cd_diamond_parameter (a * s) (b * s) c d
      = cd_diamond_parameter a b (s * c) (conj s * d).
  Proof.
    unfold cd_diamond_parameter.
    lhs rapply (ap011 (fun u v => conj c * u * d * v)
      (distropp a s) (distropp b s)).
    rhs rapply (ap (fun u => u * conj a * (conj s * d) * conj b)
      (distropp s c)).
    lhs rapply (ap (fun u => u * d * (conj s * conj b))
      (assoc (conj c) (conj s) (conj a))).
    lhs rapply (assoc (conj c * conj s * conj a) d
      (conj s * conj b))^.
    lhs rapply (ap ((conj c * conj s * conj a) *.)
      (assoc d (conj s) (conj b))).
    lhs rapply (ap (fun u => (conj c * conj s * conj a) * (u * conj b))
      (comm d (conj s))).
    exact (assoc (conj c * conj s * conj a) (conj s * d) (conj b)).
  Defined.

  Definition cd_diamond_map_l_balanced (s a c : X)
    : cd_diamond_map_l (a * s) c == cd_diamond_map_l a (s * c).
  Proof.
    intro t; unfold cd_diamond_map_l.
    exact ((assoc a s (c * -t))^
      @ ap (a *.) (assoc s c (-t))).
  Defined.

  Definition cd_diamond_map_r_balanced (s b c : X)
    : cd_diamond_map_r (b * s) c == cd_diamond_map_r b (s * c).
  Proof.
    intro t; unfold cd_diamond_map_r.
    lhs rapply (ap (c *.) (assoc t b s)).
    lhs rapply (assoc c (t * b) s).
    lhs rapply (comm (c * (t * b)) s).
    exact (assoc s c (t * b)).
  Defined.

  (** Boundary identifications induced by the same parameter and map comparisons. *)
  Definition cd_balanced_00 (s a c : X)
    : (a * s) * c = a * (s * c)
    := (cd_diamond_map_l_neg_unit (a * s) c)^
      @ cd_diamond_map_l_balanced s a c (-mon_unit)
      @ cd_diamond_map_l_neg_unit a (s * c).

  Definition cd_balanced_01 (s a b c d : X)
    : conj (a * s) * d = conj a * (conj s * d)
    := (cd_diamond_map_r_parameter (a * s) (b * s) c d)^
      @ (cd_diamond_map_r_balanced s b c
          (cd_diamond_parameter (a * s) (b * s) c d)
        @ ap (cd_diamond_map_r b (s * c))
          (cd_diamond_parameter_balanced s a b c d))
      @ cd_diamond_map_r_parameter a b (s * c) (conj s * d).

  Definition cd_balanced_10 (s b c : X)
    : c * (b * s) = (s * c) * b
    := (cd_diamond_map_r_unit (b * s) c)^
      @ cd_diamond_map_r_balanced s b c mon_unit
      @ cd_diamond_map_r_unit b (s * c).

  Definition cd_balanced_11 (s a b c d : X)
    : (-d) * conj (b * s) = (-(conj s * d)) * conj b
    := (cd_diamond_map_l_parameter (a * s) (b * s) c d)^
      @ (cd_diamond_map_l_balanced s a c
          (cd_diamond_parameter (a * s) (b * s) c d)
        @ ap (cd_diamond_map_l a (s * c))
          (cd_diamond_parameter_balanced s a b c d))
      @ cd_diamond_map_l_parameter a b (s * c) (conj s * d).

  Context `{!CayleyDicksonDiamond X (-)}.

  (** Compare the actual fillers, retaining all four induced boundaries. *)
  Definition cd_op_diamond_balanced (s a b c d : X)
    : transport011
        (fun x : X * X => fun y : X * X =>
          zigzag (fst x) (snd x) (fst y)
            = zigzag (fst x) (snd x) (snd y))
        (path_prod' (cd_balanced_00 s a c) (cd_balanced_11 s a b c d))
        (path_prod' (cd_balanced_01 s a b c d) (cd_balanced_10 s b c))
        (cd_op_diamond (a * s) (b * s) c d)
      = cd_op_diamond a b (s * c) (conj s * d).
  Proof.
    exact (join_zigzag_filler_change (fun t => (cd_diamond t)^)
      (cd_diamond_map_l_balanced s a c)
      (cd_diamond_map_r_balanced s b c)
      (cd_diamond_parameter_balanced s a b c d) _ _ _ _ _ _ _ _).
  Defined.

  Context (n : trunc_index) `{!IsConnected n X, !IsTrunc n.+1 X}.

  (** Connectedness makes scalar-path families independent of labels absent from their endpoints. The join-valued fillers are not truncated. *)
  Definition cd_balanced_01_independent (s a b c d : X)
    : cd_balanced_01 s a b c d
      = cd_balanced_01 s a mon_unit mon_unit d.
  Proof.
    destruct (isconnected_elim (Tr n) _
      (fun b => cd_balanced_01 s a b c d)) as [q hq].
    refine (hq b @ (hq mon_unit)^ @ _).
    destruct (isconnected_elim (Tr n) _
      (fun c => cd_balanced_01 s a mon_unit c d)) as [r hr].
    exact (hr c @ (hr mon_unit)^).
  Defined.

  Definition cd_balanced_11_independent (s a b c d : X)
    : cd_balanced_11 s a b c d
      = cd_balanced_11 s mon_unit b mon_unit d.
  Proof.
    destruct (isconnected_elim (Tr n) _
      (fun a => cd_balanced_11 s a b c d)) as [q hq].
    refine (hq a @ (hq mon_unit)^ @ _).
    destruct (isconnected_elim (Tr n) _
      (fun c => cd_balanced_11 s mon_unit b c d)) as [r hr].
    exact (hr c @ (hr mon_unit)^).
  Defined.

  Definition cd_op_diamond_balanced_normalized (s a b c d : X)
    : transport011
        (fun x : X * X => fun y : X * X =>
          zigzag (fst x) (snd x) (fst y)
            = zigzag (fst x) (snd x) (snd y))
        (path_prod' (cd_balanced_00 s a c)
          (cd_balanced_11 s mon_unit b mon_unit d))
        (path_prod' (cd_balanced_01 s a mon_unit mon_unit d)
          (cd_balanced_10 s b c))
        (cd_op_diamond (a * s) (b * s) c d)
      = cd_op_diamond a b (s * c) (conj s * d).
  Proof.
    lhs_V napply (ap011 (fun p q => transport011 _ p q
      (cd_op_diamond (a * s) (b * s) c d))
      (ap (path_prod' (cd_balanced_00 s a c))
        (cd_balanced_11_independent s a b c d))
      (ap (fun p => path_prod' p (cd_balanced_10 s b c))
        (cd_balanced_01_independent s a b c d))).
    exact (cd_op_diamond_balanced s a b c d).
  Defined.

  (** Left and right scalar actions have different weights on the right copy. The balanced law moves a right action on the first input to a left action on the second. *)
  Definition cd_op_balanced (s : X) (x y : pjoin X X)
    : cd_op (functor_join (.* s) (.* s) x) y
      = cd_op x (functor_join (s *.) (conj s *.) y).
  Proof.
    pose (R := functor_join (.* s) (.* s)).
    pose (L := functor_join (s *.) (conj s *.)).
    pose (F := fun x y => cd_op (R x) y).
    pose (G := fun x y => cd_op x (L y)).
    pose (W := fun a b y => ap (fun x => cd_op x y) (jglue a b)).
    pose (bh0 := fun a c d => Join_rec_beta_jglue _ _
      (fun c d => jglue (a * c) (conj a * d)) c d).
    pose (bh1 := fun b c d => Join_rec_beta_jglue _ _
      (fun c d => (jglue ((-d) * conj b) (c * b))^) c d).
    pose (bv0 := fun a b c => Join_rec_beta_jglue _ _
      (fun a b => jglue (a * c) (c * b)) a b).
    pose (bv1 := fun a b d => Join_rec_beta_jglue _ _
      (fun a b => (jglue ((-d) * conj b) (conj a * d))^) a b).
    pose (tF := fun a b y =>
      ap_compose R (fun x => cd_op x y) (jglue a b)
        @ ap (ap (fun x => cd_op x y))
          (functor_join_beta_jglue (.* s) (.* s) a b)).
    pose (bfh0 := fun a c d => bh0 (a * s) c d).
    pose (bfh1 := fun b c d => bh1 (b * s) c d).
    pose (bfv0 := fun a b c => tF a b (joinl c)
      @ bv0 (a * s) (b * s) c).
    pose (bfv1 := fun a b d => tF a b (joinr d)
      @ bv1 (a * s) (b * s) d).
    pose (bgh0 := fun a c d =>
      (ap_compose L (cd_op (joinl a)) (jglue c d)
        @ ap (ap (cd_op (joinl a)))
          (functor_join_beta_jglue (s *.) (conj s *.) c d))
        @ bh0 a (s * c) (conj s * d)).
    pose (bgh1 := fun b c d =>
      (ap_compose L (cd_op (joinr b)) (jglue c d)
        @ ap (ap (cd_op (joinr b)))
          (functor_join_beta_jglue (s *.) (conj s *.) c d))
        @ bh1 b (s * c) (conj s * d)).
    pose (bgv0 := fun a b c => bv0 a b (s * c)).
    pose (bgv1 := fun a b d => bv1 a b (conj s * d)).
    pose (p00 := cd_balanced_00 s).
    pose (p01 := fun a d => cd_balanced_01 s a mon_unit mon_unit d).
    pose (p10 := cd_balanced_10 s).
    pose (p11 := fun b d => cd_balanced_11 s mon_unit b mon_unit d).
    pose (eh0 := fun a c d => (join_natsq (p00 a c) (p01 a d))^).
    pose (eh1 := fun b c d =>
      inverse_natural _ _ (join_natsq (p11 b d) (p10 b c))).
    pose (ev0 := fun a b c => (join_natsq (p00 a c) (p10 b c))^).
    pose (ev1 := fun a b d =>
      inverse_natural _ _ (join_natsq (p11 b d) (p01 a d))).
    revert x y; snapply (Join_ind2_FlFr F G).
    - exact (fun a c => ap joinl (p00 a c)).
    - exact (fun a d => ap joinr (p01 a d)).
    - exact (fun b c => ap joinr (p10 b c)).
    - exact (fun b d => ap joinl (p11 b d)).
    - exact (fun a c d => naturality_change
        (bfh0 a c d) (bgh0 a c d) (eh0 a c d)).
    - exact (fun b c d => naturality_change
        (bfh1 b c d) (bgh1 b c d) (eh1 b c d)).
    - exact (fun a b c => naturality_change
        (bfv0 a b c) (bgv0 a b c) (ev0 a b c)).
    - exact (fun a b d => naturality_change
        (bfv1 a b d) (bgv1 a b d) (ev1 a b d)).
    - intros a b c d.
      assert (BM : forall a b c d,
        concat_Ap (W a b) (jglue c d) @ (bv0 a b c @@ 1)
        = (1 @@ bv1 a b d) @ naturality_change
          (bh0 a c d) (bh1 b c d) (cd_op_diamond a b c d)).
      { intros a0 b0 c0 d0.
        refine (Join_rec2_beta_jglue_jglue (pjoin X X)
          _ _ _ _ _ _ _ _ cd_op_diamond a0 b0 c0 d0 @ _).
        exact (1 @@ concat_p_pp _ _ _). }
      assert (BF : concat_Ap (fun y => ap (fun x => F x y)
          (jglue a b)) (jglue c d) @ (bfv0 a b c @@ 1)
        = (1 @@ bfv1 a b d) @ naturality_change
          (bfh0 a c d) (bfh1 b c d)
          (cd_op_diamond (a * s) (b * s) c d)).
      { napply (mixed_beta_vertical (tF a b (joinl c))
          (tF a b (joinr d)) (bv0 (a * s) (b * s) c)
          (bv1 (a * s) (b * s) d) _ _
          _ (concat_Ap (W (a * s) (b * s)) (jglue c d)) _).
        - exact (concat_Ap_homotopic _ _ (tF a b) (jglue c d)).
        - exact (BM (a * s) (b * s) c d). }
      assert (BG : concat_Ap (fun y => ap (fun x => G x y)
          (jglue a b)) (jglue c d) @ (bgv0 a b c @@ 1)
        = (1 @@ bgv1 a b d) @ naturality_change
          (bgh0 a c d) (bgh1 b c d)
          (cd_op_diamond a b (s * c) (conj s * d))).
      { exact (concat_Ap_precompose_beta (W a b) L (jglue c d)
          (jglue (s * c) (conj s * d))
          (functor_join_beta_jglue (s *.) (conj s *.) c d)
          (bh0 a (s * c) (conj s * d)) (bv1 a b (conj s * d))
          (bv0 a b (s * c)) (bh1 b (s * c) (conj s * d))
          _ (BM a b (s * c) (conj s * d))). }
      napply (naturality_cube_change
        (ap joinl (p00 a c)) (ap joinr (p01 a d))
        (ap joinr (p10 b c)) (ap joinl (p11 b d))
        (bfh0 a c d) (bfh1 b c d) (bfv0 a b c) (bfv1 a b d)
        (bgh0 a c d) (bgh1 b c d) (bgv0 a b c) (bgv1 a b d)
        _ _ _ _ (eh0 a c d) (eh1 b c d)
        (ev0 a b c) (ev1 a b d) BF BG).
      exact (join_zigzag_filler_cube (p00 a c) (p11 b d)
        (p01 a d) (p10 b c) _ _
        (cd_op_diamond_balanced_normalized s a b c d)).
  Defined.

  (** In multiplication coordinates, the balanced law is associativity with a left-copy scalar in the middle. Both outer arguments are arbitrary. *)
  Definition cd_assoc_middle_joinl (x : pjoin X X) (s : X)
    (y : pjoin X X)
    : cd_op (cd_op x (joinl s)) y = cd_op x (cd_op (joinl s) y).
  Proof.
    exact (ap (fun z => cd_op z y) (cd_op_right_translate_joinl s x)
      @ cd_op_balanced s x y).
  Defined.
End Balanced.
