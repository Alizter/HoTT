From HoTT Require Import Basics Types.Paths Types.Prod.
From HoTT Require Import Classes.interfaces.canonical_names.
From HoTT Require Import Pointed.Core Modalities.ReflectiveSubuniverse Truncations.Core.
From HoTT Require Import Homotopy.HSpace.Core Homotopy.CayleyDickson Homotopy.Join.Core.

Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.

(** The original diagonal cube, before exposing its geometric input. The final [idpath] checks the entire witness, including its mixed beta proofs and its four side comparisons. *)
Section DiagonalWitness.
  Context {X : pType} `{CayleyDicksonSpheroid X}
    `{!Associative hspace_op} `{!CayleyDicksonDiamond X (-)}
    `{!Commutative (@hspace_op X _)}
    `{!IsConnected (0%trunc) X, !IsTrunc 1 X}.

  Local Opaque cd_diamond cd_op_diamond.

  Definition legacy_diagonal_cube (r a b c d : X)
    : transport
        (fun y => ap (fun x => cd_op x (functor_join (.* r) (.* r) y))
            (jglue a b) @ cd_op_diagonal_equivariance_joinr r b y
          = cd_op_diagonal_equivariance_joinl r a y
            @ ap (fun x => functor_join (.* r) (.* r) (cd_op x y))
                (jglue a b))
        (jglue c d) (cd_op_diagonal_equivariance_glue_joinl r a b c)
      = cd_op_diagonal_equivariance_glue_joinr r a b d.
  Proof.
    pose (rho := functor_join (.* r) (.* r)).
    pose (f0 := cd_op (joinl a)).
    pose (f1 := cd_op (joinr b)).
    pose (W := fun y => ap (fun x => cd_op x y) (jglue a b)).
    pose (U := fun y => W (rho y)).
    pose (V := fun y => ap (fun x => rho (cd_op x y)) (jglue a b)).
    pose (brho := functor_join_beta_jglue (.* r) (.* r)).
    pose (bh0 := fun c d => Join_rec_beta_jglue _ _
      (fun c d => jglue (a * c) (conj a * d)) c d).
    pose (bh1 := fun c d => Join_rec_beta_jglue _ _
      (fun c d => (jglue ((-d) * conj b) (c * b))^) c d).
    pose (bv0 := fun c => Join_rec_beta_jglue _ _
      (fun a b => jglue (a * c) (c * b)) a b).
    pose (bv1 := fun d => Join_rec_beta_jglue _ _
      (fun a b => (jglue ((-d) * conj b) (conj a * d))^) a b).
    pose (bfh0 := (ap_compose rho f0 (jglue c d)
      @ ap (ap f0) (brho c d)) @ bh0 (c * r) (d * r)).
    pose (bfh1 := (ap_compose rho f1 (jglue c d)
      @ ap (ap f1) (brho c d)) @ bh1 (c * r) (d * r)).
    pose (bfv0 := bv0 (c * r)).
    pose (bfv1 := bv1 (d * r)).
    pose (t := fun y => ap_compose (fun x => cd_op x y) rho (jglue a b)).
    pose (bgh0 := (ap_compose f0 rho (jglue c d)
      @ ap (ap rho) (bh0 c d)) @ brho (a * c) (conj a * d)).
    pose (bgh1 := (ap_compose f1 rho (jglue c d)
      @ ap (ap rho) (bh1 c d)) @ (ap_V rho (jglue ((-d) * conj b) (c * b))
        @ inverse2 (brho ((-d) * conj b) (c * b)))).
    pose (bgv0 := (t (joinl c) @ ap (ap rho) (bv0 c))
      @ brho (a * c) (c * b)).
    pose (bgv1 := (t (joinr d) @ ap (ap rho) (bv1 d))
      @ (ap_V rho (jglue ((-d) * conj b) (conj a * d))
        @ inverse2 (brho ((-d) * conj b) (conj a * d)))).
    assert (BM : forall c d, concat_Ap W (jglue c d) @ (bv0 c @@ 1)
      = (1 @@ bv1 d) @ naturality_change
          (bh0 c d) (bh1 c d) (cd_op_diamond a b c d)).
    { intros c0 d0.
      nrefine (Join_rec2_beta_jglue_jglue (pjoin X X)
        _ _ _ _ _ _ _ _ cd_op_diamond a b c0 d0 @ _).
      exact (1 @@ concat_p_pp _ _ _). }
    assert (BF : concat_Ap U (jglue c d) @ (bfv0 @@ 1)
      = (1 @@ bfv1) @ naturality_change bfh0 bfh1
        (cd_op_diamond a b (c * r) (d * r))).
    { exact (concat_Ap_precompose_beta W rho (jglue c d)
        (jglue (c * r) (d * r)) (brho c d)
        (bh0 (c * r) (d * r)) (bv1 (d * r))
        (bv0 (c * r)) (bh1 (c * r) (d * r)) _ (BM (c * r) (d * r))). }
    assert (BG : concat_Ap V (jglue c d) @ (bgv0 @@ 1)
      = (1 @@ bgv1) @ naturality_change bgh0 bgh1
        (join_zigzag_filler (.* r) (.* r) 1 1 1 1 (cd_op_diamond a b c d))).
    { napply (mixed_beta_compose
        (ap_compose f0 rho (jglue c d) @ ap (ap rho) (bh0 c d))
        (t (joinr d) @ ap (ap rho) (bv1 d))
        (t (joinl c) @ ap (ap rho) (bv0 c))
        (ap_compose f1 rho (jglue c d) @ ap (ap rho) (bh1 c d))
        _ _ _ _ _ (ap_naturality rho (cd_op_diamond a b c d)) _).
      - napply (mixed_beta_vertical (t (joinl c)) (t (joinr d))
          (ap (ap rho) (bv0 c)) (ap (ap rho) (bv1 d)) _ _
          _ (concat_Ap (fun y => ap rho (W y)) (jglue c d)) _).
        + exact (concat_Ap_homotopic V (fun y => ap rho (W y)) t (jglue c d)).
        + exact (concat_Ap_postcompose_beta W rho (jglue c d)
            (bh0 c d) (bv1 d) (bv0 c) (bh1 c d) _ (BM c d)).
      - rhs napply (1 @@ ap (naturality_change _ _)
          (join_zigzag_filler_refl (.* r) (.* r) (cd_op_diamond a b c d))).
        exact (ap_pV_filler_beta rho
          (jglue (a * c) (conj a * d)) (jglue ((-d) * conj b) (conj a * d))
          (jglue (a * c) (c * b)) (jglue ((-d) * conj b) (c * b))
          (brho _ _) (brho _ _) (brho _ _) (brho _ _) (cd_op_diamond a b c d)). }
    pose (p00 := cd_diamond_translate_l_neg_unit a c r).
    pose (p01 := cd_diamond_translate_r_parameter a mon_unit mon_unit d r).
    pose (p10 := cd_diamond_translate_r_unit b c r).
    pose (p11 := cd_diamond_translate_l_parameter mon_unit b mon_unit d r).
    pose (eh0 := (join_natsq p00 p01)^).
    pose (eh1 := inverse_natural _ _ (join_natsq p11 p10)).
    pose (ev0 := (join_natsq p00 p10)^).
    pose (ev1 := inverse_natural _ _ (join_natsq p11 p01)).
    assert (EH0 : concat_Ap (cd_op_diagonal_equivariance_joinl r a) (jglue c d)
      = naturality_change bfh0 bgh0 eh0).
    { lhs napply (Join_ind_FlFr_beta_jglue _ _ _ _ _ c d).
      lhs napply naturality_prefix.
      lhs napply naturality_prefix.
      rhs napply concat_pp_p.
      napply (ap (fun q => (bfh0 @@ 1) @ q)).
      lhs napply naturality_suffix.
      apply naturality_suffix. }
    assert (EH1 : concat_Ap (cd_op_diagonal_equivariance_joinr r b) (jglue c d)
      = naturality_change bfh1 bgh1 eh1).
    { lhs napply (Join_ind_FlFr_beta_jglue _ _ _ _ _ c d).
      lhs napply naturality_prefix.
      lhs napply naturality_prefix.
      rhs napply concat_pp_p.
      napply (ap (fun q => (bfh1 @@ 1) @ q)).
      lhs napply naturality_suffix.
      lhs napply naturality_suffix.
      lhs napply naturality_suffix.
      exact (ap (fun q => eh1 @ (1 @@ q)^) (concat_pp_p _ _ _)). }
    assert (EV0 : cd_op_diagonal_equivariance_glue_joinl r a b c
      = naturality_change bfv0 bgv0 ev0).
    { rhs napply concat_pp_p.
      napply (ap (fun q => (bfv0 @@ 1) @ q)).
      lhs napply naturality_suffix.
      apply naturality_suffix. }
    assert (EV1 : cd_op_diagonal_equivariance_glue_joinr r a b d
      = naturality_change bfv1 bgv1 ev1).
    { rhs napply concat_pp_p.
      napply (ap (fun q => (bfv1 @@ 1) @ q)).
      lhs napply naturality_suffix.
      lhs napply naturality_suffix.
      lhs napply naturality_suffix.
      exact (ap (fun q => ev1 @ (1 @@ q)^) (concat_pp_p _ _ _)). }
    refine (ap (transport _ (jglue c d)) EV0 @ _ @ EV1^).
    napply (transport_naturality_square_beta U V
      (cd_op_diagonal_equivariance_joinl r a)
      (cd_op_diagonal_equivariance_joinr r b)
      (jglue c d) bfh0 bfh1 bfv0 bfv1 bgh0 bgh1 bgv0 bgv1
      _ _ eh0 eh1 ev0 ev1 BF BG EH0 EH1).
    exact (join_zigzag_filler_cube p00 p11 p01 p10 _ _
      (cd_op_diamond_diagonal a b c d r)).
  Defined.

  Example selected_diagonal_cube_unchanged (r a b c d : X)
    : cd_op_diagonal_equivariance_glue_glue r a b c d
      = legacy_diagonal_cube r a b c d
    := idpath.
End DiagonalWitness.
