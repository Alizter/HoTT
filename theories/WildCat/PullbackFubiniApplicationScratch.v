Require Import Basics.Equivalences Basics.Overture Basics.PathGroupoids
  Basics.Tactics.
Require Import Limits.Pullback.
Require Import WildCat.Adjoint WildCat.Core WildCat.Cylinder WildCat.Equiv
  WildCat.EquivGpd WildCat.FunctorCat WildCat.Limits WildCat.LimitsScratch
  WildCat.NatTrans WildCat.OneGroupoid WildCat.PointwiseLimitUniversal
  WildCat.PullbackLimitScratch WildCat.Square WildCat.SwapAdjunction
  WildCat.TwoFunctor WildCat.TwoOneCat WildCat.TwoYoneda WildCat.Universe
  WildCat.ZeroGroupoid.

Set Typeclasses Depth 4.

(** * The coherent pullback operation and its 3-by-3 test case *)


(** ** Ordinary pullbacks populate walking-cospan limits in [Type] *)

Definition cospan_left_map (X : Fun02 WalkingCospan Type)
  : X cospan_left -> X cospan_center
  := fmap X (a := cospan_left) (b := cospan_center) tt.

Definition cospan_right_map (X : Fun02 WalkingCospan Type)
  : X cospan_right -> X cospan_center
  := fmap X (a := cospan_right) (b := cospan_center) tt.

Definition cospan_left_naturality
  {X Y : Fun02 WalkingCospan Type} (alpha : X $-> Y)
  : alpha cospan_center o cospan_left_map X
    == cospan_left_map Y o alpha cospan_left
  := isnat alpha
    (a := cospan_left) (a' := cospan_center) tt.

Definition cospan_right_naturality
  {X Y : Fun02 WalkingCospan Type} (alpha : X $-> Y)
  : alpha cospan_center o cospan_right_map X
    == cospan_right_map Y o alpha cospan_right
  := isnat alpha
    (a := cospan_right) (a' := cospan_center) tt.

Definition cospan_pullback_apex
  (X : Fun02 WalkingCospan Type) : Type
  := Pullback (cospan_left_map X) (cospan_right_map X).

Definition cospan_pullback_cone
  (X : Fun02 WalkingCospan Type)
  : diagonal02 Type WalkingCospan (cospan_pullback_apex X) $-> X.
Proof.
  snapply Build_NatTrans.
  - intro i.
    destruct i.
    + exact pullback_pr1.
    + exact (cospan_left_map X o pullback_pr1).
    + exact pullback_pr2.
  - snapply Build_Is1Natural.
    intros i j h.
    destruct i, j; destruct h.
    + intro x. exact 1.
    + intro x. exact x.2.2.
Defined.


Definition cospan_pullback_corec
  (D : Fun02 WalkingCospan Type) (Y : Type)
  (alpha : diagonal02 Type WalkingCospan Y $-> D)
  : Y -> cospan_pullback_apex D
  := fun y =>
    (alpha cospan_left y;
     alpha cospan_right y;
     (isnat alpha
       (a := cospan_left) (a' := cospan_center) tt y)^
       @ isnat alpha
         (a := cospan_right) (a' := cospan_center) tt y).

(** The pullback apex acts functorially on coherent cospans.  We use the
    inverse of the stored naturality cell explicitly: an arbitrary
    [Is1Natural] carries both orientations but does not assert that they are
    inverse to one another. *)
Definition cospan_pullback_map
  {X Y : Fun02 WalkingCospan Type} (alpha : X $-> Y)
  : cospan_pullback_apex X -> cospan_pullback_apex Y
  := functor_pullback
      (cospan_left_map X) (cospan_right_map X)
      (cospan_left_map Y) (cospan_right_map Y)
      (alpha cospan_center) (alpha cospan_left) (alpha cospan_right)
      (fun x => (cospan_left_naturality alpha x)^)
      (fun x => (cospan_right_naturality alpha x)^).

Definition cospan_pullback_map_homotopy
  {X Y : Fun02 WalkingCospan Type}
  {alpha beta : X $-> Y} (p : alpha $== beta)
  : cospan_pullback_map alpha == cospan_pullback_map beta.
Proof.
  snapply pullback_homotopic.
  - intro x.
    exact (natmod_component alpha beta p cospan_left x.1).
  - intro x.
    exact (natmod_component alpha beta p cospan_right x.2.1).
  - intros [xl [xr xglue]].
    unfold cospan_pullback_map, functor_pullback.
    cbn beta.
    unfold Sigma.functor_sigma.
    cbn beta.
    cbn.
    unfold cospan_left_map, cospan_right_map.
    cbn beta.
    pose (cl := natmod_isnatural alpha beta p
      (a := cospan_left) (b := cospan_center) tt xl).
    pose (cr := natmod_isnatural alpha beta p
      (a := cospan_right) (b := cospan_center) tt xr).
    cbn in cl, cr.
    pose (cc := concat_Ap
      (natmod_component alpha beta p cospan_center) xglue).
    cbn in cc.
    pose (cl' := moveL_Vp _ _ _
      ((concat_pp_p _ _ _)^ @ moveR_pV _ _ _ cl)).
    rewrite !inv_V.
    rewrite <- !concat_pp_p.
    rewrite cl'.
    rewrite (concat_pp_p _
      (natmod_component alpha beta p cospan_center
        (cospan_left_map X xl))
      (ap (beta cospan_center) xglue)).
    rewrite <- cc.
    rewrite !concat_pp_p.
    rewrite <- cr.
    reflexivity.
Defined.

Global Instance is0functor_cospan_pullback_apex
  : Is0Functor cospan_pullback_apex.
Proof.
  snapply Build_Is0Functor.
  exact (fun X Y alpha => cospan_pullback_map alpha).
Defined.

Definition cospan_pullback_map_id
  (X : Fun02 WalkingCospan Type)
  : cospan_pullback_map (Id X) == idmap.
Proof.
  snapply pullback_homotopic.
  - intro x; reflexivity.
  - intro x; reflexivity.
  - intros [xl [xr xglue]].
    unfold cospan_pullback_map, functor_pullback.
    cbn beta.
    unfold Sigma.functor_sigma.
    cbn beta.
    cbn.
    rewrite !concat_1p, !concat_p1, ap_idmap.
    reflexivity.
Defined.

Definition cospan_pullback_map_comp
  {X Y Z : Fun02 WalkingCospan Type}
  (alpha : X $-> Y) (beta : Y $-> Z)
  : cospan_pullback_map (beta $o alpha)
    == cospan_pullback_map beta o cospan_pullback_map alpha.
Proof.
  snapply pullback_homotopic.
  - intro x; reflexivity.
  - intro x; reflexivity.
  - intros [xl [xr xglue]].
    unfold cospan_pullback_map, functor_pullback.
    cbn beta.
    unfold Sigma.functor_sigma.
    cbn beta.
    cbn.
    rewrite !concat_1p, !concat_p1.
    rewrite !inv_pp, !ap_pp, !ap_V, !inv_V.
    rewrite (ap_compose (alpha cospan_center)
      (beta cospan_center) xglue).
    rewrite !concat_pp_p.
    reflexivity.
Defined.

Global Instance is1functor_cospan_pullback_apex
  : Is1Functor cospan_pullback_apex.
Proof.
  snapply Build_Is1Functor.
  - intros X Y alpha beta p.
    exact (cospan_pullback_map_homotopy p).
  - exact cospan_pullback_map_id.
  - intros X Y Z alpha beta.
    exact (cospan_pullback_map_comp alpha beta).
Defined.

Definition fun12_cospan_pullback
  : Fun12 (Fun02 WalkingCospan Type) Type
  := Build_Fun12 cospan_pullback_apex.

Definition cospan_pullback_counit_component
  (X : Fun02 WalkingCospan Type)
  : diagonal02 Type WalkingCospan (cospan_pullback_apex X) $-> X
  := cospan_pullback_cone X.

Definition cospan_pullback_counit_naturality
  {X Y : Fun02 WalkingCospan Type} (alpha : X $-> Y)
  : NatModification
      (A := WalkingCospan) (B := Type)
      (F := diagonal02 Type WalkingCospan (cospan_pullback_apex X))
      (G := Y)
      (@cat_comp (Fun02 WalkingCospan Type) _
        (is01cat_fun02 WalkingCospan Type)
        (diagonal02 Type WalkingCospan (cospan_pullback_apex X))
        (diagonal02 Type WalkingCospan (cospan_pullback_apex Y))
        Y
        (cospan_pullback_counit_component Y)
        (fmap (diagonal02 Type WalkingCospan)
          (cospan_pullback_map alpha)))
      (@cat_comp (Fun02 WalkingCospan Type) _
        (is01cat_fun02 WalkingCospan Type)
        (diagonal02 Type WalkingCospan (cospan_pullback_apex X))
        X Y alpha (cospan_pullback_counit_component X)).
Proof.
  snapply Build_NatModification.
  { intro i.
    destruct i.
    - intro x; reflexivity.
    - intro x.
      exact (isnat alpha (a := cospan_left)
        (a' := cospan_center) tt x.1)^.
    - intro x; reflexivity. }
  intros i j f.
  destruct i, j; destruct f; cbn beta.
  - intros [xl [xr xglue]].
    unfold Cylinder, Square.
    cbn.
    rewrite !concat_1p, !concat_p1, concat_Vp.
    reflexivity.
  - intros [xl [xr xglue]].
    unfold Cylinder, Square.
    cbn.
    rewrite !concat_1p, !concat_p1, !inv_V, !concat_pp_p.
    reflexivity.
Defined.

Definition nattrans_cospan_pullback_counit
  : NatTrans
      (diagonal02 Type WalkingCospan o cospan_pullback_apex)
      idmap.
Proof.
  snapply Build_NatTrans.
  { exact cospan_pullback_counit_component. }
  snapply Build_Is1Natural.
  intros X Y alpha.
  exact (cospan_pullback_counit_naturality alpha).
Defined.

Definition cospan_pullback_unit_component (P : Type)
  : P -> cospan_pullback_apex
      (diagonal02 Type WalkingCospan P)
  := fun x => (x; (x; 1)).

Definition nattrans_cospan_pullback_unit
  : NatTrans idmap
      (cospan_pullback_apex o diagonal02 Type WalkingCospan).
Proof.
  snapply Build_NatTrans.
  { exact cospan_pullback_unit_component. }
  snapply Build_Is1Natural.
  intros P Q f x.
  unfold cospan_pullback_unit_component.
  unfold cospan_pullback_map, functor_pullback.
  cbn beta.
  unfold Sigma.functor_sigma.
  cbn beta.
  cbn.
  reflexivity.
Defined.

Definition cospan_pullback_triangle_l (P : Type)
  : NatModification
      (A := WalkingCospan) (B := Type)
      (F := diagonal02 Type WalkingCospan P)
      (G := diagonal02 Type WalkingCospan P)
      (nattrans_comp
        (F := diagonal02 Type WalkingCospan P)
        (G := diagonal02 Type WalkingCospan
          (cospan_pullback_apex
            (diagonal02 Type WalkingCospan P)))
        (K := diagonal02 Type WalkingCospan P)
        (cospan_pullback_counit_component
          (diagonal02 Type WalkingCospan P))
        (fmap (diagonal02 Type WalkingCospan)
          (cospan_pullback_unit_component P)))
      (nattrans_id (diagonal02 Type WalkingCospan P)).
Proof.
  snapply Build_NatModification.
  { intro i.
    destruct i; intro x; reflexivity. }
  intros i j f.
  destruct i, j; destruct f; cbn beta.
  - intro x.
    unfold Cylinder, Square.
    cbn.
    reflexivity.
  - intro x.
    unfold Cylinder, Square.
    cbn.
    reflexivity.
Defined.

Definition cospan_pullback_triangle_r
  (X : Fun02 WalkingCospan Type)
  : cospan_pullback_map
      (cospan_pullback_counit_component X)
      o cospan_pullback_unit_component (cospan_pullback_apex X)
    == idmap.
Proof.
  snapply pullback_homotopic.
  - intro x; reflexivity.
  - intro x; reflexivity.
  - intros [xl [xr xglue]].
    unfold cospan_pullback_map, functor_pullback.
    unfold cospan_pullback_unit_component.
    cbn beta.
    unfold Sigma.functor_sigma.
    cbn beta.
    cbn.
    rewrite !concat_1p, !concat_p1, inv_V.
    reflexivity.
Defined.

Definition gpd_adjunction_cospan_pullback
  : GpdAdjunction
      (fun12_fun22 (fun22_diagonal02 Type WalkingCospan))
      fun12_cospan_pullback.
Proof.
  napply (Build_GpdAdjunction_unit_counit
    (fun12_fun22 (fun22_diagonal02 Type WalkingCospan))
    fun12_cospan_pullback
    nattrans_cospan_pullback_counit
    nattrans_cospan_pullback_unit).
  - exact cospan_pullback_triangle_l.
  - exact cospan_pullback_triangle_r.
  Unshelve.
  { exact (HoTT.WildCat.LimitsScratch.is1functor_diagonal02_generic
      Type WalkingCospan). }
  exact is1functor_cospan_pullback_apex.
Defined.

Global Instance haslimit02_type_walking_cospan
  : HasLimit02 Type WalkingCospan.
Proof.
  snapply Build_HasLimit02.
  - exact fun12_cospan_pullback.
  - exact gpd_adjunction_cospan_pullback.
Defined.

(** The chosen coherent right adjoint supplies the universal property of the
    concrete pullback cone.  The canonical cone reconstructed from the
    adjunction differs only by postcomposition with the diagonal identity. *)
Definition cospan_pullback_islimit (D : Fun02 WalkingCospan Type)
  : HoTT.WildCat.LimitsScratch.IsLimitCone
      D (cospan_pullback_apex D) (cospan_pullback_cone D).
Proof.
  pose (H := cat_limit02_cone_islimit Type WalkingCospan D).
  cbn [cat_limit02 haslimit02_type_walking_cospan] in H.
  refine (islimitcone_homotopic _ H).
  unfold cat_limit02_cone, limit_cone_of_islimit, cat_limit02_islimit.
  change (NatModification
    (A := WalkingCospan) (B := Type)
    (nattrans_comp
      (cospan_pullback_counit_component D)
      (fmap (diagonal02 Type WalkingCospan)
        (Id (cospan_pullback_apex D))))
    (cospan_pullback_counit_component D)).
  snapply Build_NatModification.
  { intro i.
    destruct i; intro x; reflexivity. }
  intros i j f.
  destruct i, j; destruct f; cbn beta.
  - intro x.
    unfold Cylinder, Square.
    cbn.
    reflexivity.
  - intro x.
    unfold Cylinder, Square.
    cbn.
    rewrite !concat_1p, !concat_p1.
    reflexivity.
Defined.


(** ** Canonical iterated pullbacks *)

Definition pointwise_cospan_pullback
  {C : Type} `{IsGraph C}
  (X : Fun02 C (Fun02 WalkingCospan Type))
  : Fun02 C Type
  := fun02_postcomp (A := C) fun12_cospan_pullback X.

Definition iterated_cospan_pullback_rows
  (X : Fun02 WalkingCospan
    (Fun02 WalkingCospan Type))
  : Type
  := cospan_pullback_apex (pointwise_cospan_pullback X).

Definition iterated_cospan_pullback_columns
  (X : Fun02 WalkingCospan
    (Fun02 WalkingCospan Type))
  : Type
  := cospan_pullback_apex
      (pointwise_cospan_pullback
        (swap_fun02 WalkingCospan WalkingCospan Type X)).

(** ** Fubini for pullbacks *)

(** Pullback Fubini consumes one coherent double cospan.  Internally,
    [swap_fun02] transposes a naturality cell and [cospan_pullback_map]
    reverses it, so the resulting column map contains a double inverse.
    Homotopy invariance removes that representational difference before
    applying the ordinary pullback 3-by-3 equivalence. *)
Definition equiv_iterated_cospan_pullback_fubini
  (X : Fun02 WalkingCospan (Fun02 WalkingCospan Type))
  : iterated_cospan_pullback_columns X
    <~> iterated_cospan_pullback_rows X.
Proof.
  pose (A00 := X cospan_left cospan_left).
  pose (A02 := X cospan_left cospan_center).
  pose (A04 := X cospan_left cospan_right).
  pose (A20 := X cospan_center cospan_left).
  pose (A22 := X cospan_center cospan_center).
  pose (A24 := X cospan_center cospan_right).
  pose (A40 := X cospan_right cospan_left).
  pose (A42 := X cospan_right cospan_center).
  pose (A44 := X cospan_right cospan_right).
  pose (f01 := cospan_left_map (X cospan_left)).
  pose (f03 := cospan_right_map (X cospan_left)).
  pose (f21 := cospan_left_map (X cospan_center)).
  pose (f23 := cospan_right_map (X cospan_center)).
  pose (f41 := cospan_left_map (X cospan_right)).
  pose (f43 := cospan_right_map (X cospan_right)).
  pose (alpha1 := fmap X
    (a := cospan_left) (b := cospan_center) tt).
  pose (alpha3 := fmap X
    (a := cospan_right) (b := cospan_center) tt).
  pose (f10 := alpha1 cospan_left).
  pose (f12 := alpha1 cospan_center).
  pose (f14 := alpha1 cospan_right).
  pose (f30 := alpha3 cospan_left).
  pose (f32 := alpha3 cospan_center).
  pose (f34 := alpha3 cospan_right).
  pose (H11 := cospan_left_naturality alpha1).
  pose (H13 := cospan_right_naturality alpha1).
  pose (H31 := cospan_left_naturality alpha3).
  pose (H33 := cospan_right_naturality alpha3).
  change (Pullback
    (functor_pullback f10 f30 f12 f32 f21 f01 f41
      (fun x => ((H11 x)^)^) (fun x => ((H31 x)^)^))
    (functor_pullback f14 f34 f12 f32 f23 f03 f43
      (fun x => ((H13 x)^)^) (fun x => ((H33 x)^)^))
    <~> Pullback
    (functor_pullback f01 f03 f21 f23 f12 f10 f14
      (symmetry _ _ H11) (symmetry _ _ H13))
    (functor_pullback f41 f43 f21 f23 f32 f30 f34
      (symmetry _ _ H31) (symmetry _ _ H33))).
  refine (pullback3x3
    A00 A02 A04 A20 A22 A24 A40 A42 A44
    f01 f03 f10 f12 f14 f21 f23 f30 f32 f34 f41 f43
    H11 H13 H31 H33 oE _).
  rapply equiv_pullback_homotopic.
  - rapply functor_pullback_homotopic.
    + intro x; apply inv_V.
    + intro x; apply inv_V.
  - rapply functor_pullback_homotopic.
    + intro x; apply inv_V.
    + intro x; apply inv_V.
Defined.

(** ** A constructor for textbook 3-by-3 data *)

Section PullbackThreeByThree.
  Context
    (A00 A02 A04 A20 A22 A24 A40 A42 A44 : Type)
    (f01 : A00 $-> A02) (f03 : A04 $-> A02)
    (f10 : A00 $-> A20) (f12 : A02 $-> A22) (f14 : A04 $-> A24)
    (f21 : A20 $-> A22) (f23 : A24 $-> A22)
    (f30 : A40 $-> A20) (f32 : A42 $-> A22) (f34 : A44 $-> A24)
    (f41 : A40 $-> A42) (f43 : A44 $-> A42)
    (H11 : f12 $o f01 $== f21 $o f10)
    (H13 : f12 $o f03 $== f23 $o f14)
    (H31 : f32 $o f41 $== f21 $o f30)
    (H33 : f32 $o f43 $== f23 $o f34).

  Definition pullback_3_by_3_diagram
    : Fun02 WalkingCospan (Fun02 WalkingCospan Type).
  Proof.
    snapply (fun02_walking_cospan
      (A := Fun02 WalkingCospan Type)
      (fun02_walking_cospan (A := Type) A00 A02 A04 f01 f03)
      (fun02_walking_cospan (A := Type) A20 A22 A24 f21 f23)
      (fun02_walking_cospan (A := Type) A40 A42 A44 f41 f43)).
    - snapply Build_NatTrans.
      + intro i.
        destruct i.
        * exact f10.
        * exact f12.
        * exact f14.
      + snapply Build_Is1Natural.
        intros i j h.
        destruct i, j; destruct h.
        * exact H11.
        * exact H13.
    - snapply Build_NatTrans.
      + intro i.
        destruct i.
        * exact f30.
        * exact f32.
        * exact f34.
      + snapply Build_Is1Natural.
        intros i j h.
        destruct i, j; destruct h.
        * exact H31.
        * exact H33.
  Defined.

  Definition equiv_pullback_3_by_3_fubini
    : iterated_cospan_pullback_columns pullback_3_by_3_diagram
      <~> iterated_cospan_pullback_rows pullback_3_by_3_diagram
    := equiv_iterated_cospan_pullback_fubini pullback_3_by_3_diagram.
End PullbackThreeByThree.
