Require Import Basics.Equivalences Basics.Overture Basics.PathGroupoids
  Basics.Tactics.
Require Import Limits.Pullback.
Require Import WildCat.Adjoint WildCat.Core WildCat.Cylinder WildCat.Equiv
  WildCat.EquivGpd WildCat.FunctorCat WildCat.Limits WildCat.NatTrans
  WildCat.OneGroupoid WildCat.Square WildCat.TwoFunctor WildCat.TwoOneCat
  WildCat.Universe WildCat.Yoneda WildCat.ZeroGroupoid.

Set Typeclasses Depth 4.

(** * Pullbacks as walking-cospan limits *)

Inductive WalkingCospan :=
  | cospan_left
  | cospan_center
  | cospan_right.

Definition walking_cospan_hom (i j : WalkingCospan) : Type
  := match i, j with
     | cospan_left, cospan_center
     | cospan_right, cospan_center => Unit
     | _, _ => Empty
     end.

Global Instance isgraph_walking_cospan : IsGraph WalkingCospan
  := Build_IsGraph WalkingCospan walking_cospan_hom.

Definition fun02_walking_cospan
  {A : Type} `{IsGraph A}
  (left center right : A)
  (f : left $-> center) (g : right $-> center)
  : Fun02 WalkingCospan A.
Proof.
  snapply Build_Fun02.
  - intro i.
    destruct i.
    + exact left.
    + exact center.
    + exact right.
  - snapply Build_Is0Functor.
    intros i j h.
    destruct i, j; destruct h.
    + exact f.
    + exact g.
Defined.

(** ** The canonical pullback functor in [Type] *)

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

Definition cospan_pullback_map
  {X Y : Fun02 WalkingCospan Type} (alpha : X $-> Y)
  : cospan_pullback_apex X -> cospan_pullback_apex Y
  := functor_pullback
      (cospan_left_map X) (cospan_right_map X)
      (cospan_left_map Y) (cospan_right_map Y)
      (alpha cospan_center) (alpha cospan_left) (alpha cospan_right)
      (fun x => (cospan_left_naturality alpha x)^)
      (fun x => (cospan_right_naturality alpha x)^).

Definition cospan_pullback_map_homotopy_coherence
  {X Y : Fun02 WalkingCospan Type}
  {alpha beta : X $-> Y} (p : alpha $== beta)
  (x : cospan_pullback_apex X)
  : ap (cospan_left_map Y)
      (natmod_component alpha beta p cospan_left x.1)
      @ (cospan_pullback_map beta x).2.2
    = (cospan_pullback_map alpha x).2.2
      @ ap (cospan_right_map Y)
        (natmod_component alpha beta p cospan_right x.2.1).
Proof.
  destruct x as [xl [xr xglue]].
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
  - exact (cospan_pullback_map_homotopy_coherence p).
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

(** ** Unit, counit, and the induced hom-0-groupoid adjunction *)

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
  - intro i.
    destruct i.
    + intro x; reflexivity.
    + intro x.
      exact (isnat alpha (a := cospan_left)
        (a' := cospan_center) tt x.1)^.
    + intro x; reflexivity.
  - intros i j f.
    destruct i, j; destruct f; cbn beta.
    + intros [xl [xr xglue]].
      unfold Cylinder, Square.
      cbn.
      rewrite !concat_1p, !concat_p1, concat_Vp.
      reflexivity.
    + intros [xl [xr xglue]].
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
  - exact cospan_pullback_counit_component.
  - snapply Build_Is1Natural.
    intros X Y alpha.
    exact (cospan_pullback_counit_naturality alpha).
Defined.

Definition cospan_pullback_unit_component (P : Type)
  : P -> cospan_pullback_apex
      (diagonal02 Type WalkingCospan P)
  := fun x => (x; (x; 1)).

Definition cospan_pullback_unit_naturality
  {P Q : Type} (f : P -> Q)
  : cospan_pullback_unit_component Q o f
    == cospan_pullback_map
      (fmap (diagonal02 Type WalkingCospan) f)
      o cospan_pullback_unit_component P.
Proof.
  intro x.
  unfold cospan_pullback_unit_component.
  unfold cospan_pullback_map, functor_pullback.
  cbn beta.
  unfold Sigma.functor_sigma.
  cbn beta.
  cbn.
  reflexivity.
Defined.

Definition nattrans_cospan_pullback_unit
  : NatTrans idmap
      (cospan_pullback_apex o diagonal02 Type WalkingCospan).
Proof.
  snapply Build_NatTrans.
  - exact cospan_pullback_unit_component.
  - snapply Build_Is1Natural.
    intros P Q f.
    exact (cospan_pullback_unit_naturality f).
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
  - intro i.
    destruct i; intro x; reflexivity.
  - intros i j f.
    destruct i, j; destruct f; cbn beta.
    + intro x.
      unfold Cylinder, Square.
      cbn.
      reflexivity.
    + intro x.
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
  { exact (is1functor_diagonal02_generic Type WalkingCospan). }
  exact is1functor_cospan_pullback_apex.
Defined.

Global Instance haslimit02_type_walking_cospan
  : HasLimit02 WalkingCospan Type.
Proof.
  snapply Build_HasLimit02.
  - exact fun12_cospan_pullback.
  - exact gpd_adjunction_cospan_pullback.
Defined.

Definition cospan_pullback_islimit02
  (D : Fun02 WalkingCospan Type)
  : IsLimitCone02 D (cospan_pullback_apex D) (cospan_pullback_cone D).
Proof.
  pose (H := cat_limit02_cone_islimit WalkingCospan Type D).
  cbn [cat_limit02 haslimit02_type_walking_cospan] in H.
  napply (islimitcone02_homotopic _ H).
  unfold cat_limit02_cone, limit02_cone_of_islimit, cat_limit02_islimit.
  change (NatModification
    (A := WalkingCospan) (B := Type)
    (nattrans_comp
      (cospan_pullback_counit_component D)
      (fmap (diagonal02 Type WalkingCospan)
        (Id (cospan_pullback_apex D))))
    (cospan_pullback_counit_component D)).
  snapply Build_NatModification.
  - intro i.
    destruct i; intro x; reflexivity.
  - intros i j f.
    destruct i, j; destruct f; cbn beta.
    + intro x.
      unfold Cylinder, Square.
      cbn.
      reflexivity.
    + intro x.
      unfold Cylinder, Square.
      cbn.
      rewrite !concat_1p, !concat_p1.
      reflexivity.
Defined.
