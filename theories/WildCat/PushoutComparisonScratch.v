Require Import Basics.Equivalences Basics.Overture Basics.PathGroupoids
  Basics.Tactics.
Require Import Types.Paths Colimits.Pushout.
Require Import Cubical.DPath Cubical.PathSquare Cubical.DPathCube
  Cubical.PathCube.
Require Import WildCat.Core WildCat.NatTrans WildCat.FunctorCat.
Require Import WildCat.Equiv WildCat.EquivGpd WildCat.Universe.
Require Import WildCat.Cylinder WildCat.Square WildCat.Yoneda WildCat.ZeroGroupoid
  WildCat.TwoFunctor WildCat.LimitsScratch WildCat.TwoOneCat.

Set Typeclasses Depth 4.


(** * Pointwise pushouts, scratch development

    Concrete span-pushout operations copied verbatim from
    PushoutScratch.v (above the current break). *)

Definition span_pushout (X : Fun02 WalkingSpan Type)
  := Pushout
    (fmap X (a := span_center) (b := span_left) tt)
    (fmap X (a := span_center) (b := span_right) tt).

Definition span_pushout_map
  {X Y : Fun02 WalkingSpan Type} (alpha : X $-> Y)
  : span_pushout X -> span_pushout Y
  := functor_pushout
    (alpha span_center) (alpha span_left) (alpha span_right)
    (isnat alpha (a := span_center) (a' := span_left) tt)
    (isnat alpha (a := span_center) (a' := span_right) tt).

Definition span_pushout_map_homotopy
  {X Y : Fun02 WalkingSpan Type}
  {alpha beta : X $-> Y} (p : alpha $== beta)
  : span_pushout_map alpha == span_pushout_map beta.
Proof.
  snapply functor_pushout_homotopic.
  - exact (natmod_component alpha beta p span_center).
  - exact (natmod_component alpha beta p span_left).
  - exact (natmod_component alpha beta p span_right).
  - intros x.
    exact (natmod_isnatural alpha beta p
      (a := span_center) (b := span_left) tt x).
  - intros x.
    exact (natmod_isnatural alpha beta p
      (a := span_center) (b := span_right) tt x).
Defined.

Global Instance is0functor_span_pushout
  : Is0Functor span_pushout.
Proof.
  snapply Build_Is0Functor.
  exact (fun X Y alpha => span_pushout_map alpha).
Defined.

Definition span_pushout_map_id
  (X : Fun02 WalkingSpan Type)
  : span_pushout_map (Id X) == idmap
  := functor_pushout_idmap.

Definition span_pushout_map_comp
  {X Y Z : Fun02 WalkingSpan Type}
  (alpha : X $-> Y) (beta : Y $-> Z)
  : span_pushout_map (beta $o alpha)
    == span_pushout_map beta o span_pushout_map alpha.
Proof.
  transitivity (functor_pushout
    (beta span_center o alpha span_center)
    (beta span_left o alpha span_left)
    (beta span_right o alpha span_right)
    (fun x => ap (beta span_left)
      (isnat alpha (a := span_center) (a' := span_left) tt x)
      @ isnat beta (a := span_center) (a' := span_left) tt
          (alpha span_center x))
    (fun x => ap (beta span_right)
      (isnat alpha (a := span_center) (a' := span_right) tt x)
      @ isnat beta (a := span_center) (a' := span_right) tt
          (alpha span_center x))).
  { snapply functor_pushout_homotopic.
    - exact (fun _ => 1).
    - exact (fun _ => 1).
    - exact (fun _ => 1).
    - intros x.
      unfold nattrans_comp, trans_comp.
      cbn.
      rewrite !concat_1p, !concat_p1.
      reflexivity.
    - intros x.
      unfold nattrans_comp, trans_comp.
      cbn.
      rewrite !concat_1p, !concat_p1.
      reflexivity. }
  exact (functor_pushout_compose
    (alpha span_center) (alpha span_left) (alpha span_right)
    (beta span_center) (beta span_left) (beta span_right)
    (isnat alpha (a := span_center) (a' := span_left) tt)
    (isnat alpha (a := span_center) (a' := span_right) tt)
    (isnat beta (a := span_center) (a' := span_left) tt)
    (isnat beta (a := span_center) (a' := span_right) tt)).
Defined.

Global Instance is1functor_span_pushout
  : Is1Functor span_pushout.
Proof.
  snapply Build_Is1Functor.
  - intros X Y alpha beta p.
    exact (span_pushout_map_homotopy p).
  - exact span_pushout_map_id.
  - intros X Y Z alpha beta.
    exact (span_pushout_map_comp alpha beta).
Defined.

Definition fun12_span_pushout
  : Fun12 (Fun02 WalkingSpan Type) Type
  := Build_Fun12 span_pushout.

Definition pointwise_span_pushout
  {J : Type} `{IsGraph J}
  (X : Fun02 J (Fun02 WalkingSpan Type))
  : Fun02 J Type.
Proof.
  snapply Build_Fun02.
  { exact (fun j => span_pushout (X j)). }
  snapply Build_Is0Functor.
  intros i j f.
  exact (span_pushout_map (fmap X f)).
Defined.

Definition iterated_span_pushout
  (X : Fun02 WalkingSpan (Fun02 WalkingSpan Type))
  := span_pushout (pointwise_span_pushout X).

Definition iterated_span_pushout_swapped
  (X : Fun02 WalkingSpan (Fun02 WalkingSpan Type)) 
  := iterated_span_pushout
      (swap_fun02 WalkingSpan WalkingSpan Type X).

(** ** The 3-by-3 grid (copied from [Section PushoutsInType]) *)

Section CompareGrid.

  Context
    {A00 A02 A04 A20 A22 A24 A40 A42 A44 : Type}
    {f01 : A02 $-> A00} {f03 : A02 $-> A04}
    {f10 : A20 $-> A00} {f12 : A22 $-> A02} {f14 : A24 $-> A04}
    {f21 : A22 $-> A20} {f23 : A22 $-> A24}
    {f30 : A20 $-> A40} {f32 : A22 $-> A42} {f34 : A24 $-> A44}
    {f41 : A42 $-> A40} {f43 : A42 $-> A44}
    (H11 : Square f12 f10 f21 f01)
    (H13 : Square f12 f14 f23 f03)
    (H31 : Square f32 f30 f21 f41)
    (H33 : Square f32 f34 f23 f43).

  Definition manual_columns_left
    := functor_pushout f21 f01 f41
      (transpose H11) (transpose H31).

  Definition manual_columns_right
    := functor_pushout f23 f03 f43
      (transpose H13) (transpose H33).

  Definition manual_rows_left
    := functor_pushout f12 f10 f14 H11 H13.

  Definition manual_rows_right
    := functor_pushout f32 f30 f34 H31 H33.

  Definition grid_diagram
    : Fun02 WalkingSpan (Fun02 WalkingSpan Type).
  Proof.
    snapply (fun02_walking_span
      (A := Fun02 WalkingSpan Type)).
    - exact (fun02_walking_span A00 A02 A04 f01 f03).
    - exact (fun02_walking_span A20 A22 A24 f21 f23).
    - exact (fun02_walking_span A40 A42 A44 f41 f43).
    - snapply Build_NatTrans.
      { intro i.
        destruct i.
        - exact f10.
        - exact f12.
        - exact f14. }
      snapply Build_Is1Natural.
      intros i j f.
      destruct i, j; destruct f.
      + exact H11.
      + exact H13.
    - snapply Build_NatTrans.
      { intro i.
        destruct i.
        - exact f30.
        - exact f32.
        - exact f34. }
      snapply Build_Is1Natural.
      intros i j f.
      destruct i, j; destruct f.
      + exact H31.
      + exact H33.
  Defined.

  (** ** On-the-nose checks: iterated_span_pushout is manual *)

  Definition cmp_concrete_rows
    : iterated_span_pushout grid_diagram
      = Pushout manual_rows_left manual_rows_right
    := idpath.

  Definition cmp_pointwise_swapped_obj_left
    : pointwise_span_pushout
        (swap_fun02 WalkingSpan WalkingSpan Type grid_diagram)
        span_left
      = Pushout f10 f30
    := idpath.

  (** With the naturality-oriented hypotheses, the swapped iterated
      pushout is also on the nose: one [^$] from [swap_fun02_fmap]'s
      transpose, matching the manual column maps. *)
  Definition cmp_concrete_columns
    : iterated_span_pushout_swapped grid_diagram
      = Pushout manual_columns_left manual_columns_right
    := idpath.

  (** Object families: the concrete pointwise pushout at the outer
      vertices is literally the row pushouts. *)
  Definition cmp_pointwise_obj_left
    : pointwise_span_pushout grid_diagram span_left
      = Pushout f01 f03
    := idpath.

  (** Its arrow at the outer [center -> left] map is the manual row
      map. *)
  Definition cmp_concrete_map_rows
    : fmap (pointwise_span_pushout grid_diagram)
        (a := span_center) (b := span_left) tt
      = manual_rows_left
    := idpath.

End CompareGrid.

(** * Pointwise pushouts in functor categories over [Type]

    The pointwise pushout of a span of functors into [Type],
    computed by the HIT pushout at each point.  This is the manual
    corepresentative of the pushout in [Fun02 C Type]. *)

Section PointwisePushout.

  Context {C : Type} `{IsGraph C}
    (X : Fun02 WalkingSpan (Fun02 C Type)).

  Local Definition pw (c : C) : Fun02 WalkingSpan Type
    := swap_fun02 WalkingSpan C Type X c.

  (** The pointwise pushout functor: at [c], the pushout of the
      [c]-indexed span; on arrows, the induced pushout map. *)
  Definition pointwise_pushout : Fun02 C Type.
  Proof.
    snapply Build_Fun02.
    { intro c. exact (span_pushout (pw c)). }
    snapply Build_Is0Functor.
    intros c c' g.
    exact (span_pushout_map
      (fmap (swap_fun02 WalkingSpan C Type X) g)).
  Defined.

  (** The left leg at [c] is [pushl]; it is strictly natural since
      [functor_pushout] computes on [pushl]. *)
  Definition pointwise_pushout_leg_left
    : X span_left $-> pointwise_pushout.
  Proof.
    snapply Build_NatTrans.
    { intro c. exact pushl. }
    snapply Build_Is1Natural.
    intros c c' g x.
    reflexivity.
  Defined.

  Definition pointwise_pushout_leg_right
    : X span_right $-> pointwise_pushout.
  Proof.
    snapply Build_NatTrans.
    { intro c. exact pushr. }
    snapply Build_Is1Natural.
    intros c c' g x.
    reflexivity.
  Defined.

  (** The center leg is the composite of the left leg with the
      diagram arrow, following the [pushout_square_cocone]
      convention. *)
  Definition pointwise_pushout_leg_center
    : X span_center $-> pointwise_pushout
    := nattrans_comp pointwise_pushout_leg_left
        (fmap X (a := span_center) (b := span_left) tt).

End PointwisePushout.

(** * Pointwise colimits in an arbitrary codomain

    The curried form is primitive: it applies the selected [K]-colimit
    directly to each component of a [C]-indexed family.  The usual
    functor-category orientation is the same construction after one
    argument swap. *)

Section PointwiseColimitGeneric.

  Context {C : Type} `{IsGraph C} {D : Type} `{Is21Cat D}
    {K : Type} `{IsGraph K} `{!HasColimit02 D K}.

  Definition pointwise_colimit
    (X : Fun02 C (Fun02 K D)) : Fun02 C D.
  Proof.
    snapply Build_Fun02.
    { intro c. exact (cat_colimit02 D K (X c)). }
    snapply Build_Is0Functor.
    intros c c' g.
    exact (fmap (cat_colimit02 D K) (fmap X g)).
  Defined.

  Definition pointwise_colimit_in
    (X : Fun02 K (Fun02 C D)) : Fun02 C D
    := pointwise_colimit (swap_fun02 K C D X).

End PointwiseColimitGeneric.


(** ** Computation through the selected [Type] colimit instance *)

Section ChosenPushoutComputation.

  Context `{!Is1Functor (diagonal02 Type WalkingSpan)}
    (adj : GpdAdjunction fun12_span_pushout
      (fun02_diagonal Type WalkingSpan)).

  Local Instance hascolimit02_type_walking_span_probe
    : HasColimit02 Type WalkingSpan.
  Proof.
    snapply Build_HasColimit02.
    - exact fun12_span_pushout.
    - exact adj.
  Defined.

  Context
    {A00 A02 A04 A20 A22 A24 A40 A42 A44 : Type}
    {f01 : A02 $-> A00} {f03 : A02 $-> A04}
    {f10 : A20 $-> A00} {f12 : A22 $-> A02} {f14 : A24 $-> A04}
    {f21 : A22 $-> A20} {f23 : A22 $-> A24}
    {f30 : A20 $-> A40} {f32 : A22 $-> A42} {f34 : A24 $-> A44}
    {f41 : A42 $-> A40} {f43 : A42 $-> A44}
    (H11 : Square f12 f10 f21 f01)
    (H13 : Square f12 f14 f23 f03)
    (H31 : Square f32 f30 f21 f41)
    (H33 : Square f32 f34 f23 f43).

  Local Definition chosen_pointwise_rows
    : Fun02 WalkingSpan Type
    := pointwise_colimit
      (grid_diagram H11 H13 H31 H33).

  Definition cmp_chosen_pointwise_rows
    : chosen_pointwise_rows
      = pointwise_span_pushout
          (grid_diagram H11 H13 H31 H33)
    := idpath.

  Local Definition chosen_rows : Type
    := cat_colimit02 Type WalkingSpan chosen_pointwise_rows.

  Definition cmp_chosen_rows
    : chosen_rows
      = Pushout
          (manual_rows_left H11 H13)
          (manual_rows_right H31 H33)
    := idpath.

  Local Definition chosen_pointwise_columns
    : Fun02 WalkingSpan Type
    := pointwise_colimit
      (swap_fun02 WalkingSpan WalkingSpan Type
        (grid_diagram H11 H13 H31 H33)).

  Definition cmp_chosen_pointwise_columns
    : chosen_pointwise_columns
      = pointwise_span_pushout
          (swap_fun02 WalkingSpan WalkingSpan Type
            (grid_diagram H11 H13 H31 H33))
    := idpath.

  Local Definition chosen_columns : Type
    := cat_colimit02 Type WalkingSpan chosen_pointwise_columns.

  Definition cmp_chosen_columns
    : chosen_columns
      = Pushout
          (manual_columns_left H11 H31)
          (manual_columns_right H13 H33)
    := idpath.

End ChosenPushoutComputation.
