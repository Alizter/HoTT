Require Import Basics.Equivalences Basics.Overture Basics.PathGroupoids
  Basics.Tactics.
Require Import Limits.Pullback.
Require Import WildCat.Core WildCat.Equiv WildCat.Limits WildCat.NatTrans
  WildCat.PointwiseLimitUniversal WildCat.PullbackLimitScratch
  WildCat.SwapAdjunction WildCat.TwoFunctor WildCat.TwoOneCat
  WildCat.Universe WildCat.FunctorCat WildCat.OneGroupoid WildCat.EquivGpd WildCat.TwoYoneda.

Set Typeclasses Depth 4.

(** * General limit Fubini and the pullback 3-by-3 test case *)

(** ** The general theorem we want *)

Section GeneralLimitFubini.
  Context {A I J : Type} `{Is21Cat A, IsGraph I, IsGraph J}.
  Context `{!HasEquivs A, !HasLimits I A, !HasLimits J A}.

  Definition limit_fubini_statement
    (X : Fun02 J (Fun02 I A)) : Type
    := cat_limit I (pointwise_limit_apex I A J X)
      $<~> cat_limit J
        (pointwise_limit_apex J A I (swap_fun02 J I A X)).
End GeneralLimitFubini.

(** This is the only theorem assumed by the application below.  Its proof is
    the general Fubini development, not part of the walking-cospan instance. *)
Axiom limit_fubini
  : forall {A I J : Type} `{Is21Cat A, IsGraph I, IsGraph J}
      `{!HasEquivs A, !HasLimits I A, !HasLimits J A}
      (X : Fun02 J (Fun02 I A)),
    limit_fubini_statement X.

(** ** Ordinary pullbacks populate walking-cospan limits in [Type] *)

Definition cospan_left_map (X : Fun02 WalkingCospan Type)
  : X cospan_left -> X cospan_center
  := fmap X (a := cospan_left) (b := cospan_center) tt.

Definition cospan_right_map (X : Fun02 WalkingCospan Type)
  : X cospan_right -> X cospan_center
  := fmap X (a := cospan_right) (b := cospan_center) tt.

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

(** First local proof obligation: [equiv_pullback_corec] supplies this
    universal property. *)
Definition cospan_pullback_islimit (D : Fun02 WalkingCospan Type)
  : IsLimitCone D (cospan_pullback_apex D) (cospan_pullback_cone D).
Proof.
  intros Y.
  simpl.
  stapply isequiv_1gpd_issurjinj.
  - intros eta.
    eexists (cospan_pullback_corec D Y eta).
    stapply Build_NatModification.
    + intros [ | | ].
      * reflexivity.
      * simpl.
        admit.
      * reflexivity.
    + 

    

  .
Admitted.

Definition cospan_pullback_limit
  (X : Fun02 WalkingCospan Type) : Limit WalkingCospan X.
Proof.
  snapply Build_Limit.
  - exact (cospan_pullback_apex X).
  - exact (cospan_pullback_cone X).
  - exact (cospan_pullback_islimit X).
Defined.

Global Instance haslimits_walking_cospan_type
  : HasLimits WalkingCospan Type
  := fun X => cospan_pullback_limit X.

(** ** The pullback 3-by-3 application *)

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

  Let fX1 := functor_pullback
    f10 f30 f12 f32 f21 f01 f41 H11 H31.
  Let fX3 := functor_pullback
    f14 f34 f12 f32 f23 f03 f43 H13 H33.
  Let f1X := functor_pullback
    f01 f03 f21 f23 f12 f10 f14
    (symmetry _ _ H11) (symmetry _ _ H13).
  Let f3X := functor_pullback
    f41 f43 f21 f23 f32 f30 f34
    (symmetry _ _ H31) (symmetry _ _ H33).

  Local Definition pullback_3_by_3_diagram
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

  Local Definition columnwise_limits : Fun02 WalkingCospan Type
    := pointwise_limit_apex WalkingCospan Type WalkingCospan
      pullback_3_by_3_diagram.

  Local Definition rowwise_limits : Fun02 WalkingCospan Type
    := pointwise_limit_apex WalkingCospan Type WalkingCospan
      (swap_fun02 WalkingCospan WalkingCospan Type
        pullback_3_by_3_diagram).

  Local Definition iterated_column_limit : Type
    := cat_limit WalkingCospan columnwise_limits.

  Local Definition iterated_row_limit : Type
    := cat_limit WalkingCospan rowwise_limits.

  (** These are the two concrete comparison obligations left after applying
      general Fubini. *)
  Definition columnwise_pullback_comparison_statement
    : iterated_column_limit <~> Pullback fX1 fX3.
  Proof.

  Admitted.

  Definition rowwise_pullback_comparison_statement
    : iterated_row_limit <~> Pullback f1X f3X.
  Proof.
  Admitted.

  Definition pullback_3_by_3_from_limit_fubini
    : Pullback fX1 fX3 <~> Pullback f1X f3X
    := rowwise_pullback_comparison_statement 
      oE limit_fubini pullback_3_by_3_diagram
      oE equiv_inverse columnwise_pullback_comparison_statement.
End PullbackThreeByThree.
