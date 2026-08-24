Require Import Basics.Equivalences Basics.Overture Basics.PathGroupoids
  Basics.Tactics.
Require Import Limits.Pullback.
Require Import WildCat.Core WildCat.Equiv WildCat.EquivGpd WildCat.Limits
  WildCat.NatTrans WildCat.OneGroupoid WildCat.TwoFunctor
  WildCat.TwoOneCat WildCat.Universe WildCat.ZeroGroupoid.

Set Typeclasses Depth 4.

(** * Type pullbacks as walking-cospan limits *)

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

Section PullbackCone.
  Context {left center right : Type}
    (f : left -> center) (g : right -> center).

  Definition type_pullback_cone
    : diagonal02 Type WalkingCospan (Pullback f g) $->
      fun02_walking_cospan left center right f g.
  Proof.
    snapply Build_NatTrans.
    - intro i.
      destruct i.
      + exact pullback_pr1.
      + exact (f o pullback_pr1).
      + exact pullback_pr2.
    - snapply Build_Is1Natural.
      intros i j h.
      destruct i, j; destruct h.
      + intro x. exact 1.
      + intro x. exact x.2.2.
  Defined.

  Definition type_pullback_islimit_statement : Type
    := IsLimitCone
      (fun02_walking_cospan left center right f g)
      (Pullback f g) type_pullback_cone.
End PullbackCone.
