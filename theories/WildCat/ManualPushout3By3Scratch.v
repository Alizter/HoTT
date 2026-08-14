Require Import Basics.Overture Basics.Tactics.
Require Import Colimits.Pushout.
Require Import WildCat.Core WildCat.Equiv WildCat.FunctorCat
  WildCat.LimitsScratch WildCat.NatTrans WildCat.Square
  WildCat.TwoFunctor WildCat.TwoOneCat WildCat.Universe
  WildCat.ZeroGroupoid.
Require Import WildCat.PushoutScratch.
Require Import WildCat.PushoutComparisonScratch.

Set Typeclasses Depth 4.


(** * The concrete pushout 3-by-3 statement in [Type] *)

Section ManualPushoutThreeByThree.

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


  Definition pointwise_columns_three_by_three
    : IsPointwiseColimitCocone02
        Type WalkingSpan WalkingSpan
        (grid_diagram H11 H13 H31 H33)
        (pointwise_span_pushout
          (grid_diagram H11 H13 H31 H33)).
  Proof.
  Admitted.

  Definition pointwise_rows_three_by_three
    : IsPointwiseColimitCocone02
        Type WalkingSpan WalkingSpan
        (swap_fun02 WalkingSpan WalkingSpan Type
          (grid_diagram H11 H13 H31 H33))
        (pointwise_span_pushout
          (swap_fun02 WalkingSpan WalkingSpan Type
            (grid_diagram H11 H13 H31 H33))).
  Proof.
  Admitted.

  Definition isdoublecols_three_by_three
    : IsDoubleColimitColumns Type WalkingSpan WalkingSpan
        (grid_diagram H11 H13 H31 H33)
        (iterated_span_pushout
          (grid_diagram H11 H13 H31 H33)).
  Proof.
    exact (isdoublecolimitcolumns_of_pointwise_colimit
      Type WalkingSpan WalkingSpan
      (grid_diagram H11 H13 H31 H33)
      (pointwise_span_pushout
        (grid_diagram H11 H13 H31 H33))
      pointwise_columns_three_by_three
      (iterated_span_pushout
        (grid_diagram H11 H13 H31 H33))
      (span_pushout_iscolimit
        (pointwise_span_pushout
          (grid_diagram H11 H13 H31 H33)))).
  Defined.

  Definition isdoublerows_three_by_three
    : IsDoubleColimitRows Type WalkingSpan WalkingSpan
        (grid_diagram H11 H13 H31 H33)
        (iterated_span_pushout_swapped
          (grid_diagram H11 H13 H31 H33)).
  Proof.
    exact (isdoublecolimitrows_of_pointwise_colimit
      Type WalkingSpan WalkingSpan
      (grid_diagram H11 H13 H31 H33)
      (pointwise_span_pushout
        (swap_fun02 WalkingSpan WalkingSpan Type
          (grid_diagram H11 H13 H31 H33)))
      pointwise_rows_three_by_three
      (iterated_span_pushout_swapped
        (grid_diagram H11 H13 H31 H33))
      (span_pushout_iscolimit
        (pointwise_span_pushout
          (swap_fun02 WalkingSpan WalkingSpan Type
            (grid_diagram H11 H13 H31 H33))))).
  Defined.


  Definition three_by_three
    : Pushout
        (functor_pushout f21 f01 f41
          (transpose H11) (transpose H31))
        (functor_pushout f23 f03 f43
          (transpose H13) (transpose H33))
      $<~>
      Pushout
        (functor_pushout f12 f10 f14 H11 H13)
        (functor_pushout f32 f30 f34 H31 H33).
  Proof.
    change
      (iterated_span_pushout_swapped
          (grid_diagram H11 H13 H31 H33)
        $<~>
        iterated_span_pushout
          (grid_diagram H11 H13 H31 H33)).
    exact (cate_inv
      (equiv_colimit_fubini
        Type WalkingSpan WalkingSpan
        (grid_diagram H11 H13 H31 H33)
        isdoublerows_three_by_three
        isdoublecols_three_by_three)).
  Defined.

End ManualPushoutThreeByThree.
