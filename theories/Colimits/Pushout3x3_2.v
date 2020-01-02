Require Import Basics.
Require Import Types.
Require Import Pushout.
Require Import Pullback.
Require Import Yoneda.
Require Import Pullback3x3.

(* The 3x3 Diagram looks like the following:

    A00 <--- A02 ---> A04
     ^     // ^ \\     ^
     |    //  |  \\    |
     |   //   |   \\   |
    A20 <--- A22 ---> A24
     |   \\   |   //   |
     |    \\  |  //    |
     V     \\ V //     V
    A40 <--- A42 ---> A44

The labels look like this:

    A00 f01 A02 f03 A04
    f10 H11 f12 H13 f14
    A20 f21 A22 f23 A24
    f30 H31 f32 H33 f34
    A40 f41 A42 f43 A44 *)

Section Pushout3x3.

  Context `{Funext}
    (A00 A02 A04 A20 A22 A24 A40 A42 A44 : Type)
    (f01 : A02 -> A00) (f03 : A02 -> A04)
    (f10 : A20 -> A00) (f12 : A22 -> A02) (f14 : A24 -> A04)
    (f21 : A22 -> A20) (f23 : A22 -> A24)
    (f30 : A20 -> A40) (f32 : A22 -> A42) (f34 : A24 -> A44)
    (f41 : A42 -> A40) (f43 : A42 -> A44)
    (H11 : f01 o f12 == f10 o f21) (H13 : f03 o f12 == f14 o f23)
    (H31 : f41 o f32 == f30 o f21) (H33 : f43 o f32 == f34 o  f23).

  Local Definition AX0 := Pushout f10 f30.
  Local Definition AX2 := Pushout f12 f32.
  Local Definition AX4 := Pushout f14 f34.

  Local Definition fX1
    := functor_pushout f21 f01 f41 H11 H31.

  Local Definition fX3
    := functor_pushout f23 f03 f43 H13 H33.

  Local Definition AXO := Pushout fX1 fX3.

  Local Definition A0X := Pushout f01 f03.
  Local Definition A2X := Pushout f21 f23.
  Local Definition A4X := Pushout f41 f43.

  Local Definition f1X
    := functor_pushout f12 f10 f14 (symmetry _ _ H11) (symmetry _ _ H13).

  Local Definition f3X
    := functor_pushout f32 f30 f34 (symmetry _ _ H31) (symmetry _ _ H33).

  Local Definition AOX := Pushout f1X f3X.

  Lemma part1 : forall X : Type, (AXO -> X) <~> (AOX -> X).
  Proof.
    intro X.
    refine (equiv_pullback_pushout^-1 oE _ oE equiv_pullback_pushout).
    
    refine (_^-1 oE _ oE _).
    { serapply equiv_pullback.
      6-8: serapply equiv_pullback_pushout.
      { serapply functor_pullback.
        + intros f a.
          exact (f (f12 a)).
        + intros f a.
          exact (f (f10 a)).
        + intros f a.
          exact (f (f14 a)).
        + symmetry.
          intro f; apply path_forall.
          exact (pointwise_paths_postwhisker f H11).
        + symmetry.
          intro f; apply path_forall.
          exact (pointwise_paths_postwhisker f H13). }
      { serapply functor_pullback.
        + intros f a.
          exact (f (f32 a)).
        + intros f a.
          exact (f (f30 a)).
        + intros f a.
          exact (f (f34 a)).
        + symmetry.
          intro f; apply path_forall.
          exact (pointwise_paths_postwhisker f H31).
        + symmetry.
          intro f; apply path_forall.
          exact (pointwise_paths_postwhisker f H33). }
      { simpl.
        intros f.
        unfold functor_pullback.
        unfold functor_sigma.
        simpl.
        serapply path_sigma'.
        1: reflexivity.
        serapply path_sigma'.
        1: reflexivity.
        simpl.
        Import Cubical.
        Arguments path_forall {_ _ _ _ _}.
        rewrite inv_V.
        rewrite concat_pp_p.
        apply moveR_Vp.
        apply sq_path^-1.
        refine (sq_cGcc _^ _).
        { apply ap.
          apply path_forall.
          intro x.
          refine (ap_compose _ _ _ @ _).
          refine (ap (ap f) _ @ _).
          1: apply Pushout_rec_beta_pglue.
          refine (ap_pp _ _ _ @ _).
          rewrite ap_pp.
          rewrite <- ap_compose.
          rewrite <- (ap_compose pushr).
          unfold symmetry.
          simpl.
          rewrite inv_V.
          rewrite ap_V.
          reflexivity. }
        unfold pointwise_paths_postwhisker.
        rewrite 2 path_forall_pp.
        apply sq_path.
        rewrite 2 concat_p_pp.
        apply (ap (fun x => x @ _)).
        rewrite path_forall_V.
        rewrite concat_pV.
        rewrite concat_1p.
        change (fun (f0 : A02 -> X) (a : A22) => f0 (f12 a))
          with (@functor_arrow A22 A02 f12 X X idmap).
        rewrite ap_functor_arrow.
        apply ap.
        apply path_forall.
        intro x.
        apply ap_idmap. }
{ simpl.
        intros f.
        unfold functor_pullback.
        unfold functor_sigma.
        simpl.
        serapply path_sigma'.
        1: reflexivity.
        serapply path_sigma'.
        1: reflexivity.
        simpl.
        Import Cubical.
        Arguments path_forall {_ _ _ _ _}.
        rewrite inv_V.
        rewrite concat_pp_p.
        apply moveR_Vp.
        apply sq_path^-1.
        refine (sq_cGcc _^ _).
        { apply ap.
          apply path_forall.
          intro x.
          refine (ap_compose _ _ _ @ _).
          refine (ap (ap f) _ @ _).
          1: apply Pushout_rec_beta_pglue.
          refine (ap_pp _ _ _ @ _).
          rewrite ap_pp.
          rewrite <- ap_compose.
          rewrite <- (ap_compose pushr).
          unfold symmetry.
          simpl.
          rewrite inv_V.
          rewrite ap_V.
          reflexivity. }
        unfold pointwise_paths_postwhisker.
        rewrite 2 path_forall_pp.
        apply sq_path.
        rewrite 2 concat_p_pp.
        apply (ap (fun x => x @ _)).
        rewrite path_forall_V.
        rewrite concat_pV.
        rewrite concat_1p.
        change (fun (f0 : A42 -> X) (a : A22) => f0 (f32 a))
          with (@functor_arrow A22 A42 f32 X X idmap).
        rewrite ap_functor_arrow.
        apply ap.
        apply path_forall.
        intro x.
        apply ap_idmap. } }
    1: shelve.
    
    { serapply equiv_pullback.
      6-8: serapply equiv_pullback_pushout.
      { serapply functor_pullback.
        + intros f a.
          exact (f (f21 a)).
        + intros f a.
          exact (f (f01 a)).
        + intros f a.
          exact (f (f41 a)).
        + intro f; apply path_forall.
          exact (pointwise_paths_postwhisker f H11).
        + intro f; apply path_forall.
          exact (pointwise_paths_postwhisker f H31). }
      { serapply functor_pullback.
        + intros f a.
          exact (f (f23 a)).
        + intros f a.
          exact (f (f03 a)).
        + intros f a.
          exact (f (f43 a)).
        + intro f; apply path_forall.
          exact (pointwise_paths_postwhisker f H13).
        + intro f; apply path_forall.
          exact (pointwise_paths_postwhisker f H33). }
      { simpl.
        intros f.
        unfold functor_pullback.
        unfold functor_sigma.
        simpl.
        serapply path_sigma'.
        1: reflexivity.
        serapply path_sigma'.
        1: reflexivity.
        simpl.
        Import Cubical.
        Arguments path_forall {_ _ _ _ _}.
        apply moveR_pV.
        apply sq_path^-1.
        refine (sq_ccGc _^ _).
        { apply ap.
          apply path_forall.
          intro x.
          refine (ap_compose _ _ _ @ _).
          refine (ap (ap f) _ @ _).
          1: apply Pushout_rec_beta_pglue.
          refine (ap_pp _ _ _ @ _).
          rewrite ap_pp.
          rewrite <- ap_compose.
          rewrite <- (ap_compose pushr).
          rewrite ap_V.
          reflexivity. }
        unfold pointwise_paths_postwhisker.
        rewrite 2 path_forall_pp.
        apply sq_path.
        rewrite 2 concat_pp_p.
        apply ap.
        rewrite path_forall_V.
        rewrite concat_Vp.
        rewrite concat_p1.
        change (fun (f0 : A20 -> X) (a : A22) => f0 (f21 a))
          with (@functor_arrow A22 A20 f21 X X idmap).
        rewrite ap_functor_arrow.
        apply ap.
        apply path_forall.
        intro x.
        apply ap_idmap. }
      { simpl.
        intros f.
        unfold functor_pullback.
        unfold functor_sigma.
        simpl.
        serapply path_sigma'.
        1: reflexivity.
        serapply path_sigma'.
        1: reflexivity.
        simpl.
        Import Cubical.
        Arguments path_forall {_ _ _ _ _}.
        apply moveR_pV.
        apply sq_path^-1.
        refine (sq_ccGc _^ _).
        { apply ap.
          apply path_forall.
          intro x.
          refine (ap_compose _ _ _ @ _).
          refine (ap (ap f) _ @ _).
          1: apply Pushout_rec_beta_pglue.
          refine (ap_pp _ _ _ @ _).
          rewrite ap_pp.
          rewrite <- ap_compose.
          rewrite <- (ap_compose pushr).
          rewrite ap_V.
          reflexivity. }
        unfold pointwise_paths_postwhisker.
        rewrite 2 path_forall_pp.
        apply sq_path.
        rewrite 2 concat_pp_p.
        apply ap.
        rewrite path_forall_V.
        rewrite concat_Vp.
        rewrite concat_p1.
        change (fun (f0 : A24 -> X) (a : A22) => f0 (f23 a))
          with (@functor_arrow A22 A24 f23 X X idmap).
        rewrite ap_functor_arrow.
        apply ap.
        apply path_forall.
        intro x.
        apply ap_idmap. } }
    Unshelve.
    serapply (pullback3x3 _ _ _ _ _ _ _ _ _ _).
  Defined.

  Lemma part2 (X Y : Type) (f : X -> Y)
    : (fun g : AOX -> X => f o g) o part1 X
    == part1 Y o (fun h : AXO -> X => f o h).
  Proof.
    intro g.
    funext x.
    unfold part1.
  Admitted.

  Theorem pushout3x3 : AXO <~> AOX.
  Proof.
    serapply yoneda.
    1: apply part1.
    apply part2.
  Defined.



