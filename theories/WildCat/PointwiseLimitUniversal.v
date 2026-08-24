Require Import Basics.Overture Basics.Tactics.
Require Import WildCat.Core WildCat.Equiv WildCat.FunctorCat WildCat.Limits
  WildCat.NatTrans WildCat.OneGroupoid WildCat.Square WildCat.TwoFunctor
  WildCat.TwoOneCat WildCat.TwoYoneda.
Require Import WildCat.PointwiseLimitCorec.

(** * Universality of pointwise limits

    The componentwise eta cells from [PointwiseLimitCorec] are natural in the
    mapping 1-groupoid.  Together with beta, this packages the assembled
    pointwise cone as an [IsLimitCone] and supplies limits in coherent functor
    categories. *)

Set Typeclasses Depth 4.



Section PointwiseLimitEta.
  Context (I A J : Type) `{IsGraph I, Is21Cat A, IsGraph J}.
  Context `{!HasLimits J A}.

  Definition pointwise_limit_eta
    (X : Fun02 J (Fun02 I A)) (P : Fun02 I A)
    : fun11_compose
        (pointwise_limit_corec_fun11 I A J X P)
        (limit_cone_map X
          (pointwise_limit_apex I A J X)
          (pointwise_limit_cone I A J X) P)
      $== Id (hom_1gpd P (pointwise_limit_apex I A J X)).
  Proof.
    snapply Build_NatTrans.
    - exact (pointwise_limit_eta_modification I A J X P).
    - snapply Build_Is1Natural.
      intros k l p.
      intro i.
      pose (Fglobal := limit_cone_map X
        (pointwise_limit_apex I A J X)
        (pointwise_limit_cone I A J X) P).
      pose (q := fun11_fmap Fglobal p).
      pose (c := isnat (pointwise_limit_beta I A J X P) q).
      cbn.
      pose (D := pointwise_limit_diagram I A J X i).
      pose (Flocal := limit_cone_map D
        (pointwise_limit_apex I A J X i)
        (cat_limit_cone J D) (P i)).
      pose (HF := limit_cone_biinv_direct
        (cat_limit_cone J D) (cat_islimit_cone J D) (P i)).
      pose (compk :=
        pointwise_limit_cone_map_comparison I A J X P k i).
      pose (compl :=
        pointwise_limit_cone_map_comparison I A J X P l i).
      pose (r := natmod_component _ _
        (pointwise_limit_local_cones_modification I A J q) i).
      assert (d : Square r
        (fun11_fmap Flocal (natmod_component k l p i))
        compk compl).
      {
        napply Build_NatModificationSquare.
        intro j.
        rewrite natmod_cat_comp_component.
        rewrite natmod_cat_comp_component.
        pose (ek :=
          pointwise_limit_cone_map_comparison_component
            I A J X P k i j).
        pose (el :=
          pointwise_limit_cone_map_comparison_component
            I A J X P l i j).
        nrefine (vconcatR (vconcatL ek _) el).
        napply Build_Square.
        lhs' exact (cat_idr _).
        rhs' exact (cat_idl _).
        unfold Flocal, r, q, Fglobal.
        cbn.
        reflexivity.
      }
      napply (fun11_fmap_bireflect_2cell Flocal HF).
      lhs' exact (fmap_comp Flocal _ _).
      rhs' exact (fmap_comp Flocal _ _).
      pose (sk :=
        limit_beta_direct D
          (pointwise_limit_local_cones I A J (Fglobal k) i)
        $@ pointwise_limit_cone_map_comparison I A J X P k i).
      pose (sl :=
        limit_beta_direct D
          (pointwise_limit_local_cones I A J (Fglobal l) i)
        $@ pointwise_limit_cone_map_comparison I A J X P l i).
      lhs' exact ((fun11_fmap_bireflect Flocal HF sl)
        $@R _).
      rhs' exact (_ $@L
        fun11_fmap_bireflect Flocal HF sk).
      pose (betak := limit_beta_direct D
        (pointwise_limit_local_cones I A J (Fglobal k) i)).
      pose (betal := limit_beta_direct D
        (pointwise_limit_local_cones I A J (Fglobal l) i)).
      pose (b := limit_beta_direct_naturality D r).
      unfold sl, sk.
      lhs' exact (cat_assoc _ _ _).
      lhs' exact (compl $@L b^$).
      lhs' exact (cat_assoc_opp _ _ _).
      lhs' exact (d^$ $@R betak).
      exact (cat_assoc _ _ _).
  Defined.

  Definition pointwise_limit_islimitcone
    (X : Fun02 J (Fun02 I A))
    : IsLimitCone X
        (pointwise_limit_apex I A J X)
        (pointwise_limit_cone I A J X).
  Proof.
    intro P.
    snapply Build_Cat_IsBiInv.
    - exact (pointwise_limit_corec_fun11 I A J X P).
    - exact (pointwise_limit_beta I A J X P).
    - exact (pointwise_limit_corec_fun11 I A J X P).
    - exact (pointwise_limit_eta X P).
  Defined.

  Definition pointwise_limit
    (X : Fun02 J (Fun02 I A)) : Limit J X.
  Proof.
    snapply Build_Limit.
    - exact (pointwise_limit_apex I A J X).
    - exact (pointwise_limit_cone I A J X).
    - exact (pointwise_limit_islimitcone X).
  Defined.

  Global Instance haslimits_fun02
    : HasLimits J (Fun02 I A)
    := fun X => pointwise_limit X.
End PointwiseLimitEta.
