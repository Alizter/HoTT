Require Import Basics.Overture Basics.PathGroupoids Basics.Tactics.
Require Import WildCat.Adjoint WildCat.Core WildCat.Cylinder WildCat.Equiv
  WildCat.FunctorCat WildCat.Limits WildCat.NatTrans WildCat.Square
  WildCat.SwapAdjunction WildCat.TwoFunctor WildCat.TwoOneCat.

Set Typeclasses Depth 4.

(** A coherent limit adjunction is the higher structure needed to lift chosen
    limits through coherent functor categories. *)
Class HasLimit22
  (J A : Type) `{IsGraph J, Is21Cat A} := {
  cat_limit22 : Fun22 (Fun02 J A) A;
  cubical_adjunction_cat_limit22
    : CubicalAdjunction (fun22_diagonal02 A J) cat_limit22;
}.

Section PointwiseLimitAdjunction.
  Context (I A J : Type) `{IsGraph I, Is21Cat A, IsGraph J}.
  Context `{!HasLimit22 J A}.

  Definition fun12_pointwise_limit22
    : Fun12 (Fun02 J (Fun02 I A)) (Fun02 I A)
    := fun12_compose
      (fun12_fun02_postcomp (A := I)
        (cat_limit22 (J := J) (A := A)))
      (fun12_swap_fun02 J I A).

  Definition fun12_pointwise_diagonal
    : Fun12 (Fun02 I A) (Fun02 J (Fun02 I A))
    := fun12_compose
      (fun12_swap_fun02 I J A)
      (fun12_fun02_postcomp (A := I) (fun22_diagonal02 A J)).

  Definition gpd_adjunction_pointwise_limit22
    : GpdAdjunction fun12_pointwise_diagonal fun12_pointwise_limit22.
  Proof.
    exact (gpd_adjunction_compose
      (Fun02 I A)
      (Fun02 I (Fun02 J A))
      (Fun02 J (Fun02 I A))
      (fun11_fun12
        (fun12_fun02_postcomp (A := I) (fun22_diagonal02 A J)))
      (fun11_fun12
        (fun12_fun02_postcomp (A := I)
          (cat_limit22 (J := J) (A := A))))
      (fun11_fun12 (fun12_swap_fun02 I J A))
      (fun11_fun12 (fun12_swap_fun02 J I A))
      (gpd_adjunction_fun02_postcomp_cubical
        A (Fun02 J A) I
        (fun22_diagonal02 A J)
        (cat_limit22 (J := J) (A := A))
        (cubical_adjunction_cat_limit22 (J := J) (A := A)))
      (gpd_adjunction_swap_fun02 I J A)).
  Defined.
End PointwiseLimitAdjunction.

(** The swapped pointwise diagonal is naturally equivalent to the actual
    diagonal in the coherent functor category. *)
Section PointwiseDiagonalComparison.
  Context (I A J : Type) `{IsGraph I, Is21Cat A, IsGraph J}.

  Local Definition transpose_hrefl_vrefl
    {a b : A} (h : a $-> b)
    : transpose (hrefl h) $== vrefl h.
  Proof.
    cbv [transpose hrefl vrefl].
    exact (gpd_rev_pp ((cat_idl h)^$) (cat_idr h)
      $@ ((cat_idr h)^$ $@L gpd_rev_rev (cat_idl h))).
  Defined.

  Definition pointwise_diagonal_component (F : Fun02 I A)
    : fun12_pointwise_diagonal I A J F
      $-> fun22_diagonal02 (Fun02 I A) J F.
  Proof.
    snapply Build_NatTrans.
    { intro j. exact (Id F). }
    snapply Build_Is1Natural.
    intros j j' g.
    snapply Build_NatModification.
    { intro i. exact (Id _). }
    intros i i' f.
    cbn.
    exact (cylinder_rewrite_front
      (s0' := transpose (hrefl (fmap F f)) $@v vrefl (fmap F f))
      (square_vconcat_natural_above
        (transpose_hrefl_vrefl (fmap F f))
        (vrefl (fmap F f)))
      (cylinder_refl (vrefl (fmap F f) $@v vrefl (fmap F f)))).
  Defined.

  Local Definition swap_diag_hrefl_vrefl_inv {x y : A} (p : x $-> y)
    : hrefl p $== (vrefl p)^$.
  Proof.
    cbv [hrefl vrefl].
    symmetry.
    exact (gpd_rev_pp ((cat_idr p)^$) (cat_idl p)
      $@ ((cat_idl p)^$ $@L gpd_rev_rev (cat_idr p))).
  Defined.

  Local Definition pointwise_diagonal_outer_coherence
    {x y : A} (p : x $-> y)
    : ((cat_assoc (Id x) p (Id y) $@ (Id y $@L hrefl p))
        $@ (((cat_assoc p (Id y) (Id y))^$
          $@ (Id (Id y $o Id y) $@R p))
          $@ cat_assoc p (Id y) (Id y)))
        $@ (Id y $@L (cat_idl p $@ (cat_idr p)^$))
      $== ((cat_idl p $@ (cat_idr p)^$) $@R Id x)
        $@ ((cat_assoc (Id x) (Id x) p
          $@ (p $@L Id (Id x $o Id x)))
          $@ (((cat_assoc (Id x) (Id x) p)^$
            $@ ((cat_idr p $@ (cat_idl p)^$) $@R Id x))
            $@ cat_assoc (Id x) p (Id y))).
  Proof.
    cbv [hrefl].
    transitivity (cat_assoc (Id x) p (Id y)).
    - pose (PA := cat_assoc (Id x) p (Id y)).
      pose (PH := Id y $@L (cat_idr p $@ (cat_idl p)^$)).
      pose (PC1 := cat_assoc p (Id y) (Id y)).
      pose (PD := Id (Id y $o Id y) $@R p).
      pose (PU := Id y $@L (cat_idl p $@ (cat_idr p)^$)).
      pose (PX := (PC1^$ $@ PD) $@ PC1).
      change (((PA $@ PH) $@ PX) $@ PU $== PA).
      lhs' exact (PU $@L cat_assoc_opp PA PH PX).
      lhs' exact (cat_assoc_opp PA (PH $@ PX) PU).
      assert (xz : PX $== Id (Id y $o (Id y $o p))).
      { exact ((PC1 $@L
          ((fmap_id (cat_precomp y p) (Id y $o Id y))
            $@R PC1^$ $@ cat_idl PC1^$))
          $@ gpd_isretr PC1). }
      assert (uh : PU $o PH $== Id (Id y $o (p $o Id x))).
      { refine ((PU $@L (_ $@ _)) $@ gpd_isretr PU).
        - exact (fmap2 (cat_postcomp x (Id y))
            (swap_diag_hrefl_vrefl_inv p)).
        - exact (gpd_1functor_V
            (cat_postcomp x (Id y)) (vrefl p)). }
      assert (z : ((PH $@ PX) $@ PU)
        $== Id (Id y $o (p $o Id x))).
      { exact ((PU $@L (xz $@R PH))
          $@ (PU $@L cat_idl PH) $@ uh). }
      lhs' exact (z $@R PA).
      exact (cat_idl PA).
    - pose (PA := cat_assoc (Id x) p (Id y)).
      pose (PR1 := (cat_idr p $@ (cat_idl p)^$) $@R Id x).
      pose (PA' := cat_assoc (Id x) (Id x) p).
      pose (PE := p $@L Id (Id x $o Id x)).
      pose (PR0 := (cat_idl p $@ (cat_idr p)^$) $@R Id x).
      change (PA
        $== PR0 $@ ((PA' $@ PE) $@ ((PA'^$ $@ PR1) $@ PA))).
      rhs' exact
        ((cat_assoc_opp PR0 (PA' $@ PE) ((PA'^$ $@ PR1) $@ PA))^$).
      rhs' exact
        ((cat_assoc_opp (PR0 $@ (PA' $@ PE)) (PA'^$ $@ PR1) PA)^$).
      assert (mid : PA'^$ $o (PE $o PA')
        $== Id ((p $o Id x) $o Id x)).
      { exact ((PA'^$ $@L
          ((fmap_id (cat_postcomp x p) (Id x $o Id x))
            $@R PA' $@ cat_idl PA'))
          $@ gpd_issect PA'). }
      assert (rr : PR1 $o PR0
        $== Id ((Id y $o p) $o Id x)).
      { exact (((fmap2 (cat_precomp y (Id x))
          (swap_diag_hrefl_vrefl_inv p)
          $@ gpd_1functor_V (cat_precomp y (Id x)) (vrefl p))
          $@R PR0) $@ gpd_issect PR0). }
      assert (pm : ((PR0 $@ (PA' $@ PE)) $@ (PA'^$ $@ PR1))
        $== Id ((Id y $o p) $o Id x)).
      { lhs' exact (cat_assoc ((PE $o PA') $o PR0) PA'^$ PR1).
        lhs' exact
          (PR1 $@L cat_assoc_opp PR0 (PE $o PA') PA'^$).
        lhs' exact
          (cat_assoc_opp PR0 (PA'^$ $o (PE $o PA')) PR1).
        lhs' exact ((PR1 $@L mid) $@R PR0).
        lhs' exact ((cat_idr PR1) $@R PR0).
        exact rr. }
      rhs' exact ((PA $@L pm) $@ cat_idr PA).
      reflexivity.
  Defined.

  Local Definition pointwise_diagonal_triangle (a : A)
    : ((cat_assoc (Id a) (Id a) (Id a)
          $@ ((Id a) $@L Id ((Id a) $o (Id a))))
        $@ (((cat_assoc (Id a) (Id a) (Id a))^$
          $@ (Id ((Id a) $o (Id a)) $@R (Id a)))
          $@ cat_assoc (Id a) (Id a) (Id a))) $@
      ((Id a) $@L cat_idl (Id a))
      $== (cat_idl (Id a) $@R (Id a))
        $@ (cat_idl (Id a) $@ (cat_idr (Id a))^$).
  Proof.
    pose (I0 := Id a).
    pose (TA := cat_assoc I0 I0 I0).
    pose (TE := I0 $@L Id (I0 $o I0)).
    pose (TD := Id (I0 $o I0) $@R I0).
    pose (TU := I0 $@L cat_idl I0).
    pose (TX := (TA^$ $@ TD) $@ TA).
    change (((TA $@ TE) $@ TX) $@ TU
      $== (cat_idl I0 $@R I0)
        $@ (cat_idl I0 $@ (cat_idr I0)^$)).
    transitivity (cat_idr I0 $@R I0).
    - lhs' exact (TU $@L cat_assoc_opp TA TE TX).
      lhs' exact (cat_assoc_opp TA (TE $@ TX) TU).
      assert (mid1 : TX $== Id (I0 $o (I0 $o I0))).
      { exact ((TA $@L
          ((fmap_id (cat_precomp a I0) (I0 $o I0))
            $@R TA^$ $@ cat_idl TA^$))
          $@ gpd_isretr TA). }
      assert (xz2 : TX $o TE $== Id (I0 $o (I0 $o I0))).
      { exact ((mid1 $@R TE) $@ cat_idl TE
          $@ fmap_id (cat_postcomp a I0) (I0 $o I0)). }
      lhs' exact ((TU $@L xz2) $@R TA).
      lhs' exact ((cat_idr TU) $@R TA).
      exact (cat_tril (A := A) a a a I0 I0).
    - rhs' exact (((((cat_idr I0)^$ $@L cat_idl_idr_id a)
          $@ gpd_issect (cat_idr I0))
          $@R (cat_idl I0 $@R I0))).
      rhs' exact (cat_idl (cat_idl I0 $@R I0)).
      exact ((fmap2 (cat_precomp a I0) (cat_idl_idr_id a))^$).
  Defined.

  Local Definition pointwise_diagonal_triangle_symm (a : A)
    : ((cat_assoc (Id a) (Id a) (Id a)
          $@ ((Id a) $@L Id ((Id a) $o (Id a))))
        $@ (((cat_assoc (Id a) (Id a) (Id a))^$
          $@ (Id ((Id a) $o (Id a)) $@R (Id a)))
          $@ cat_assoc (Id a) (Id a) (Id a))) $@
      ((Id a) $@L cat_idr (Id a))
      $== (cat_idr (Id a) $@R (Id a))
        $@ (cat_idl (Id a) $@ (cat_idr (Id a))^$).
  Proof.
    pose (I0 := Id a).
    pose (TA := cat_assoc I0 I0 I0).
    pose (TE := I0 $@L Id (I0 $o I0)).
    pose (TD := Id (I0 $o I0) $@R I0).
    pose (TU := I0 $@L cat_idr I0).
    pose (TX := (TA^$ $@ TD) $@ TA).
    change (((TA $@ TE) $@ TX) $@ TU
      $== (cat_idr I0 $@R I0)
        $@ (cat_idl I0 $@ (cat_idr I0)^$)).
    transitivity (cat_idl I0 $@R I0).
    - lhs' exact (TU $@L cat_assoc_opp TA TE TX).
      lhs' exact (cat_assoc_opp TA (TE $@ TX) TU).
      assert (mid1 : TX $== Id (I0 $o (I0 $o I0))).
      { exact ((TA $@L
          ((fmap_id (cat_precomp a I0) (I0 $o I0))
            $@R TA^$ $@ cat_idl TA^$))
          $@ gpd_isretr TA). }
      assert (xz2 : TX $o TE $== Id (I0 $o (I0 $o I0))).
      { exact ((mid1 $@R TE) $@ cat_idl TE
          $@ fmap_id (cat_postcomp a I0) (I0 $o I0)). }
      lhs' exact ((TU $@L xz2) $@R TA).
      lhs' exact ((cat_idr TU) $@R TA).
      lhs' exact
        (((fmap2 (cat_postcomp a I0) (cat_idl_idr_id a))^$)
          $@R TA).
      lhs' exact (cat_tril (A := A) a a a I0 I0).
      exact ((fmap2 (cat_precomp a I0) (cat_idl_idr_id a))^$).
    - rhs' exact (((((cat_idr I0)^$ $@L cat_idl_idr_id a)
          $@ gpd_issect (cat_idr I0))
          $@R (cat_idr I0 $@R I0))).
      rhs' exact (cat_idl (cat_idr I0 $@R I0)).
      exact (fmap2 (cat_precomp a I0) (cat_idl_idr_id a)).
  Defined.

  Definition nattrans_pointwise_diagonal
    : NatTrans
        (fun12_pointwise_diagonal I A J)
        (fun22_diagonal02 (Fun02 I A) J).
  Proof.
    snapply Build_NatTrans.
    - intro F. exact (pointwise_diagonal_component F).
    - snapply Build_Is1Natural.
      intros F G alpha.
      snapply Build_NatModification.
      { intro j.
        snapply Build_NatModification.
        { intro i.
          cbn.
          exact (cat_idl (alpha i) $@ (cat_idr (alpha i))^$). }
        intros i i' f.
        cbn.
        exact (cylinder_rewrite_front
          (s0' := (((Id (alpha i' $o fmap F f))^$
            $@ is1natural_nattrans alpha i i' f)
            $@ Id (fmap G f $o alpha i))
            $@v (cat_idl (fmap G f) $@ (cat_idr (fmap G f))^$))
          (square_vconcat_natural_above
            (cat_idl
              (is1natural_nattrans alpha i i' f
                $o (Id (alpha i' $o fmap F f))^$)
              $@ (is1natural_nattrans alpha i i' f $@L gpd_rev_1)
              $@ cat_idr (is1natural_nattrans alpha i i' f))
            (cat_idl (fmap G f) $@ (cat_idr (fmap G f))^$))
          (cylinder_comp
            (square_vconcat_idl (is1natural_nattrans alpha i i' f))
            (cylinder_inverse
              (square_vconcat_idr
                (is1natural_nattrans alpha i i' f))))). }
      intros j j' g.
      cbn.
      intro i.
      exact (pointwise_diagonal_outer_coherence (alpha i)).
  Defined.

  Local Definition pointwise_diagonal_component_inv (F : Fun02 I A)
    : fun22_diagonal02 (Fun02 I A) J F
      $-> fun12_pointwise_diagonal I A J F.
  Proof.
    snapply Build_NatTrans.
    { intro j. exact (Id F). }
    snapply Build_Is1Natural.
    intros j j' g.
    snapply Build_NatModification.
    { intro i. exact (Id _). }
    intros i i' f.
    cbn.
    exact (cylinder_rewrite_back
      (s1' := vrefl (fmap F f) $@v transpose (hrefl (fmap F f)))
      (square_vconcat_natural_below
        (vrefl (fmap F f))
        (transpose_hrefl_vrefl (fmap F f)))
      (cylinder_refl
        (vrefl (fmap F f) $@v vrefl (fmap F f)))).
  Defined.

  Local Definition pointwise_diagonal_retr (F : Fun02 I A)
    : NatModification
        (nattrans_comp
          (pointwise_diagonal_component F)
          (pointwise_diagonal_component_inv F))
        (nattrans_id (fun22_diagonal02 (Fun02 I A) J F)).
  Proof.
    snapply Build_NatModification.
    { intro j. cbn. exact (cat_idl (Id F)). }
    intros j j' g.
    cbn.
    intro i.
    exact (pointwise_diagonal_triangle (F i)).
  Defined.

  Local Definition pointwise_diagonal_sect (F : Fun02 I A)
    : NatModification
        (nattrans_comp
          (pointwise_diagonal_component_inv F)
          (pointwise_diagonal_component F))
        (nattrans_id (fun12_pointwise_diagonal I A J F)).
  Proof.
    snapply Build_NatModification.
    { intro j. cbn. exact (cat_idr (Id F)). }
    intros j j' g.
    cbn.
    intro i.
    exact (pointwise_diagonal_triangle_symm (F i)).
  Defined.

  Definition natequiv_pointwise_diagonal
    : NatEquiv
        (fun12_pointwise_diagonal I A J)
        (fun22_diagonal02 (Fun02 I A) J).
  Proof.
    snapply Build_NatEquiv'.
    - exact nattrans_pointwise_diagonal.
    - intro F.
      snapply catie_adjointify.
      + exact (pointwise_diagonal_component_inv F).
      + exact (pointwise_diagonal_retr F).
      + exact (pointwise_diagonal_sect F).
  Defined.
End PointwiseDiagonalComparison.

Section PointwiseLimitFunctorCategory.
  Context (I A J : Type) `{IsGraph I, Is21Cat A, IsGraph J}.
  Context `{!HasLimit22 J A}.

  Definition gpd_adjunction_pointwise_limit_fun02
    : GpdAdjunction
        (fun11_fun22 (fun22_diagonal02 (Fun02 I A) J))
        (fun11_fun12 (fun12_pointwise_limit22 I A J)).
  Proof.
    rapply (gpd_adjunction_natequiv_left
      (fun11_fun12 (fun12_pointwise_diagonal I A J))
      (fun11_fun22 (fun22_diagonal02 (Fun02 I A) J))
      (fun11_fun12 (fun12_pointwise_limit22 I A J))
      (natequiv_pointwise_diagonal I A J)).
    exact (gpd_adjunction_pointwise_limit22 I A J).
  Defined.
End PointwiseLimitFunctorCategory.
