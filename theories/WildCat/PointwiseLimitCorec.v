Require Import Basics.Overture Basics.Tactics.
Require Import WildCat.Core WildCat.Cylinder WildCat.Equiv WildCat.FunctorCat
  WildCat.Limits WildCat.NatTrans WildCat.OneGroupoid WildCat.Square
  WildCat.TwoFunctor WildCat.TwoOneCat WildCat.TwoYoneda.

(** * Componentwise mediating maps for pointwise limits

    This module contains the stable, calculation-heavy construction of the
    pointwise corecursor and its beta and edgewise eta coherences.  The final
    categorical-equivalence packaging is kept in
    [PointwiseLimitUniversal] so changes there do not re-elaborate these
    pasting calculations. *)

Set Typeclasses Depth 4.







Definition limit_cone_biinv_direct
  {A J : Type} `{Is21Cat A, IsGraph J}
  {D : Fun02 J A} {l : A}
  (lambda : diagonal02 A J l $-> D)
  (Hlambda : IsLimitCone D l lambda)
  (a : A)
  : @Cat_IsBiInv OneGpd isgraph_1gpd is2graph_1gpd
      is01cat_1gpd is1cat_1gpd
      (hom_1gpd (A := A) a l) (cone_1gpd D a)
      (limit_cone_map D l lambda a).
Proof.
  destruct (Hlambda a) as [g r g' s].
  exact (Build_Cat_IsBiInv g r g' s).
Defined.

Definition limit_cone_map_inv_direct
  {A J : Type} `{Is21Cat A, IsGraph J}
  {D : Fun02 J A} {l : A}
  (lambda : diagonal02 A J l $-> D)
  (Hlambda : IsLimitCone D l lambda)
  (a : A)
  : Fun11 (cone_1gpd D a) (hom_1gpd (A := A) a l)
  := @cat_equiv_inv OneGpd isgraph_1gpd is2graph_1gpd
      is01cat_1gpd is1cat_1gpd
      (hom_1gpd (A := A) a l) (cone_1gpd D a)
      (limit_cone_map D l lambda a)
      (limit_cone_biinv_direct lambda Hlambda a).

Definition limit_corec_of_islimitcone_direct
  {A J : Type} `{Is21Cat A, IsGraph J}
  {D : Fun02 J A} {l a : A}
  (lambda : diagonal02 A J l $-> D)
  (Hlambda : IsLimitCone D l lambda)
  (alpha : diagonal02 A J a $-> D)
  : a $-> l
  := limit_cone_map_inv_direct lambda Hlambda a alpha.

Definition limit_beta_of_islimitcone_direct
  {A J : Type} `{Is21Cat A, IsGraph J}
  {D : Fun02 J A} {l a : A}
  (lambda : diagonal02 A J l $-> D)
  (Hlambda : IsLimitCone D l lambda)
  (alpha : diagonal02 A J a $-> D)
  : limit_cone_map D l lambda a
      (limit_corec_of_islimitcone_direct lambda Hlambda alpha)
    $== alpha
  := @cat_eisretr OneGpd isgraph_1gpd is2graph_1gpd
      is01cat_1gpd is1cat_1gpd
      (hom_1gpd (A := A) a l) (cone_1gpd D a)
      (limit_cone_map D l lambda a)
      (limit_cone_biinv_direct lambda Hlambda a) alpha.

Definition limit_eta_of_islimitcone_direct
  {A J : Type} `{Is21Cat A, IsGraph J}
  {D : Fun02 J A} {l a : A}
  (lambda : diagonal02 A J l $-> D)
  (Hlambda : IsLimitCone D l lambda)
  (k : a $-> l)
  : limit_corec_of_islimitcone_direct lambda Hlambda
      (limit_cone_map D l lambda a k)
    $== k
  := @cat_eissect OneGpd isgraph_1gpd is2graph_1gpd
      is01cat_1gpd is1cat_1gpd
      (hom_1gpd (A := A) a l) (cone_1gpd D a)
      (limit_cone_map D l lambda a)
      (limit_cone_biinv_direct lambda Hlambda a) k.

Definition limit_cone_map_reflects_direct
  {A J : Type} `{Is21Cat A, IsGraph J}
  {D : Fun02 J A} {l a : A}
  (lambda : diagonal02 A J l $-> D)
  (Hlambda : IsLimitCone D l lambda)
  {f g : a $-> l}
  (p : limit_cone_map D l lambda a f
    $== limit_cone_map D l lambda a g)
  : f $== g
  := fun11_bireflect
      (limit_cone_map D l lambda a)
      (limit_cone_biinv_direct lambda Hlambda a) p.

Definition limit_corec_direct
  {A J : Type} `{Is21Cat A, IsGraph J}
  (D : Fun02 J A) `{!Limit J D}
  {a : A} (alpha : diagonal02 A J a $-> D)
  : a $-> cat_limit J D
  := limit_corec_of_islimitcone_direct
      (cat_limit_cone J D) (cat_islimit_cone J D) alpha.

Definition limit_beta_direct
  {A J : Type} `{Is21Cat A, IsGraph J}
  (D : Fun02 J A) `{!Limit J D}
  {a : A} (alpha : diagonal02 A J a $-> D)
  : limit_cone_map D (cat_limit J D) (cat_limit_cone J D) a
      (limit_corec_direct D alpha)
    $== alpha
  := limit_beta_of_islimitcone_direct
      (cat_limit_cone J D) (cat_islimit_cone J D) alpha.

Definition limit_corec_modification_direct
  {A J : Type} `{Is21Cat A, IsGraph J}
  (D : Fun02 J A) `{!Limit J D}
  {a : A} {alpha beta : diagonal02 A J a $-> D}
  (p : alpha $== beta)
  : limit_corec_direct D alpha $== limit_corec_direct D beta
  := fun11_fmap
      (limit_cone_map_inv_direct
        (cat_limit_cone J D) (cat_islimit_cone J D) a) p.


Definition limit_beta_direct_naturality
  {A J : Type} `{Is21Cat A, IsGraph J}
  (D : Fun02 J A) `{!Limit J D}
  {a : A} {alpha beta : diagonal02 A J a $-> D}
  (p : alpha $== beta)
  : Square
      (fun11_fmap
        (limit_cone_map D (cat_limit J D) (cat_limit_cone J D) a)
        (limit_corec_modification_direct D p))
      p
      (limit_beta_direct D alpha)
      (limit_beta_direct D beta).
Proof.
  exact ((isnat
    (@cat_eisretr OneGpd isgraph_1gpd is2graph_1gpd
      is01cat_1gpd is1cat_1gpd
      (hom_1gpd (A := A) a (cat_limit J D))
      (cone_1gpd D a)
      (limit_cone_map D (cat_limit J D) (cat_limit_cone J D) a)
      (limit_cone_biinv_direct
        (cat_limit_cone J D) (cat_islimit_cone J D) a))
    p)^$).
Defined.


Section PointwiseLimitDirect.
  Context (I A J : Type) `{IsGraph I, Is21Cat A, IsGraph J}.
  Context `{!HasLimits J A}.

  Local Definition transpose_hrefl_vrefl_direct
    {a b : A} (h : a $-> b)
    : transpose (hrefl h) $== vrefl h.
  Proof.
    exact (gpd_rev_pp ((cat_idl h)^$) (cat_idr h)
      $@ ((cat_idr h)^$ $@L gpd_rev_rev (cat_idl h))).
  Defined.

  Local Definition transpose_vrefl_hrefl_direct
    {a b : A} (h : a $-> b)
    : transpose (vrefl h) $== hrefl h.
  Proof.
    exact (gpd_rev_pp ((cat_idr h)^$) (cat_idl h)
      $@ ((cat_idl h)^$ $@L gpd_rev_rev (cat_idr h))).
  Defined.

  Definition pointwise_diagonal_fmap_direct
    (P : Fun02 I A) {i i' : I} (f : i $-> i')
    : fmap
        (swap_fun02 J I A
          (diagonal02 (Fun02 I A) J P)) f
      $== fmap (diagonal02 A J) (fmap P f).
  Proof.
    snapply Build_NatModification.
    - intro j.
      exact (Id _).
    - intros j j' g.
      exact (cylinder_rewrite_front
        (transpose_vrefl_hrefl_direct (fmap P f))
        (cylinder_refl (hrefl (fmap P f)))).
  Defined.

  Definition pointwise_diagonal_map_comparison
    {P Q : Fun02 I A} (k : P $-> Q) (i : I)
    : nattrans_swap_fun02_at J I A
        (fmap (diagonal02 (Fun02 I A) J) k) i
      $== fmap (diagonal02 A J) (k i).
  Proof.
    snapply Build_NatModification.
    - intro j.
      exact (Id _).
    - intros j j' g.
      exact (cylinder_refl (hrefl (k i))).
  Defined.

  Definition pointwise_diagonal_comparison
    (P : Fun02 I A)
    : swap_fun02 I J A
        (fun02_postcomp (A := I)
          (fun12_fun22 (fun22_diagonal02 A J)) P)
      $-> diagonal02 (Fun02 I A) J P.
  Proof.
    snapply Build_NatTrans.
    - intro j. exact (Id P).
    - snapply Build_Is1Natural.
      intros j j' g.
      snapply Build_NatModification.
      + intro i. exact (Id _).
      + intros i i' f.
        exact (cylinder_rewrite_front
          (s0' := transpose (hrefl (fmap P f)) $@v vrefl (fmap P f))
          (square_vconcat_natural_above
            (transpose_hrefl_vrefl_direct (fmap P f))
            (vrefl (fmap P f)))
          (cylinder_refl
            (vrefl (fmap P f) $@v vrefl (fmap P f)))).
  Defined.

  Definition swap_fun02_hom_to_at_direct
    {A0 B0 C : Type} `{IsGraph A0, IsGraph B0, Is21Cat C}
    {F : Fun02 A0 (Fun02 B0 C)}
    {G : Fun02 B0 (Fun02 A0 C)}
    (alpha : swap_fun02 A0 B0 C F $-> G) (a : A0)
    : F a $-> swap_fun02 B0 A0 C G a.
  Proof.
    snapply Build_NatTrans.
    - exact (fun b => alpha b a).
    - snapply Build_Is1Natural.
      intros b b' g.
      exact (natmod_component _ _
        (isnat (alnat := is1natural_nattrans alpha) alpha g) a).
  Defined.

  Definition swap_fun02_hom_to_naturality_direct
    {A0 B0 C : Type} `{IsGraph A0, IsGraph B0, Is21Cat C}
    {F : Fun02 A0 (Fun02 B0 C)}
    {G : Fun02 B0 (Fun02 A0 C)}
    (alpha : swap_fun02 A0 B0 C F $-> G)
    {a a' : A0} (f : a $-> a')
    : swap_fun02_hom_to_at_direct alpha a' $o fmap F f
      $== fmap (swap_fun02 B0 A0 C G) f
        $o swap_fun02_hom_to_at_direct alpha a.
  Proof.
    snapply Build_NatModification.
    - intro b.
      exact (isnat
        (alnat := is1natural_nattrans (alpha b)) (alpha b) f).
    - intros b b' g.
      cbn beta.
      exact (cylinder_rotate_vconcat_transpose_front
        (natmod_isnatural _ _
          (isnat (alnat := is1natural_nattrans alpha) alpha g) f)).
  Defined.

  Definition swap_fun02_hom_to_direct
    {A0 B0 C : Type} `{IsGraph A0, IsGraph B0, Is21Cat C}
    (F : Fun02 A0 (Fun02 B0 C))
    (G : Fun02 B0 (Fun02 A0 C))
    : swap_fun02 A0 B0 C F $-> G
      -> F $-> swap_fun02 B0 A0 C G.
  Proof.
    intro alpha.
    snapply Build_NatTrans.
    - exact (swap_fun02_hom_to_at_direct alpha).
    - snapply Build_Is1Natural.
      intros a a' f.
      exact (swap_fun02_hom_to_naturality_direct alpha f).
  Defined.

  Definition pointwise_limit_local_cones_simple
    {X : Fun02 J (Fun02 I A)} {P : Fun02 I A}
    (alpha : diagonal02 (Fun02 I A) J P $-> X) (i : I)
    : diagonal02 A J (P i)
      $-> pointwise_limit_diagram I A J X i
    := nattrans_swap_fun02_at J I A alpha i.

  Definition double_swap_unit_direct
    (F : Fun02 I (Fun02 J A))
    : F $-> swap_fun02 J I A (swap_fun02 I J A F)
    := swap_fun02_hom_to_direct F (swap_fun02 I J A F)
      (Id (swap_fun02 I J A F)).

  Definition pointwise_limit_local_cones
    {X : Fun02 J (Fun02 I A)} {P : Fun02 I A}
    (alpha : diagonal02 (Fun02 I A) J P $-> X)
    : swap_fun02 J I A (diagonal02 (Fun02 I A) J P)
      $-> swap_fun02 J I A X
    := nattrans_swap_fun02 J I A alpha.

  Definition pointwise_limit_local_cones_fun11
    (X : Fun02 J (Fun02 I A)) (P : Fun02 I A)
    : Fun11
        (cone_1gpd X P)
        (hom_1gpd
          (swap_fun02 J I A (diagonal02 (Fun02 I A) J P))
          (swap_fun02 J I A X))
    := fun11_swap_fun02_hom
      (diagonal02 (Fun02 I A) J P) X.

  Definition pointwise_limit_corec_component
    {X : Fun02 J (Fun02 I A)} {P : Fun02 I A}
    (alpha : diagonal02 (Fun02 I A) J P $-> X) (i : I)
    : P i $-> pointwise_limit_apex I A J X i
    := limit_corec_direct (pointwise_limit_diagram I A J X i)
      (pointwise_limit_local_cones alpha i).

  Definition pointwise_limit_cone_map_comparison
    (X : Fun02 J (Fun02 I A)) (P : Fun02 I A)
    (k : P $-> pointwise_limit_apex I A J X) (i : I)
    : nattrans_swap_fun02_at J I A
        (limit_cone_map X
          (pointwise_limit_apex I A J X)
          (pointwise_limit_cone I A J X) P k) i
      $==
      limit_cone_map
        (pointwise_limit_diagram I A J X i)
        (pointwise_limit_apex I A J X i)
        (cat_limit_cone J
          (pointwise_limit_diagram I A J X i))
        (P i) (k i).
  Proof.
    lhs' exact (natmod_swap_fun02_comp_at J I A
      (fmap (diagonal02 (Fun02 I A) J) k)
      (pointwise_limit_cone I A J X) i).
    exact (natmod_postcompose
      (nattrans_swap_fun02_at J I A
        (pointwise_limit_cone I A J X) i)
      (pointwise_diagonal_map_comparison k i)).
  Defined.

  Definition pointwise_limit_cone_map_comparison_component
    (X : Fun02 J (Fun02 I A)) (P : Fun02 I A)
    (k : P $-> pointwise_limit_apex I A J X)
    (i : I) (j : J)
    : natmod_component _ _
        (pointwise_limit_cone_map_comparison X P k i) j
      $== Id _.
  Proof.
    rewrite natmod_cat_comp_component.
    rewrite natmod_postcompose_component.
    pose (lambda :=
      cat_limit_cone J
        (pointwise_limit_diagram I A J X i) j).
    exact (cat_idr (lambda $@L Id (k i))
      $@ fmap_id (cat_postcomp (P i) lambda) (k i)).
  Defined.

  Definition pointwise_limit_corec_component_fun11
    (X : Fun02 J (Fun02 I A)) (P : Fun02 I A) (i : I)
    : Fun11
        (cone_1gpd X P)
        (hom_1gpd (P i) (pointwise_limit_apex I A J X i)).
  Proof.
    pose (L := pointwise_limit_local_cones_fun11 X P).
    pose (V := fun11_eval_fun02_hom
      (swap_fun02 J I A (diagonal02 (Fun02 I A) J P))
      (swap_fun02 J I A X) i).
    pose (E := limit_cone_map_inv_direct
      (cat_limit_cone J
        (pointwise_limit_diagram I A J X i))
      (cat_islimit_cone J
        (pointwise_limit_diagram I A J X i))
      (P i)).
    exact (fun11_compose E (fun11_compose V L)).
  Defined.

  Definition pointwise_limit_corec_naturality_cone
    {X : Fun02 J (Fun02 I A)} {P : Fun02 I A}
    (alpha : diagonal02 (Fun02 I A) J P $-> X)
    {i i' : I} (f : i $-> i')
    : limit_cone_map
        (pointwise_limit_diagram I A J X i')
        (pointwise_limit_apex I A J X i')
        (cat_limit_cone J
          (pointwise_limit_diagram I A J X i'))
        (P i)
        (pointwise_limit_corec_component alpha i'
          $o fmap P f)
      $==
      limit_cone_map
        (pointwise_limit_diagram I A J X i')
        (pointwise_limit_apex I A J X i')
        (cat_limit_cone J
          (pointwise_limit_diagram I A J X i'))
        (P i)
        (fmap (pointwise_limit_apex I A J X) f
          $o pointwise_limit_corec_component alpha i).
  Proof.
    pose (D := pointwise_limit_diagram I A J X i).
    pose (D' := pointwise_limit_diagram I A J X i').
    pose (lambda := cat_limit_cone J D).
    pose (lambda' := cat_limit_cone J D').
    pose (a := pointwise_limit_local_cones alpha i).
    pose (a' := pointwise_limit_local_cones alpha i').
    pose (pf := fmap P f).
    pose (df := fmap (swap_fun02 J I A X) f).
    pose (k := pointwise_limit_corec_component alpha i).
    pose (k' := pointwise_limit_corec_component alpha i').
    pose (lf := fmap (pointwise_limit_apex I A J X) f).
    lhs' exact (natmod_postcompose lambda'
      (natmod_diagonal02_comp A J pf k')).
    lhs' exact (natmod_inverse
      (natmod_assoc_from_cylinder
        (fmap (diagonal02 A J) pf)
        (fmap (diagonal02 A J) k') lambda')).
    lhs' exact (natmod_precompose
      (fmap (diagonal02 A J) pf)
      (limit_beta_direct D' a')).
    lhs' exact (natmod_postcompose a'
      (natmod_inverse
        (pointwise_diagonal_fmap_direct P f))).
    lhs' exact (isnat (pointwise_limit_local_cones alpha) f).
    lhs' exact (natmod_postcompose df
      (natmod_inverse (limit_beta_direct D a))).
    lhs' exact (natmod_inverse
      (natmod_assoc_from_cylinder
        (fmap (diagonal02 A J) k) lambda df)).
    lhs' exact (natmod_precompose
      (fmap (diagonal02 A J) k)
      (natmod_inverse (cat_limit_map_beta df))).
    lhs' exact (natmod_assoc_from_cylinder
      (fmap (diagonal02 A J) k)
      (fmap (diagonal02 A J) lf) lambda').
    exact (natmod_postcompose lambda'
      (natmod_inverse (natmod_diagonal02_comp A J k lf))).
  Defined.

  Definition pointwise_limit_corec_naturality
    {X : Fun02 J (Fun02 I A)} {P : Fun02 I A}
    (alpha : diagonal02 (Fun02 I A) J P $-> X)
    {i i' : I} (f : i $-> i')
    : pointwise_limit_corec_component alpha i'
        $o fmap P f
      $== fmap (pointwise_limit_apex I A J X) f
        $o pointwise_limit_corec_component alpha i.
  Proof.
    exact (limit_cone_map_reflects_direct
      (cat_limit_cone J
        (pointwise_limit_diagram I A J X i'))
      (cat_islimit_cone J
        (pointwise_limit_diagram I A J X i'))
      (pointwise_limit_corec_naturality_cone alpha f)).
  Defined.

  Definition pointwise_limit_corec
    {X : Fun02 J (Fun02 I A)} {P : Fun02 I A}
    (alpha : diagonal02 (Fun02 I A) J P $-> X)
    : P $-> pointwise_limit_apex I A J X.
  Proof.
    snapply Build_NatTrans.
    - exact (pointwise_limit_corec_component alpha).
    - snapply Build_Is1Natural.
      exact (fun i i' f =>
        pointwise_limit_corec_naturality alpha f).
  Defined.

  Definition pointwise_limit_local_cones_modification
    {X : Fun02 J (Fun02 I A)} {P : Fun02 I A}
    {alpha beta : diagonal02 (Fun02 I A) J P $-> X}
    (p : alpha $== beta)
    : pointwise_limit_local_cones alpha
      $== pointwise_limit_local_cones beta.
  Proof.
    exact (fun11_fmap
      (pointwise_limit_local_cones_fun11 X P) p).
  Defined.

  Definition pointwise_limit_corec_modification_component
    {X : Fun02 J (Fun02 I A)} {P : Fun02 I A}
    {alpha beta : diagonal02 (Fun02 I A) J P $-> X}
    (p : alpha $== beta) (i : I)
    : pointwise_limit_corec_component alpha i
      $== pointwise_limit_corec_component beta i.
  Proof.
    exact (fun11_fmap
      (pointwise_limit_corec_component_fun11 X P i) p).
  Defined.

  Definition pointwise_limit_corec_modification_naturality_cone_square
    {X : Fun02 J (Fun02 I A)} {P : Fun02 I A}
    {alpha beta : diagonal02 (Fun02 I A) J P $-> X}
    (p : alpha $== beta) {i i' : I} (f : i $-> i')
    : let D' := pointwise_limit_diagram I A J X i' in
      let F := limit_cone_map D'
        (pointwise_limit_apex I A J X i')
        (cat_limit_cone J D') (P i) in
      Square
        (fun11_fmap F
          (pointwise_limit_corec_modification_component p i'
            $@R fmap P f))
        (fun11_fmap F
          (fmap (pointwise_limit_apex I A J X) f
            $@L pointwise_limit_corec_modification_component p i))
        (pointwise_limit_corec_naturality_cone alpha f)
        (pointwise_limit_corec_naturality_cone beta f).
    nrefine (hconcatR _ _).
    2: reflexivity.
    nrefine (hconcatL _ _).
    { reflexivity. }
    pose (D := pointwise_limit_diagram I A J X i).
    pose (D' := pointwise_limit_diagram I A J X i').
    pose (lambda := cat_limit_cone J D).
    pose (lambda' := cat_limit_cone J D').
    pose (delta := fun22_diagonal02 A J).
    pose (pf := fmap P f).
    pose (df := fmap (swap_fun02 J I A X) f).
    pose (k := pointwise_limit_corec_component alpha i).
    pose (l := pointwise_limit_corec_component beta i).
    pose (k' := pointwise_limit_corec_component alpha i').
    pose (l' := pointwise_limit_corec_component beta i').
    pose (lf := fmap (pointwise_limit_apex I A J X) f).
    pose (dpf := fmap delta pf).
    pose (dfk := fmap delta k).
    pose (dfl := fmap delta l).
    pose (dfk' := fmap delta k').
    pose (dfl' := fmap delta l').
    pose (dlf := fmap delta lf).
    pose (a := pointwise_limit_local_cones alpha i).
    pose (b := pointwise_limit_local_cones beta i).
    pose (a' := pointwise_limit_local_cones alpha i').
    pose (b' := pointwise_limit_local_cones beta i').
    pose (p0 := natmod_component _ _
      (pointwise_limit_local_cones_modification p) i).
    pose (p1 := natmod_component _ _
      (pointwise_limit_local_cones_modification p) i').
    pose (m0 :=
      pointwise_limit_corec_modification_component p i).
    pose (m1 :=
      pointwise_limit_corec_modification_component p i').
    pose (dm0 := fmap2 delta m0).
    pose (dm1 := fmap2 delta m1).
    pose (na := isnat (pointwise_limit_local_cones alpha) f).
    pose (nb := isnat (pointwise_limit_local_cones beta) f).
    pose (np := natmod_isnatural
      (pointwise_limit_local_cones alpha)
      (pointwise_limit_local_cones beta)
      (pointwise_limit_local_cones_modification p) f).
    pose (ep0 := limit_beta_direct_naturality D p0).
    pose (ep1 := limit_beta_direct_naturality D' p1).
    pose (c1 := fmap_square
      (cat_postcomp (diagonal02 A J (P i)) lambda')
      (fmap_comp_prewhisker_natural delta pf m1)).
    pose (c2 :=
      cat_assoc_opp_natural_m dpf dm1 lambda').
    pose (c3 := fmap_square
      (cat_precomp D' dpf) ep1).
    pose (s := fmap
      (swap_fun02 J I A
        (diagonal02 (Fun02 I A) J P)) f).
    pose (u := pointwise_diagonal_fmap_direct P f).
    pose (c3' := (bifunctor_coh_comp u^$ p1)^$
      : Square
        (p1 $@R dpf) (p1 $@R s)
        (a' $@L u^$) (b' $@L u^$)).
    pose (c4 := np).
    pose (c5 := fmap_square
      (cat_postcomp (diagonal02 A J (P i)) df)
      (hinverse_square_gpd ep0)).
    pose (c6 := cat_assoc_opp_natural_r dm0 lambda df).
    pose (t := (cat_limit_map_beta df)^$).
    pose (c7 := bifunctor_coh_comp dm0 t).
    pose (c8 := transpose
      (cat_assoc_natural_r dm0 dlf lambda')).
    assert (e8 :
      ((lambda' $o dlf) $@L dm0)
      $==
      (limit_cone_map D' (cat_limit J D') lambda'
        (cat_limit J D) (cat_limit_map df) $@L dm0)).
    { reflexivity. }
    pose (c7' := hconcatR c7 e8).
    pose (c9 := fmap_square
      (cat_postcomp (diagonal02 A J (P i)) lambda')
      (hinverse_square_gpd
        (fmap_comp_postwhisker_natural delta m0 lf))).
    nrefine (hconcat c1 _).
    nrefine (hconcat c2 _).
    nrefine (hconcat c3 _).
    nrefine (hconcat c3' _).
    nrefine (hconcat c4 _).
    nrefine (hconcat c5 _).
    nrefine (hconcat c6 _).
    nrefine (hconcat c7' _).
    nrefine (hconcat c8 c9).
  Defined.

  Definition limit_cone_map_reflects_3cell_direct
    {D : Fun02 J A} {l a : A}
    (lambda : diagonal02 A J l $-> D)
    (Hlambda : IsLimitCone D l lambda)
    {f g : a $-> l} {p q : f $== g}
    (h : fun11_fmap (limit_cone_map D l lambda a) p
      $== fun11_fmap (limit_cone_map D l lambda a) q)
    : p $== q.
  Proof.
    pose (e := limit_cone_map_cate_of_islimitcone
      lambda Hlambda a).
    pose (eta := cate_issect e).
    pose (gh := fmap2 (cate_fun e^-1$) h).
    pose (np := isnat eta p).
    pose (nq := isnat eta q).
    napply (@gpd_cancelR (a $-> l)
      (isgraph_hom a l)
      (isgraph_hom_hom a l)
      (is01cat_hom a l)
      (is1cat_hom a l)
      (is0gpd_hom a l)
      (is1gpd_hom a l)).
    exact (np^$ $@ (eta g $@L gh) $@ nq).
  Defined.

  Definition pointwise_limit_corec_modification_naturality_cylinder
    {X : Fun02 J (Fun02 I A)} {P : Fun02 I A}
    {alpha beta : diagonal02 (Fun02 I A) J P $-> X}
    (p : alpha $== beta) {i i' : I} (f : i $-> i')
    : Cylinder
        (pointwise_limit_corec_modification_component p i)
        (pointwise_limit_corec_modification_component p i')
        (pointwise_limit_corec_naturality alpha f)
        (pointwise_limit_corec_naturality beta f).
  Proof.
    napply cylinder_of_square.
    pose (D' := pointwise_limit_diagram I A J X i').
    pose (lambda' := cat_limit_cone J D').
    pose (F := limit_cone_map D'
      (pointwise_limit_apex I A J X i') lambda' (P i)).
    pose (HF := limit_cone_biinv_direct lambda'
      (cat_islimit_cone J D') (P i)).
    nrefine (hconcatR _ _).
    - nrefine (hconcatL _ _).
      + exact (fun11_bireflect_fmap F HF
          (pointwise_limit_corec_modification_component p i'
            $@R fmap P f))^$.
      + napply (fun11_bireflect_square F HF).
        exact (pointwise_limit_corec_modification_naturality_cone_square p f).
    - exact (fun11_bireflect_fmap F HF
        (fmap (pointwise_limit_apex I A J X) f
          $@L pointwise_limit_corec_modification_component p i))^$.
  Defined.


  Definition pointwise_limit_corec_modification
    {X : Fun02 J (Fun02 I A)} {P : Fun02 I A}
    {alpha beta : diagonal02 (Fun02 I A) J P $-> X}
    (p : alpha $== beta)
    : pointwise_limit_corec alpha $== pointwise_limit_corec beta.
  Proof.
    snapply Build_NatModification.
    - exact (pointwise_limit_corec_modification_component p).
    - exact (fun i i' f =>
        pointwise_limit_corec_modification_naturality_cylinder p f).
  Defined.

  Definition pointwise_limit_corec_3cell
    {X : Fun02 J (Fun02 I A)} {P : Fun02 I A}
    {alpha beta : diagonal02 (Fun02 I A) J P $-> X}
    {p q : alpha $== beta} (h : p $== q)
    : pointwise_limit_corec_modification p
      $== pointwise_limit_corec_modification q.
  Proof.
    intro i.
    exact (fmap2
      (pointwise_limit_corec_component_fun11 X P i) h).
  Defined.

  Definition pointwise_limit_corec_fun11
    (X : Fun02 J (Fun02 I A)) (P : Fun02 I A)
    : Fun11
        (cone_1gpd X P)
        (hom_1gpd P (pointwise_limit_apex I A J X)).
  Proof.
    snapply Build_Fun11.
    - exact (fun alpha => pointwise_limit_corec alpha).
    - snapply Build_Is0Functor.
      exact (fun alpha beta p =>
        pointwise_limit_corec_modification p).
    - snapply Build_Is1Functor.
      + exact (fun alpha beta p q h =>
          pointwise_limit_corec_3cell h).
      + intros alpha i.
        exact (fmap_id
          (pointwise_limit_corec_component_fun11 X P i) alpha).
      + intros alpha beta gamma p q i.
        exact (fmap_comp
          (pointwise_limit_corec_component_fun11 X P i) p q).
  Defined.


  Definition pointwise_limit_beta_at
    (X : Fun02 J (Fun02 I A)) (P : Fun02 I A)
    (alpha : cone_1gpd X P) (j : J)
    : (limit_cone_map X
        (pointwise_limit_apex I A J X)
        (pointwise_limit_cone I A J X) P
        (pointwise_limit_corec alpha)) j
      $== alpha j.
  Proof.
    snapply Build_NatModification.
    - intro i.
        pose (b := natmod_component _ _
          (limit_beta_direct
            (pointwise_limit_diagram I A J X i)
            (pointwise_limit_local_cones alpha i)) j).
        exact b.
    - intros i i' f.
        pose (D' := pointwise_limit_diagram I A J X i').
        pose (lambda' := cat_limit_cone J D').
        pose (F := limit_cone_map D'
          (pointwise_limit_apex I A J X i') lambda' (P i)).
        pose (HF := limit_cone_biinv_direct lambda'
          (cat_islimit_cone J D') (P i)).
        pose (s :=
          pointwise_limit_corec_naturality_cone alpha f).
        pose (h := fun11_fmap_bireflect F HF s).
        pose (hj := h j).
        pose (delta := fun22_diagonal02 A J).
        pose (n := pointwise_limit_corec_naturality alpha f).
        napply Build_Cylinder.
        pose (D := pointwise_limit_diagram I A J X i).
        pose (lambda := cat_limit_cone J D).
        pose (a := pointwise_limit_local_cones alpha i).
        pose (a' := pointwise_limit_local_cones alpha i').
        pose (k := pointwise_limit_corec_component alpha i).
        pose (k' := pointwise_limit_corec_component alpha i').
        pose (xf := fmap (X j) f).
        pose (pf := fmap P f).
        pose (q := isnat
          (pointwise_limit_cone_at I A J X j
            $o pointwise_limit_corec alpha) f).
        pose (af := isnat (alpha j) f).
        pose (bi := natmod_component
          (limit_cone_map D (pointwise_limit_apex I A J X i)
            lambda (P i) k) a
          (limit_beta_direct D a) j).
        pose (bi' := natmod_component
          (limit_cone_map D' (pointwise_limit_apex I A J X i')
            lambda' (P i') k') a'
          (limit_beta_direct D' a') j).
        change (xf $@L bi $o q $== af $o bi' $@R pf).
        pose (df := fmap (swap_fun02 J I A X) f).
        pose (lf := fmap (pointwise_limit_apex I A J X) f).
        pose (cf := natmod_component
          (limit_cone_map D' (pointwise_limit_apex I A J X i')
            lambda' (pointwise_limit_apex I A J X i)
            (cat_limit_map df))
          (df $o lambda) (cat_limit_map_beta df) j).
        assert (eq_q : q $== n $@v cf).
        { reflexivity. }
        lhs' exact ((xf $@L bi) $@L eq_q).
        pose (sj := natmod_component
          (F (k' $o pf)) (F (lf $o k)) s j).
        assert (eh : lambda' j $@L n $== sj).
        { exact hj. }
        unfold vconcat.
        change (xf $@L bi $o
          (cat_assoc pf k' (lambda' j) $@
            (lambda' j $@L n)) $@
          ((cat_assoc_opp k lf (lambda' j) $@
              (cf $@R k)) $@
            cat_assoc k (lambda j) (df j))
          $== af $o bi' $@R pf).
        pose (aa := cat_assoc pf k' (lambda' j)).
        pose (rr :=
          (cat_assoc_opp k lf (lambda' j) $@ (cf $@R k))
            $@ cat_assoc k (lambda j) (df j)).
        assert (e1 :
          aa $@ (lambda' j $@L n) $==
          aa $@ sj).
        { exact (eh $@R aa). }
        pose (bb := xf $@L bi).
        lhs' exact (bb $@L (rr $@L e1)).
        pose (u := pointwise_diagonal_fmap_direct P f).
        pose (uj := natmod_component _ _ u j).
        pose (br := a' j $@L uj^$).
        assert (esj :
          sj $==
          aa^$ $@ (bi' $@R pf) $@ br $@ af
            $@ (xf $@L bi^$) $@ rr^$).
        { unfold sj, s, pointwise_limit_corec_naturality_cone.
          cbn beta.
          unfold transitive_GpdHom,
            transitive_natmodification,
            natmod_postcompose, natmod_precompose,
            natmod_inverse, natmod_assoc_from_cylinder,
            natmod_diagonal02_comp.
          cbn beta.
          unfold gpd_comp.
          unfold is01cat_hom_fun02.
          unfold cat_comp.
          repeat rewrite natmod_comp_component.
          cbn beta.
          unfold natmod_component.
          cbn beta.
          assert (dpf :
            fmap (diagonal02 A J) pf j = pf).
          { reflexivity. }
          assert (dk :
            fmap (diagonal02 A J) k j = k).
          { reflexivity. }
          assert (dkp :
            fmap (diagonal02 A J) (k' $o pf) j = k' $o pf).
          { reflexivity. }
          assert (dlfk :
            fmap (diagonal02 A J) (lf $o k) j = lf $o k).
          { reflexivity. }
          assert (ddf : df j = xf).
          { reflexivity. }
          assert (dlcn :
            natmod_component _ _
              (is1natural_nattrans
                (pointwise_limit_local_cones alpha) i i' f) j
            = af).
          { reflexivity. }
          change (
            ((lambda' j $@L Id (k' $o pf))
              $@ (aa^$
                $@ ((bi' $@R pf)
                  $@ (br
                    $@ (af
                      $@ ((xf $@L bi^$)
                        $@ ((cat_assoc k (lambda j) (df j))^$
                          $@ ((cf^$ $@R k)
                            $@ (cat_assoc k lf (lambda' j)
                              $@ (lambda' j $@L
                                (Id (lf $o k))^$))))))))))
            $==
            aa^$ $@ (bi' $@R pf) $@ br $@ af
              $@ (xf $@L bi^$) $@ rr^$).
          pose (ao := cat_assoc_opp k lf (lambda' j)).
          pose (a1 := cf $@R k).
          pose (a2 := cat_assoc k (lambda j) (df j)).
          pose (r0 := cat_assoc k lf (lambda' j)).
          pose (r1 := cf^$ $@R k).
          pose (r2 := (cat_assoc k (lambda j) (df j))^$).
          pose (idtail := lambda' j $@L (Id (lf $o k))^$).
          pose (er :=
            fmap2 (cat_postcomp (P i) (lambda' j))
              (gpd_rev_1
                (A := P i $->
                  pointwise_limit_apex I A J X i')
                (a := lf $o k))
              $@ fmap_id
                (cat_postcomp (P i) (lambda' j)) (lf $o k)).
          assert (etail :
            r2 $@ (r1 $@ (r0 $@ idtail)) $== rr^$).
          { pose (eend :=
              (er $@R r0) $@ cat_idl r0).
            lhs' exact ((eend $@R r1) $@R r2).
            pose (eao :=
              cat_assoc_opp_is_rev _ _ _ _
                k lf (lambda' j)).
            pose (e0 :=
              (gpd_rev2 eao $@ gpd_rev_rev r0)^$).
            lhs' exact ((e0 $@R r1) $@R r2).
            pose (epre :=
              gpd_1functor_V
                (cat_precomp (X j i') k) cf).
            lhs' exact ((ao^$ $@L epre) $@R r2).
            lhs' exact ((gpd_rev_pp a1 ao)^$ $@R r2).
            exact (gpd_rev_pp a2 (a1 $o ao))^$. }
          pose (rest :=
            aa^$ $@ ((bi' $@R pf)
              $@ (br $@ (af $@ ((xf $@L bi^$)
                $@ (r2 $@ (r1 $@ (r0 $@ idtail)))))))).
          pose (el :=
            fmap_id
              (cat_postcomp (P i) (lambda' j)) (k' $o pf)).
          lhs' exact (rest $@L el).
          lhs' exact (cat_idr rest).
          unfold rest.
          lhs' exact (cat_assoc _ _ _).
          lhs' exact (cat_assoc _ _ _).
          lhs' exact (cat_assoc _ _ _).
          lhs' exact (cat_assoc _ _ _).
          exact (etail $@R
            ((((aa^$ $@ (bi' $@R pf)) $@ br)
              $@ af) $@ (xf $@L bi^$))). }
        assert (ebr : br $== Id (a' j $o pf)).
        { change (
            (a' j $@L (Id pf)^$)
              $== Id (a' j $o pf)).
          exact (
            fmap2 (cat_postcomp (P i) (a' j))
              (gpd_rev_1
                (A := P i $-> P i') (a := pf))
            $@ fmap_id
              (cat_postcomp (P i) (a' j)) pf). }
        lhs' exact (bb $@L (rr $@L (esj $@R aa))).
        pose (b0 := bi' $@R pf).
        pose (l2 := b0 $o aa^$).
        pose (l3 := br $o l2).
        pose (l4 := af $o l3).
        pose (bbi := xf $@L bi^$).
        pose (l5 := bbi $o l4).
        change (
          bb $o (rr $o ((rr^$ $o l5) $o aa))
            $== af $o b0).
        lhs' exact
          (bb $@L (rr $@L (cat_assoc aa l5 rr^$))).
        lhs' exact
          (bb $@L (rr $@L (rr^$ $@L
            (cat_assoc aa l4 bbi)))).
        lhs' exact
          (bb $@L (rr $@L (rr^$ $@L
            (bbi $@L (cat_assoc aa l3 af))))).
        lhs' exact
          (bb $@L (rr $@L (rr^$ $@L
            (bbi $@L (af $@L
              (cat_assoc aa l2 br)))))).
        lhs' exact
          (bb $@L (rr $@L (rr^$ $@L
            (bbi $@L (af $@L (br $@L
              (cat_assoc aa aa^$ b0))))))).
        pose (eca :=
          (b0 $@L gpd_issect aa) $@ cat_idr b0).
        lhs' exact
          (bb $@L (rr $@L (rr^$ $@L
            (bbi $@L (af $@L (br $@L eca)))))).
        pose (rest := af $o (br $o b0)).
        lhs' exact
          (bb $@L
            gpd_h_Vh rr (bbi $o rest)).
        pose (ebbi :=
          gpd_1functor_V
            (cat_postcomp (P i) xf) bi).
        lhs' exact (bb $@L (ebbi $@R rest)).
        lhs' exact (gpd_h_Vh bb rest).
        lhs' exact (af $@L (ebr $@R b0)).
        exact (af $@L cat_idl b0).
  Defined.

  Local Definition pointwise_limit_beta_at_component
    (X : Fun02 J (Fun02 I A)) (P : Fun02 I A)
    (alpha : cone_1gpd X P) (j : J) (i : I)
    : natmod_component _ _
        (pointwise_limit_beta_at X P alpha j) i
      =
      natmod_component _ _
        (limit_beta_direct
          (pointwise_limit_diagram I A J X i)
          (pointwise_limit_local_cones alpha i)) j.
  Proof.
    reflexivity.
  Defined.

  Local Definition pointwise_limit_local_cones_isnatural_component
    (X : Fun02 J (Fun02 I A)) (P : Fun02 I A)
    (alpha : cone_1gpd X P)
    (j j' : J) (g : j $-> j') (i : I)
    : natmod_component _ _
        (is1natural_nattrans alpha j j' g) i
      =
      is1natural_nattrans
        (pointwise_limit_local_cones alpha i) j j' g.
  Proof.
    reflexivity.
  Defined.

  Local Definition pointwise_limit_cone_map_isnatural_component
    (X : Fun02 J (Fun02 I A)) (P : Fun02 I A)
    (alpha : cone_1gpd X P)
    (j j' : J) (g : j $-> j') (i : I)
    : natmod_component _ _
        (is1natural_nattrans
          (limit_cone_map X
            (pointwise_limit_apex I A J X)
            (pointwise_limit_cone I A J X) P
            (pointwise_limit_corec alpha))
          j j' g) i
      $==
      is1natural_nattrans
        (limit_cone_map
          (pointwise_limit_diagram I A J X i)
          (pointwise_limit_apex I A J X i)
          (cat_limit_cone J
            (pointwise_limit_diagram I A J X i))
          (P i)
          (pointwise_limit_corec_component alpha i))
        j j' g.
  Proof.
    pose (h := pointwise_limit_cone_map_comparison
      X P (pointwise_limit_corec alpha) i).
    pose (ehj :=
      pointwise_limit_cone_map_comparison_component
        X P (pointwise_limit_corec alpha) i j).
    pose (ehj' :=
      pointwise_limit_cone_map_comparison_component
        X P (pointwise_limit_corec alpha) i j').
    pose (c := natmod_isnatural _ _ h g).
    exact (cylinder_id_to_3cell
      (cylinder_rewrite_right ehj'^$
        (cylinder_rewrite_left ehj^$ c))).
  Defined.

  Definition pointwise_limit_beta_component
    (X : Fun02 J (Fun02 I A)) (P : Fun02 I A)
    (alpha : cone_1gpd X P)
    : (limit_cone_map X
        (pointwise_limit_apex I A J X)
        (pointwise_limit_cone I A J X) P
        (pointwise_limit_corec alpha))
      $== alpha.
  Proof.
    snapply Build_NatModification.
    - exact (pointwise_limit_beta_at X P alpha).
    - intros j j' g.
      intro i.
      pose (D := pointwise_limit_diagram I A J X i).
      pose (a := pointwise_limit_local_cones alpha i).
      pose (beta := limit_beta_direct D a).
      pose (c := natmod_isnatural _ _ beta g).
      pose (e :=
        pointwise_limit_cone_map_isnatural_component
          X P alpha j j' g i).
      pose (b := natmod_component _ _ beta j).
      lhs' exact ((fmap D g $@L b) $@L e).
      exact c.
  Defined.

  Local Definition pointwise_limit_beta_component_at
    (X : Fun02 J (Fun02 I A)) (P : Fun02 I A)
    (alpha : cone_1gpd X P) (j : J)
    : natmod_component _ _
        (pointwise_limit_beta_component X P alpha) j
      =
      pointwise_limit_beta_at X P alpha j.
  Proof.
    reflexivity.
  Defined.

  Local Definition pointwise_limit_beta_comparison
    (X : Fun02 J (Fun02 I A)) (P : Fun02 I A)
    (alpha : cone_1gpd X P) (i : I)
    : Square
        (natmod_swap_fun02_at J I A
          (pointwise_limit_beta_component X P alpha) i)
        (limit_beta_direct
          (pointwise_limit_diagram I A J X i)
          (pointwise_limit_local_cones alpha i))
        (pointwise_limit_cone_map_comparison X P
          (pointwise_limit_corec alpha) i)
        (Id (pointwise_limit_local_cones alpha i)).
  Proof.
    napply Build_NatModificationSquare.
    intro j.
    rewrite natmod_cat_comp_component.
    pose (hcj := natmod_component _ _
      (pointwise_limit_cone_map_comparison X P
        (pointwise_limit_corec alpha) i) j).
    pose (betj := natmod_component _ _
      (limit_beta_direct
        (pointwise_limit_diagram I A J X i)
        (pointwise_limit_local_cones alpha i)) j).
    pose (bgj := natmod_component _ _
      (natmod_swap_fun02_at J I A
        (pointwise_limit_beta_component X P alpha) i) j).
    pose (eh := pointwise_limit_cone_map_comparison_component
      X P (pointwise_limit_corec alpha) i j).
    assert (eb : bgj $== betj).
    {
      unfold bgj.
      rewrite natmod_swap_fun02_at_component.
      rewrite pointwise_limit_beta_at_component.
      exact (Id betj).
    }
    exact (vconcatL eh (hconcatL eb (hrefl betj))).
  Defined.

  Definition pointwise_limit_beta_naturality
    (X : Fun02 J (Fun02 I A)) (P : Fun02 I A)
    {alpha beta : cone_1gpd X P} (p : alpha $== beta)
    : Square
        (fun11_fmap
          (fun11_compose
            (limit_cone_map X
              (pointwise_limit_apex I A J X)
              (pointwise_limit_cone I A J X) P)
            (pointwise_limit_corec_fun11 X P)) p)
        p
        (pointwise_limit_beta_component X P alpha)
        (pointwise_limit_beta_component X P beta).
  Proof.
    napply Build_NatModificationSquare.
    intro j.
    napply Build_NatModificationSquare.
    intro i.
    pose (D := pointwise_limit_diagram I A J X i).
    pose (q := natmod_component _ _
      (pointwise_limit_local_cones_modification p) i).
    pose (c := limit_beta_direct_naturality D q).
    exact (c j).
  Defined.

  Definition pointwise_limit_beta
    (X : Fun02 J (Fun02 I A)) (P : Fun02 I A)
    : fun11_compose
        (limit_cone_map X
          (pointwise_limit_apex I A J X)
          (pointwise_limit_cone I A J X) P)
        (pointwise_limit_corec_fun11 X P)
      $== Id (cone_1gpd X P).
  Proof.
    snapply Build_NatTrans.
    - exact (pointwise_limit_beta_component X P).
    - snapply Build_Is1Natural.
      intros alpha beta p.
      exact (pointwise_limit_beta_naturality X P p)^$.
  Defined.

  Opaque pointwise_limit_beta.

  Definition pointwise_limit_eta_component
    (X : Fun02 J (Fun02 I A)) (P : Fun02 I A)
    (k : P $-> pointwise_limit_apex I A J X) (i : I)
    : pointwise_limit_corec
        (limit_cone_map X
          (pointwise_limit_apex I A J X)
          (pointwise_limit_cone I A J X) P k) i
      $== k i.
  Proof.
    napply (fun11_bireflect
      (limit_cone_map
        (pointwise_limit_diagram I A J X i)
        (pointwise_limit_apex I A J X i)
        (cat_limit_cone J (pointwise_limit_diagram I A J X i))
        (P i))
      (limit_cone_biinv_direct
        (cat_limit_cone J (pointwise_limit_diagram I A J X i))
        (cat_islimit_cone J (pointwise_limit_diagram I A J X i))
        (P i))).
    exact (limit_beta_direct
      (pointwise_limit_diagram I A J X i)
      (pointwise_limit_local_cones
        (limit_cone_map X
          (pointwise_limit_apex I A J X)
          (pointwise_limit_cone I A J X) P k) i)
      $@ pointwise_limit_cone_map_comparison X P k i).
  Defined.



  Definition pointwise_limit_eta_naturality_cone
    (X : Fun02 J (Fun02 I A)) (P : Fun02 I A)
    (k : P $-> pointwise_limit_apex I A J X)
    {i i' : I} (f : i $-> i')
    : let alpha := limit_cone_map X
          (pointwise_limit_apex I A J X)
          (pointwise_limit_cone I A J X) P k in
      let D' := pointwise_limit_diagram I A J X i' in
      let F := limit_cone_map D'
        (pointwise_limit_apex I A J X i')
        (cat_limit_cone J D') (P i) in
      Square
        (fun11_fmap F
          (pointwise_limit_eta_component X P k i'
            $@R fmap P f))
        (fun11_fmap F
          (fmap (pointwise_limit_apex I A J X) f
            $@L pointwise_limit_eta_component X P k i))
        (pointwise_limit_corec_naturality_cone alpha f)
        (fun11_fmap F (isnat k f)).
  Proof.
    cbn zeta.
    pose (alpha := limit_cone_map X
      (pointwise_limit_apex I A J X)
      (pointwise_limit_cone I A J X) P k).
    pose (D := pointwise_limit_diagram I A J X i).
    pose (D' := pointwise_limit_diagram I A J X i').
    pose (lambda := cat_limit_cone J D).
    pose (lambda' := cat_limit_cone J D').
    pose (delta := fun22_diagonal02 A J).
    pose (pf := fmap P f).
    pose (df := fmap (swap_fun02 J I A X) f).
    pose (m := pointwise_limit_corec_component alpha i).
    pose (m' := pointwise_limit_corec_component alpha i').
    pose (l := k i).
    pose (l' := k i').
    pose (lf := fmap (pointwise_limit_apex I A J X) f).
    pose (dpf := fmap delta pf).
    pose (dm := fmap delta m).
    pose (dm' := fmap delta m').
    pose (dl := fmap delta l).
    pose (dl' := fmap delta l').
    pose (dlf := fmap delta lf).
    pose (a := pointwise_limit_local_cones alpha i).
    pose (a' := pointwise_limit_local_cones alpha i').
    pose (h := pointwise_limit_cone_map_comparison X P k i).
    pose (h' := pointwise_limit_cone_map_comparison X P k i').
    pose (bet := limit_beta_direct D a).
    pose (bet' := limit_beta_direct D' a').
    pose (p0 := bet $@ h).
    pose (p1 := bet' $@ h').
    pose (eta0 := pointwise_limit_eta_component X P k i).
    pose (eta1 := pointwise_limit_eta_component X P k i').
    pose (deta0 := fmap2 delta eta0).
    pose (deta1 := fmap2 delta eta1).
    pose (ep0 := fun11_fmap_bireflect
      (limit_cone_map D (cat_limit J D) lambda (P i))
      (limit_cone_biinv_direct lambda
        (cat_islimit_cone J D) (P i)) p0).
    pose (ep1 := fun11_fmap_bireflect
      (limit_cone_map D' (cat_limit J D') lambda' (P i'))
      (limit_cone_biinv_direct lambda'
        (cat_islimit_cone J D') (P i')) p1).
    pose (c1 := fmap_square
      (cat_postcomp (diagonal02 A J (P i)) lambda')
      (fmap_comp_prewhisker_natural delta pf eta1)).
    pose (c2 := cat_assoc_opp_natural_m
      dpf deta1 lambda').
    pose (c3 := fmap_square
      (cat_precomp D' dpf) (hdeg_square ep1)).
    pose (cleft12 := c1 $@h c2).
    pose (eep1 := fmap2 (cat_precomp D' dpf) ep1).
    pose (cleft := cleft12 $@hR eep1^$).
    pose (u := pointwise_diagonal_fmap_direct P f).
    pose (bglobal :=
      pointwise_limit_beta_component X P alpha).
    pose (bglobal0 :=
      natmod_swap_fun02_at J I A bglobal i).
    pose (bglobal1 :=
      natmod_swap_fun02_at J I A bglobal i').
    pose (cmid := fun j =>
      natmod_isnatural _ _
        (pointwise_limit_beta_at X P alpha j) f).
    assert (cmid' : Square
      (A := hom_1gpd (diagonal02 A J (P i)) D')
      (natmod_precompose
        (fmap (swap_fun02 J I A
          (diagonal02 (Fun02 I A) J P)) f) bglobal1)
      (natmod_postcompose df bglobal0)
      (isnat (pointwise_limit_local_cones
        (limit_cone_map X
          (pointwise_limit_apex I A J X)
          (pointwise_limit_cone I A J X) P
          (pointwise_limit_corec alpha))) f)
      (isnat (pointwise_limit_local_cones alpha) f)).
    { exact cmid. }
    pose (cbeta0 :=
      pointwise_limit_beta_comparison X P alpha i).
    pose (cbeta1 :=
      pointwise_limit_beta_comparison X P alpha i').
    pose (sdf := fmap (swap_fun02 J I A
      (diagonal02 (Fun02 I A) J P)) f).
    pose (cbetabridge1 := fmap_square
      (cat_precomp D' sdf) (hinverse_square_gpd cbeta1)).
    pose (cbetabridge0 := fmap_square
      (cat_postcomp (diagonal02 A J (P i)) df) cbeta0).
    assert (cbase0 : Square bet p0 (Id _) h).
    { exact (cat_idr p0). }
    assert (cbase1 : Square bet' p1 (Id _) h').
    { exact (cat_idr p1). }
    pose (cbridge1 := fmap_square (cat_precomp D' dpf)
      (hinverse_square_gpd cbase1)).
    pose (cu := bifunctor_coh_comp u^$ bet').
    pose (cbridge0 := fmap_square
      (cat_postcomp (diagonal02 A J (P i)) df) cbase0).
    pose (c6 := cat_assoc_opp_natural_r deta0 lambda df).
    pose (t := (cat_limit_map_beta df)^$).
    pose (c7 := bifunctor_coh_comp deta0 t).
    pose (c8 := transpose
      (cat_assoc_natural_r deta0 dlf lambda')).
    assert (e8 :
      ((lambda' $o dlf) $@L deta0)
      $==
      (limit_cone_map D' (cat_limit J D') lambda'
        (cat_limit J D) (cat_limit_map df) $@L deta0)).
    { reflexivity. }
    pose (c7' := c7 $@hR e8).
    pose (c9 := fmap_square
      (cat_postcomp (diagonal02 A J (P i)) lambda')
      (hinverse_square_gpd
        (fmap_comp_postwhisker_natural
          delta eta0 lf))).
    pose (cright0 :=
      c6 $@h (c7' $@h (c8 $@h c9))).
    pose (eep0 := fmap2
      (cat_postcomp (diagonal02 A J (P i)) df) ep0).
    pose (cright := cright0 $@hL eep0^$).
    pose (middle := cbridge1 $@h (transpose cu $@h
      (cbetabridge1 $@h (cmid' $@h (cbetabridge0 $@h
        cbridge0))))).
    pose (whole := cleft $@h (cbridge1 $@h (transpose cu $@h
      (cbetabridge1 $@h (cmid' $@h (cbetabridge0 $@h
        (cbridge0 $@h cright))))))).
    pose (F := limit_cone_map D' (cat_limit J D') lambda' (P i)).
    square_bottom whole as WB.
    assert (ebottom : fun11_fmap F (isnat k f) $== WB).
    {
    intro j.
    cbn.
    lazymatch goal with
    | |- ?L0x $== (?R1x $@ ?R2x) $@ (?R3x $@ ?R4x) =>
      pose (BL0 := L0x);
      pose (BR1 := R1x);
      pose (BR2 := R2x);
      pose (BR3 := R3x);
      pose (BR4 := R4x);
      change (BL0 $==
        (BR1 $@ BR2) $@ (BR3 $@ BR4))
    end.
    let V := (eval unfold BR4 in BR4) in
      lazymatch V with
      | ?x1 $@ ?r1 => pose (X1 := x1); pose (Rest1 := r1)
      end;
    let V := (eval unfold Rest1 in Rest1) in
      lazymatch V with
      | ?x2 $@ ?r2 => pose (X2 := x2); pose (Rest2 := r2)
      end;
    let V := (eval unfold Rest2 in Rest2) in
      lazymatch V with
      | ?x3 $@ ?r3 => pose (X3 := x3); pose (Rest3 := r3)
      end;
    let V := (eval unfold Rest3 in Rest3) in
      lazymatch V with
      | ?x4 $@ ?r4 => pose (X4 := x4); pose (Rest4 := r4)
      end;
    let V := (eval unfold Rest4 in Rest4) in
      lazymatch V with
      | ?x5 $@ ?r5 => pose (X5 := x5); pose (Rest5 := r5)
      end;
    let V := (eval unfold Rest5 in Rest5) in
      lazymatch V with
      | ?x6 $@ ?r6 => pose (X6 := x6); pose (Rest6 := r6)
      end;
    let V := (eval unfold Rest6 in Rest6) in
      lazymatch V with
      | ?x7 $@ ?r7 => pose (X7 := x7); pose (Rest7 := r7)
      end;
    let V := (eval unfold Rest7 in Rest7) in
      lazymatch V with
      | ?x8 $@ ?r8 => pose (X8 := x8); pose (Rest8 := r8)
      end.
    assert (ecore :
      BL0 $==
      (BR2 $@ X3) $@ (X6 $@ (X7 $@ X8))).
    {
      unfold BR2, X3, X6, X7, X8, BL0, vconcat.
      let V := (eval unfold X7 in X7) in
        lazymatch V with
        | ?u0x^$ $@R ?kx => pose (u0 := u0x)
        end.
      pose (a0 := cat_assoc pf (k i') (lambda' j)).
      pose (d0 := cat_assoc (k i)
        (cat_limit_map (swap_fun02_fmap J I A X f))
        (lambda' j)).
      pose (c0a := cat_assoc
        (k i) (lambda j) (fmap (X j) f)).
      pose (s0a := lambda' j $@L
        isnat k f).
      pose (ao0 := cat_assoc_opp (k i)
        (cat_limit_map (swap_fun02_fmap J I A X f))
        (lambda' j)).
      pose (uk0 := u0 $@R k i).
      pose (uik0 := u0^$ $@R k i).
      change (s0a $==
        (a0^$ $@
          ((a0 $@ s0a) $@ ((ao0 $@ uk0) $@ c0a)))
        $@ (c0a^$ $@ (uik0 $@ d0))).
      pose (t0a := (ao0 $@ uk0) $@ c0a).
      pose (q0a := c0a^$ $@ (uik0 $@ d0)).
      symmetry.
      change
        ((a0^$ $@ ((a0 $@ s0a) $@ t0a)) $@ q0a
          $== s0a).
      lhs' exact
        (q0a $@L cat_assoc a0^$ (a0 $@ s0a) t0a).
      lhs' exact
        (q0a $@L (t0a $@L gpd_hh_V s0a a0)).
      assert (etail : t0a $@ q0a $== Id _).
      {
        pose (euk := gpd_1functor_V
          (cat_precomp (X j i') (k i)) u0).
        pose (eao := cat_assoc_opp_is_rev _ _ _ _
          (k i)
          (cat_limit_map (swap_fun02_fmap J I A X f))
          (lambda' j)).
        pose (ed :=
          (gpd_rev2 eao $@ gpd_rev_rev d0)^$).
        pose (eqmid := euk $@@ ed).
        pose (eqfront := eqmid $@R c0a^$).
        pose (etinv :=
          gpd_rev_pp c0a (uk0 $o ao0)
          $@ (gpd_rev_pp uk0 ao0 $@R c0a^$)).
        pose (eqtail := eqfront $@ etinv^$).
        lhs' exact (eqtail $@R t0a).
        exact (gpd_issect t0a).
      }
      lhs' exact (cat_assoc s0a t0a q0a)^$.
      lhs' exact (etail $@R s0a).
      exact (cat_idl s0a).
    }
    change (BL0 $==
      (BR1 $@ BR2) $@
      (BR3 $@
        (X1 $@ (X2 $@ (X3 $@
          (X4 $@ (X5 $@
            (X6 $@ (X7 $@ (X8 $@ Rest8)))))))))).
    pose (eBR1 := fmap_id
      (cat_postcomp (P i) (lambda' j))
      (k i' $o pf)).
    pose (eh0 :=
      pointwise_limit_cone_map_comparison_component
        X P k i j).
    pose (eh1 :=
      pointwise_limit_cone_map_comparison_component
        X P k i' j).
    pose (eh1v := gpd_rev2 eh1 $@ gpd_rev_1).
    pose (eBR3 :=
      fmap2 (cat_precomp (X j i') pf) eh1v
      $@ fmap_id (cat_precomp (X j i') pf) _).
    pose (hk1 := trans_comp
      (fun i : I =>
        cat_limit_cone J
          (swap_fun02_at J I A X i) j)
      k i').
    pose (eidpf :=
      (gpd_rev_1 : (Id pf)^$ $== Id pf)).
    pose (eX1 :=
      fmap2 (cat_postcomp (P i) hk1) eidpf
      $@ fmap_id (cat_postcomp (P i) hk1) pf).
    pose (eidhk1 :=
      (gpd_rev_1 : (Id hk1)^$ $== Id hk1)).
    pose (eX2 :=
      fmap2 (cat_precomp (X j i') pf) eidhk1
      $@ fmap_id (cat_precomp (X j i') pf) hk1).
    pose (hk0 := trans_comp
      (fun i : I =>
        cat_limit_cone J
          (swap_fun02_at J I A X i) j)
      k i).
    pose (eX4 :=
      fmap_id
        (cat_postcomp (P i) (fmap (X j) f)) hk0).
    pose (eX5 :=
      fmap2 (cat_postcomp (P i) (fmap (X j) f)) eh0
      $@ fmap_id
        (cat_postcomp (P i) (fmap (X j) f)) _).
    pose (lk0 :=
      cat_limit_map (swap_fun02_fmap J I A X f)
      $o k i).
    pose (eidlk :=
      (gpd_rev_1 : (Id lk0)^$ $== Id lk0)).
    pose (eRest8 :=
      fmap2 (cat_postcomp (P i) (lambda' j)) eidlk
      $@ fmap_id
        (cat_postcomp (P i) (lambda' j)) lk0).
    pose (efull :=
      (eBR1 $@@ Id BR2)
      $@@
      (eBR3 $@@
        (eX1 $@@ (eX2 $@@
          (Id X3 $@@ (eX4 $@@ (eX5 $@@
            (Id X6 $@@ (Id X7 $@@
              (Id X8 $@@ eRest8)))))))))).
    let EF := type of efull in
      lazymatch EF with
      | _ $== ?N =>
          assert (eunit :
            N $== (BR2 $@ X3) $@ (X6 $@ (X7 $@ X8)))
      end.
    {
      pose (etail0 := cat_idl X8).
      pose (etail1 := etail0 $@R X7).
      pose (etail2 := etail1 $@R X6).
      pose (etail3 :=
        (etail2 $@R Id _) $@
        cat_idr (X6 $@ (X7 $@ X8))).
      pose (etail4 :=
        (etail3 $@R Id _) $@
        cat_idr (X6 $@ (X7 $@ X8))).
      pose (emid0 := etail4 $@R X3).
      pose (emid1 :=
        (emid0 $@R Id _) $@
        cat_idr (X3 $@ (X6 $@ (X7 $@ X8)))).
      pose (emid2 :=
        (emid1 $@R Id _) $@
        cat_idr (X3 $@ (X6 $@ (X7 $@ X8)))).
      pose (emid3 :=
        (emid2 $@R Id _) $@
        cat_idr (X3 $@ (X6 $@ (X7 $@ X8)))).
      pose (eleft := cat_idr BR2).
      pose (eunits := eleft $@@ emid3).
      exact (eunits $@
        cat_assoc BR2 X3 (X6 $@ (X7 $@ X8))).
    }
    exact (ecore $@ (efull $@ eunit)^$).
    }
    square_boundaries middle as MidL MidR MidT MidB.
    pose (Lbet := fmap (cat_precomp D' dpf) bet').
    pose (Lh := fmap (cat_precomp D' dpf) h').
    pose (Rbet := fmap
      (cat_postcomp (diagonal02 A J (P i)) df) bet).
    pose (Rh := fmap
      (cat_postcomp (diagonal02 A J (P i)) df) h).
    assert (eLp : (Lh $o Lbet) $== MidL).
    {
      unfold MidL, Lh, Lbet, p1.
      exact (fmap_comp (cat_precomp D' dpf) bet' h')^$.
    }
    assert (eRp : (Rh $o Rbet) $== MidR).
    {
      unfold MidR, Rh, Rbet, p0.
      exact (fmap_comp
        (cat_postcomp (diagonal02 A J (P i)) df)
        bet h)^$.
    }
    pose (tmiddle := transpose middle).
    pose (tmiddle' := tmiddle $@vL eLp $@vR eRp).
    pose (rot := square_rotate_composites tmiddle').
    pose (eT0 := gpd_moveL_Vh rot).
    pose (eT := gpd_moveL_hM eT0).
    pose (middleC := middle $@vL eT^$).
    pose (wholeC := cleft $@h (middleC $@h cright)).
    square_top wholeC as WCT.
    square_bottom wholeC as WCB.
    square_top cleft as CLTop.
    square_top cright as CRTop.
    pose (RbetInv := fmap
      (cat_postcomp (diagonal02 A J (P i)) df) bet^$).
    pose (NatA := isnat (pointwise_limit_local_cones alpha) f).
    pose (Uterm := a' $@L u^$).
    pose (Nmid0 := RbetInv $o NatA).
    pose (Nmid1 := Nmid0 $o Uterm).
    pose (Nmid := Nmid1 $o Lbet).
    pose (PostDf :=
      cat_postcomp (diagonal02 A J (P i)) df).
    pose (PreSdf := cat_precomp D' sdf).
    pose (PreDpf := cat_precomp D' dpf).
    pose (RId := fmap PostDf (Id a)).
    pose (LIdV := fmap PreSdf (Id a')^$).
    pose (LhV := fmap PreDpf h'^$).
    assert (eRId : RId $== Id (PostDf a)).
    { exact (fmap_id PostDf a). }
    assert (eLIdV : LIdV $== Id (PreSdf a')).
    {
      exact (gpd_1functor_V PreSdf (Id a') $@
        gpd_rev2 (fmap_id PreSdf a') $@
        gpd_rev_1).
    }
    assert (eLhV : LhV $== Lh^$).
    { exact (gpd_1functor_V PreDpf h'). }
    assert (eUnits :
      ((RId $o NatA) $o LIdV) $== NatA).
    {
      pose (eu0 := (eRId $@R NatA) $@R LIdV).
      pose (eu1 := eu0 $@ (cat_idl NatA $@R LIdV)).
      pose (eu2 := eu1 $@ (NatA $@L eLIdV)).
      exact (eu2 $@ cat_idr NatA).
    }
    pose (Rest := (Rh $o NatA) $o Uterm).
    pose (Core := Rest $o Lh^$).
    assert (eCore : MidB $== Core).
    {
      change ((((((Rh $o RId) $o NatA) $o LIdV)
        $o Uterm) $o LhV) $== Core).
      pose (ePrefix :=
        (cat_assoc NatA RId Rh $@R LIdV)
        $@ cat_assoc LIdV (RId $o NatA) Rh
        $@ (Rh $@L eUnits)).
      exact (((ePrefix $@R Uterm) $@R LhV)
        $@ (Rest $@L eLhV)).
    }
    assert (eRbetV : RbetInv $== Rbet^$).
    { exact (gpd_1functor_V PostDf bet). }
    pose (Inner := (Rh^$ $o MidB) $o Lh).
    assert (eInner : Inner $== NatA $o Uterm).
    {
      pose (ei0 := (Rh^$ $@L eCore) $@R Lh).
      pose (ei1 := ei0 $@ cat_assoc Lh Core Rh^$).
      pose (ei2 := ei1 $@
        (Rh^$ $@L gpd_hV_h Rest Lh)).
      pose (ei3 := ei2 $@
        (Rh^$ $@L cat_assoc Uterm NatA Rh)).
      exact (ei3 $@ gpd_V_hh Rh (NatA $o Uterm)).
    }
    pose (Wrapped := (Rbet^$ $o Inner) $o Lbet).
    assert (eWrapped : Wrapped $== Nmid).
    {
      pose (ew0 := (Rbet^$ $@L eInner) $@R Lbet).
      pose (ew1 := ew0 $@
        (cat_assoc_opp Uterm NatA Rbet^$ $@R Lbet)).
      exact (ew1 $@
        (((eRbetV^$ $@R NatA) $@R Uterm) $@R Lbet)).
    }
    pose (CL1 := fmap
      (cat_postcomp (diagonal02 A J (P i)) lambda')
      (fmap_comp delta pf m')).
    pose (CL2 := cat_assoc_opp dpf dm' lambda').
    pose (FlatMid :=
      ((((CRTop $o RbetInv) $o NatA)
        $o Uterm) $o Lbet)).
    pose (DirectFlat := (FlatMid $o CL2) $o CL1).
    assert (eGroupMid : FlatMid $== CRTop $o Nmid).
    {
      pose (eg0 :=
        (cat_assoc NatA RbetInv CRTop $@R Uterm)
        $@R Lbet).
      pose (eg1 := eg0 $@
        (cat_assoc Uterm (RbetInv $o NatA) CRTop
          $@R Lbet)).
      exact (eg1 $@ cat_assoc Lbet Nmid1 CRTop).
    }
    assert (eGroup :
      DirectFlat $== (CRTop $o Nmid) $o CLTop).
    {
      change (DirectFlat $==
        (CRTop $o Nmid) $o (CL2 $o CL1)).
      exact ((((eGroupMid $@R CL2) $@R CL1)
        $@ cat_assoc CL1 CL2 (CRTop $o Nmid))).
    }
    assert (ePasted :
      WCT $== (CRTop $o Nmid) $o CLTop).
    {
      change (((CRTop $o Wrapped) $o CLTop)
        $== (CRTop $o Nmid) $o CLTop).
      exact ((CRTop $@L eWrapped) $@R CLTop).
    }
    assert (etopC :
      pointwise_limit_corec_naturality_cone alpha f $== WCT).
    {
      unfold pointwise_limit_corec_naturality_cone.
      change (DirectFlat $== WCT).
      exact (eGroup $@ ePasted^$).
    }
    square_bottom cright as CRBottom.
    square_bottom cleft as CLBottom.
    pose (B1 := Rh $o RId).
    pose (B2 := B1 $o NatA).
    pose (B3 := B2 $o LIdV).
    pose (B4 := B3 $o Uterm).
    pose (B5 := B4 $o LhV).
    assert (eB5 : B5 $== MidB).
    { reflexivity. }
    pose (FlatBottomMid :=
      (((((CRBottom $o Rh) $o RId) $o NatA)
        $o LIdV) $o Uterm) $o LhV).
    pose (FlatBottom := FlatBottomMid $o CLBottom).
    assert (eBottomMid :
      FlatBottomMid $== CRBottom $o MidB).
    {
      pose (eb00 := cat_assoc RId Rh CRBottom).
      pose (eb01 := eb00 $@R NatA).
      pose (eb02 := eb01 $@R LIdV).
      pose (eb03 := eb02 $@R Uterm).
      pose (eb0 := eb03 $@R LhV).
      pose (eb1 := eb0 $@
        (((cat_assoc NatA B1 CRBottom $@R LIdV)
          $@R Uterm) $@R LhV)).
      pose (eb2 := eb1 $@
        ((cat_assoc LIdV B2 CRBottom $@R Uterm)
          $@R LhV)).
      pose (eb3 := eb2 $@
        (cat_assoc Uterm B3 CRBottom $@R LhV)).
      pose (eb4 := eb3 $@
        cat_assoc LhV B4 CRBottom).
      exact (eb4 $@ (CRBottom $@L eB5)).
    }
    assert (eBottomGroup : FlatBottom $== WCB).
    {
      change (FlatBottom $==
        (CRBottom $o MidB) $o CLBottom).
      exact (eBottomMid $@R CLBottom).
    }
    assert (ebottomC :
      fun11_fmap F (isnat k f) $== WCB).
    {
      change (fun11_fmap F (isnat k f)
        $== FlatBottom) in ebottom.
      exact (ebottom $@ eBottomGroup).
    }
    nrefine (wholeC $@hL _ $@hR _
      $@vL etopC $@vR ebottomC).
    all: try reflexivity.
  Defined.

  Definition pointwise_limit_eta_modification
    (X : Fun02 J (Fun02 I A)) (P : Fun02 I A)
    (k : P $-> pointwise_limit_apex I A J X)
    : pointwise_limit_corec
        (limit_cone_map X
          (pointwise_limit_apex I A J X)
          (pointwise_limit_cone I A J X) P k)
      $== k.
  Proof.
    snapply Build_NatModification.
    - exact (pointwise_limit_eta_component X P k).
    - intros i i' f.
      pose (D' := pointwise_limit_diagram I A J X i').
      pose (lambda' := cat_limit_cone J D').
      pose (F := limit_cone_map D'
        (pointwise_limit_apex I A J X i')
        lambda' (P i)).
      pose (HF := limit_cone_biinv_direct lambda'
        (cat_islimit_cone J D') (P i)).
      pose (c := fun11_bireflect_square F HF
        (pointwise_limit_eta_naturality_cone X P k f)).
      nrefine (c $@hL _ $@hR _ $@vL _ $@vR _).
      + reflexivity.
      + exact (fun11_bireflect_fmap F HF
          (pointwise_limit_eta_component X P k i'
            $@R fmap P f))^$.
      + exact (fun11_bireflect_fmap F HF
          (fmap (pointwise_limit_apex I A J X) f
            $@L pointwise_limit_eta_component X P k i))^$.
      + exact (fun11_bireflect_fmap F HF (isnat k f))^$.
  Defined.
End PointwiseLimitDirect.
