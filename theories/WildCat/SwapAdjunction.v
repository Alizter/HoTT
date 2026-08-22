Require Import Basics.Overture Basics.PathGroupoids Basics.Tactics.
Require Import WildCat.Adjoint WildCat.Core WildCat.Cylinder WildCat.Equiv
  WildCat.EquivGpd WildCat.FunctorCat WildCat.NatTrans WildCat.OneGroupoid
  WildCat.Opposite WildCat.Square WildCat.TwoFunctor WildCat.TwoOneCat
  WildCat.TwoYoneda WildCat.Yoneda WildCat.ZeroGroupoid.

Set Typeclasses Depth 3.

(** ** The coherent argument-swap adjunction *)
Local Definition cat_assoc_rev_is_opp
  {D : Type} `{Is21Cat D}
  {a b c d : D} (f : a $-> b) (g : b $-> c) (h : c $-> d)
  : (cat_assoc f g h)^$ $== cat_assoc_opp f g h.
Proof.
  symmetry.
  rapply cat_assoc_opp_is_rev.
Defined.
Local Transparent op.


Section Swap02Adjunction.
  Context (A B C : Type) `{IsGraph A, IsGraph B, Is21Cat C}.

  Definition swap_fun02_hom_to_at
    {F : Fun02 A (Fun02 B C)} {G : Fun02 B (Fun02 A C)}
    (alpha : swap_fun02 A B C F $-> G) (a : A)
    : F a $-> swap_fun02 B A C G a.
  Proof.
    snapply Build_NatTrans.
    { exact (fun b => alpha b a). }
    snapply Build_Is1Natural.
    intros b b' g.
    exact (natmod_component _ _
      (isnat (alnat := is1natural_nattrans alpha) alpha g) a).
  Defined.

  Definition natmod_swap_fun02_hom_to_naturality
    {F : Fun02 A (Fun02 B C)} {G : Fun02 B (Fun02 A C)}
    (alpha : swap_fun02 A B C F $-> G)
    {a a' : A} (f : a $-> a')
    : swap_fun02_hom_to_at alpha a' $o fmap F f
      $== fmap (swap_fun02 B A C G) f
        $o swap_fun02_hom_to_at alpha a.
  Proof.
    snapply Build_NatModification.
    { intro b.
      exact (isnat
        (alnat := is1natural_nattrans (alpha b)) (alpha b) f). }
    intros b b' g.
    cbn beta.
    exact (cylinder_rotate_vconcat_transpose_front
      (natmod_isnatural _ _
        (isnat (alnat := is1natural_nattrans alpha) alpha g) f)).
  Defined.

  Definition swap_fun02_hom_to
    (F : Fun02 A (Fun02 B C)) (G : Fun02 B (Fun02 A C))
    : swap_fun02 A B C F $-> G
      -> F $-> swap_fun02 B A C G.
  Proof.
    intro alpha.
    snapply Build_NatTrans.
    { exact (swap_fun02_hom_to_at alpha). }
    snapply Build_Is1Natural.
    intros a a' f.
    exact (natmod_swap_fun02_hom_to_naturality alpha f).
  Defined.

  Definition swap_fun02_hom_from_at
    {F : Fun02 A (Fun02 B C)} {G : Fun02 B (Fun02 A C)}
    (alpha : F $-> swap_fun02 B A C G) (b : B)
    : swap_fun02 A B C F b $-> G b.
  Proof.
    snapply Build_NatTrans.
    { exact (fun a => alpha a b). }
    snapply Build_Is1Natural.
    intros a a' f.
    exact (natmod_component _ _
      (isnat (alnat := is1natural_nattrans alpha) alpha f) b).
  Defined.

  Definition natmod_swap_fun02_hom_from_naturality
    {F : Fun02 A (Fun02 B C)} {G : Fun02 B (Fun02 A C)}
    (alpha : F $-> swap_fun02 B A C G)
    {b b' : B} (g : b $-> b')
    : swap_fun02_hom_from_at alpha b'
        $o fmap (swap_fun02 A B C F) g
      $== fmap G g $o swap_fun02_hom_from_at alpha b.
  Proof.
    snapply Build_NatModification.
    { intro a.
      exact (isnat
        (alnat := is1natural_nattrans (alpha a)) (alpha a) g). }
    intros a a' f.
    cbn beta.
    exact (cylinder_rotate_vconcat_transpose_back
      (natmod_isnatural _ _
        (isnat (alnat := is1natural_nattrans alpha) alpha f) g)).
  Defined.

  Definition swap_fun02_hom_from
    (F : Fun02 A (Fun02 B C)) (G : Fun02 B (Fun02 A C))
    : F $-> swap_fun02 B A C G
      -> swap_fun02 A B C F $-> G.
  Proof.
    intro alpha.
    snapply Build_NatTrans.
    { exact (swap_fun02_hom_from_at alpha). }
    snapply Build_Is1Natural.
    intros b b' g.
    exact (natmod_swap_fun02_hom_from_naturality alpha g).
  Defined.

  Definition natmod_swap_fun02_hom_from_to_at
    (F : Fun02 A (Fun02 B C)) (G : Fun02 B (Fun02 A C))
    (alpha : swap_fun02 A B C F $-> G) (b : B)
    : swap_fun02_hom_from_at (swap_fun02_hom_to F G alpha) b
      $== alpha b.
  Proof.
    snapply Build_NatModification.
    { intro a.
      exact (Id _). }
    intros a a' f.
    exact (cylinder_refl _).
  Defined.

  Definition natmod_swap_fun02_hom_from_to
    (F : Fun02 A (Fun02 B C)) (G : Fun02 B (Fun02 A C))
    (alpha : swap_fun02 A B C F $-> G)
    : swap_fun02_hom_from F G (swap_fun02_hom_to F G alpha)
      $== alpha.
  Proof.
    snapply Build_NatModification.
    { exact (natmod_swap_fun02_hom_from_to_at F G alpha). }
    intros b b' g a.
    exact (cylinder_refl _).
  Defined.

  Definition natmod_swap_fun02_hom_to_from_at
    (F : Fun02 A (Fun02 B C)) (G : Fun02 B (Fun02 A C))
    (alpha : F $-> swap_fun02 B A C G) (a : A)
    : swap_fun02_hom_to_at (swap_fun02_hom_from F G alpha) a
      $== alpha a.
  Proof.
    snapply Build_NatModification.
    { intro b.
      exact (Id _). }
    intros b b' g.
    exact (cylinder_refl _).
  Defined.

  Definition natmod_swap_fun02_hom_to_from
    (F : Fun02 A (Fun02 B C)) (G : Fun02 B (Fun02 A C))
    (alpha : F $-> swap_fun02 B A C G)
    : swap_fun02_hom_to F G (swap_fun02_hom_from F G alpha)
      $== alpha.
  Proof.
    snapply Build_NatModification.
    { exact (natmod_swap_fun02_hom_to_from_at F G alpha). }
    intros a a' f b.
    exact (cylinder_refl _).
  Defined.

  Definition natmod_swap_fun02_hom_to_at
    (F : Fun02 A (Fun02 B C)) (G : Fun02 B (Fun02 A C))
    {alpha beta : swap_fun02 A B C F $-> G}
    (p : alpha $== beta) (a : A)
    : swap_fun02_hom_to_at alpha a
      $== swap_fun02_hom_to_at beta a.
  Proof.
    snapply Build_NatModification.
    { intro b.
      exact (natmod_component
        (alpha b) (beta b) (natmod_component alpha beta p b) a). }
    intros b b' g.
    exact (natmod_isnatural alpha beta p g a).
  Defined.

  Definition natmod_swap_fun02_hom_to
    (F : Fun02 A (Fun02 B C)) (G : Fun02 B (Fun02 A C))
    {alpha beta : swap_fun02 A B C F $-> G}
    (p : alpha $== beta)
    : swap_fun02_hom_to F G alpha
      $== swap_fun02_hom_to F G beta.
  Proof.
    snapply Build_NatModification.
    { exact (natmod_swap_fun02_hom_to_at F G p). }
    intros a a' f b.
    exact (natmod_isnatural
      (alpha b) (beta b) (natmod_component alpha beta p b) f).
  Defined.

  Definition natmod_swap_fun02_hom_from_at
    (F : Fun02 A (Fun02 B C)) (G : Fun02 B (Fun02 A C))
    {alpha beta : F $-> swap_fun02 B A C G}
    (p : alpha $== beta) (b : B)
    : swap_fun02_hom_from_at alpha b
      $== swap_fun02_hom_from_at beta b.
  Proof.
    snapply Build_NatModification.
    { intro a.
      exact (natmod_component
        (alpha a) (beta a) (natmod_component alpha beta p a) b). }
    intros a a' f.
    exact (natmod_isnatural alpha beta p f b).
  Defined.

  Definition natmod_swap_fun02_hom_from
    (F : Fun02 A (Fun02 B C)) (G : Fun02 B (Fun02 A C))
    {alpha beta : F $-> swap_fun02 B A C G}
    (p : alpha $== beta)
    : swap_fun02_hom_from F G alpha
      $== swap_fun02_hom_from F G beta.
  Proof.
    snapply Build_NatModification.
    { exact (natmod_swap_fun02_hom_from_at F G p). }
    intros b b' g a.
    exact (natmod_isnatural
      (alpha a) (beta a) (natmod_component alpha beta p a) g).
  Defined.

  Definition fun01_swap_fun02_hom_to
    (F : Fun02 A (Fun02 B C)) (G : Fun02 B (Fun02 A C))
    : opyon_0gpd (swap_fun02 A B C F) G
      $-> opyon_0gpd F (swap_fun02 B A C G).
  Proof.
    snapply Build_Fun01'.
    { exact (swap_fun02_hom_to F G). }
    intros alpha beta p.
    exact (natmod_swap_fun02_hom_to F G p).
  Defined.

  Definition fun01_swap_fun02_hom_from
    (F : Fun02 A (Fun02 B C)) (G : Fun02 B (Fun02 A C))
    : opyon_0gpd F (swap_fun02 B A C G)
      $-> opyon_0gpd (swap_fun02 A B C F) G.
  Proof.
    snapply Build_Fun01'.
    { exact (swap_fun02_hom_from F G). }
    intros alpha beta p.
    exact (natmod_swap_fun02_hom_from F G p).
  Defined.

  Definition cylinder_swap_fun02_hom_to_precompose_at_naturality
    {F F' : Fun02 A (Fun02 B C)} (alpha : F' $-> F)
    {G : Fun02 B (Fun02 A C)}
    (beta : swap_fun02 A B C F $-> G) (a : A)
    {b b' : B} (g : b $-> b')
    : Cylinder
        (Id (beta b a $o alpha a b))
        (Id (beta b' a $o alpha a b'))
        (isnat (swap_fun02_hom_to_at
          (beta $o nattrans_swap_fun02 A B C alpha) a) g)
        (isnat (alpha a) g $@v
          isnat (swap_fun02_hom_to_at beta a) g).
  Proof.
    rapply cylinder_rewrite_back.
    { rapply cat_prewhisker.
      rapply cat_postwhisker.
      rapply cat_postwhisker.
      rapply cat_assoc_opp_is_rev. }
    exact (cylinder_refl _).
  Defined.

  Definition natmod_swap_fun02_hom_to_precompose_at
    {F F' : Fun02 A (Fun02 B C)} (alpha : F' $-> F)
    {G : Fun02 B (Fun02 A C)}
    (beta : swap_fun02 A B C F $-> G) (a : A)
    : swap_fun02_hom_to_at
        (beta $o nattrans_swap_fun02 A B C alpha) a
      $== swap_fun02_hom_to_at beta a $o alpha a.
  Proof.
    snapply Build_NatModification.
    { intro b.
      exact (Id _). }
    intros b b' g.
    exact (cylinder_swap_fun02_hom_to_precompose_at_naturality
      alpha beta a g).
  Defined.

  Definition edge_swap_fun02_hom_to_precompose_front
    {F F' : Fun02 A (Fun02 B C)} (alpha : F' $-> F)
    {G : Fun02 B (Fun02 A C)}
    (beta : swap_fun02 A B C F $-> G) (a : A) (b : B)
    := swap_fun02_hom_to_at
         (beta $o nattrans_swap_fun02 A B C alpha) a b.

  Definition edge_swap_fun02_hom_to_precompose_back
    {F F' : Fun02 A (Fun02 B C)} (alpha : F' $-> F)
    {G : Fun02 B (Fun02 A C)}
    (beta : swap_fun02 A B C F $-> G) (a : A) (b : B)
    := (swap_fun02_hom_to_at beta a $o alpha a) b.

  Definition cell_swap_fun02_hom_to_precompose
    {F F' : Fun02 A (Fun02 B C)} (alpha : F' $-> F)
    {G : Fun02 B (Fun02 A C)}
    (beta : swap_fun02 A B C F $-> G) (a : A) (b : B)
    : edge_swap_fun02_hom_to_precompose_front alpha beta a b
      $== edge_swap_fun02_hom_to_precompose_back alpha beta a b
    := natmod_component _ _
         (natmod_swap_fun02_hom_to_precompose_at alpha beta a) b.

  Definition square_swap_fun02_hom_to_precompose_front
    {F F' : Fun02 A (Fun02 B C)} (alpha : F' $-> F)
    {G : Fun02 B (Fun02 A C)}
    (beta : swap_fun02 A B C F $-> G)
    {a a' : A} (f : a $-> a') (b : B)
    : Square
        (edge_swap_fun02_hom_to_precompose_front alpha beta a b)
        (edge_swap_fun02_hom_to_precompose_front alpha beta a' b)
        (fmap F' f b)
        (fmap (swap_fun02 B A C G) f b)
    := natmod_component _ _
         (natmod_swap_fun02_hom_to_naturality
           (beta $o nattrans_swap_fun02 A B C alpha) f) b.

  Definition square_swap_fun02_hom_to_precompose_back
    {F F' : Fun02 A (Fun02 B C)} (alpha : F' $-> F)
    {G : Fun02 B (Fun02 A C)}
    (beta : swap_fun02 A B C F $-> G)
    {a a' : A} (f : a $-> a') (b : B)
    : Square
        (edge_swap_fun02_hom_to_precompose_back alpha beta a b)
        (edge_swap_fun02_hom_to_precompose_back alpha beta a' b)
        (fmap F' f b)
        (fmap (swap_fun02 B A C G) f b)
    := natmod_component _ _
         (isnat (alnat := is1natural_nattrans alpha) alpha f $@v
          natmod_swap_fun02_hom_to_naturality beta f) b.

  Definition square_swap_fun02_hom_to_precompose
    {F F' : Fun02 A (Fun02 B C)} (alpha : F' $-> F)
    {G : Fun02 B (Fun02 A C)}
    (beta : swap_fun02 A B C F $-> G)
    {a a' : A} (f : a $-> a') (b : B)
    : square_swap_fun02_hom_to_precompose_back alpha beta f b
      $== square_swap_fun02_hom_to_precompose_front alpha beta f b.
  Proof.
    unfold square_swap_fun02_hom_to_precompose_back.
    unfold square_swap_fun02_hom_to_precompose_front.
    rapply cat_prewhisker.
    rapply cat_postwhisker.
    rapply cat_postwhisker.
    nrefine (cat_assoc_rev_is_opp _ _ _).
  Defined.

  Definition cylinder_swap_fun02_hom_to_precompose_at
    {F F' : Fun02 A (Fun02 B C)} (alpha : F' $-> F)
    {G : Fun02 B (Fun02 A C)}
    (beta : swap_fun02 A B C F $-> G)
    {a a' : A} (f : a $-> a') (b : B)
    : Cylinder
        (f := fmap F' f b)
        (g := fmap (swap_fun02 B A C G) f b)
        (cell_swap_fun02_hom_to_precompose alpha beta a b)
        (cell_swap_fun02_hom_to_precompose alpha beta a' b)
        (square_swap_fun02_hom_to_precompose_front alpha beta f b)
        (square_swap_fun02_hom_to_precompose_back alpha beta f b).
  Proof.
    unfold cell_swap_fun02_hom_to_precompose.
    unfold edge_swap_fun02_hom_to_precompose_front.
    unfold edge_swap_fun02_hom_to_precompose_back.
    unfold natmod_swap_fun02_hom_to_precompose_at.
    unfold swap_fun02_hom_to_at.
    unfold natmod_component.
    rapply cylinder_rewrite_front.
    { symmetry.
      rapply square_swap_fun02_hom_to_precompose. }
    exact (cylinder_refl _).
  Defined.

  Definition cylinder_swap_fun02_hom_to_precompose
    {F F' : Fun02 A (Fun02 B C)} (alpha : F' $-> F)
    {G : Fun02 B (Fun02 A C)}
    (beta : swap_fun02 A B C F $-> G)
    {a a' : A} (f : a $-> a')
    : Cylinder
        (natmod_swap_fun02_hom_to_precompose_at alpha beta a)
        (natmod_swap_fun02_hom_to_precompose_at alpha beta a')
        (natmod_swap_fun02_hom_to_naturality
          (beta $o nattrans_swap_fun02 A B C alpha) f)
        (isnat alpha f $@v
          natmod_swap_fun02_hom_to_naturality beta f).
  Proof.
    rapply Build_Cylinder_fun02.
    intro b.
    nrefine (cylinder_swap_fun02_hom_to_precompose_at alpha beta f b).
  Defined.

  Definition natmod_swap_fun02_hom_to_precompose
    {F F' : Fun02 A (Fun02 B C)} (alpha : F' $-> F)
    {G : Fun02 B (Fun02 A C)}
    (beta : swap_fun02 A B C F $-> G)
    : swap_fun02_hom_to F' G
        (beta $o nattrans_swap_fun02 A B C alpha)
      $== swap_fun02_hom_to F G beta $o alpha.
  Proof.
    snapply Build_NatModification.
    { exact (natmod_swap_fun02_hom_to_precompose_at alpha beta). }
    intros a a' f.
    exact (cylinder_swap_fun02_hom_to_precompose alpha beta f).
  Defined.

  Definition equiv_swap_fun02_hom
    (F : Fun02 A (Fun02 B C)) (G : Fun02 B (Fun02 A C))
    : opyon_0gpd (swap_fun02 A B C F) G
      $<~> opyon_0gpd F (swap_fun02 B A C G)
    := cate_adjointify
      (fun01_swap_fun02_hom_to F G)
      (fun01_swap_fun02_hom_from F G)
      (natmod_swap_fun02_hom_to_from F G)
      (natmod_swap_fun02_hom_from_to F G).

  (** The argument-swap equivalence on natural transformations retains the
      modifications and perturbations in the hom 1-groupoids. *)
  Definition fun11_swap_fun02_hom_to
    (F : Fun02 A (Fun02 B C)) (G : Fun02 B (Fun02 A C))
    : Fun11
        (hom_1gpd (swap_fun02 A B C F) G)
        (hom_1gpd F (swap_fun02 B A C G)).
  Proof.
    snapply Build_Fun11.
    - exact (swap_fun02_hom_to F G).
    - snapply Build_Is0Functor.
      exact (fun alpha beta p =>
        natmod_swap_fun02_hom_to F G p).
    - snapply Build_Is1Functor.
      + intros alpha beta p q h a b. exact (h b a).
      + intros alpha a b. exact (Id _).
      + intros alpha beta gamma p q a b. exact (Id _).
  Defined.

  Definition fun11_swap_fun02_hom_from
    (F : Fun02 A (Fun02 B C)) (G : Fun02 B (Fun02 A C))
    : Fun11
        (hom_1gpd F (swap_fun02 B A C G))
        (hom_1gpd (swap_fun02 A B C F) G).
  Proof.
    snapply Build_Fun11.
    - exact (swap_fun02_hom_from F G).
    - snapply Build_Is0Functor.
      exact (fun alpha beta p =>
        natmod_swap_fun02_hom_from F G p).
    - snapply Build_Is1Functor.
      + intros alpha beta p q h b a. exact (h a b).
      + intros alpha b a. exact (Id _).
      + intros alpha beta gamma p q b a. exact (Id _).
  Defined.

  Definition nattrans_fun11_swap_fun02_hom_to_from
    (F : Fun02 A (Fun02 B C)) (G : Fun02 B (Fun02 A C))
    : NatTrans
        (fun11_compose
          (fun11_swap_fun02_hom_to F G)
          (fun11_swap_fun02_hom_from F G))
        (Id (hom_1gpd F (swap_fun02 B A C G))).
  Proof.
    snapply Build_NatTrans.
    - exact (natmod_swap_fun02_hom_to_from F G).
    - snapply Build_Is1Natural.
      intros alpha beta p a b.
      exact (cat_idl _ $@ (cat_idr _)^$).
  Defined.

  Definition nattrans_fun11_swap_fun02_hom_from_to
    (F : Fun02 A (Fun02 B C)) (G : Fun02 B (Fun02 A C))
    : NatTrans
        (fun11_compose
          (fun11_swap_fun02_hom_from F G)
          (fun11_swap_fun02_hom_to F G))
        (Id (hom_1gpd (swap_fun02 A B C F) G)).
  Proof.
    snapply Build_NatTrans.
    - exact (natmod_swap_fun02_hom_from_to F G).
    - snapply Build_Is1Natural.
      intros alpha beta p b a.
      exact (cat_idl _ $@ (cat_idr _)^$).
  Defined.

  Global Instance catie_fun11_swap_fun02_hom_to
    (F : Fun02 A (Fun02 B C)) (G : Fun02 B (Fun02 A C))
    : @Cat_IsBiInv OneGpd isgraph_1gpd is2graph_1gpd
        is01cat_1gpd is1cat_1gpd
        (hom_1gpd (swap_fun02 A B C F) G)
        (hom_1gpd F (swap_fun02 B A C G))
        (fun11_swap_fun02_hom_to F G).
  Proof.
    snapply Build_Cat_IsBiInv.
    - exact (fun11_swap_fun02_hom_from F G).
    - exact (nattrans_fun11_swap_fun02_hom_to_from F G).
    - exact (fun11_swap_fun02_hom_from F G).
    - exact (nattrans_fun11_swap_fun02_hom_from_to F G).
  Defined.

  Local Definition equiv_swap_fun02_hom_op
    (F : (Fun02 A (Fun02 B C))^op)
    (G : Fun02 B (Fun02 A C))
    : yon_0gpd G (swap_fun02 A B C F)
      $<~> yon_0gpd (swap_fun02 B A C G) F.
  Proof.
    unfold yon_0gpd, opyon_0gpd, op.
    exact (equiv_swap_fun02_hom F G).
  Defined.

  Local Instance is1natural_equiv_swap_fun02_hom_l
    (G : Fun02 B (Fun02 A C))
    : Is1Natural (A := (Fun02 A (Fun02 B C))^op) (B := ZeroGpd)
        (isgraph_A := isgraph_op)
        (is0functor_F := @is0functor_compose
          ((Fun02 A (Fun02 B C))^op)
          ((Fun02 B (Fun02 A C))^op) ZeroGpd
          isgraph_op isgraph_op isgraph_0gpd
          (swap_fun02 A B C)
          (is0functor_op _ _ (swap_fun02 A B C))
          (yon_0gpd G) (is0functor_yon_0gpd G))
        (is0functor_G := is0functor_yon_0gpd
          (swap_fun02 B A C G))
        (yon_0gpd G o swap_fun02 A B C)
        (yon_0gpd (swap_fun02 B A C G))
        (fun F => cate_fun (equiv_swap_fun02_hom_op F G)).
  Proof.
    snapply Build_Is1Natural.
    intros F F' alpha beta.
    nrefine (natmod_swap_fun02_hom_to_precompose alpha beta).
  Defined.

  Definition natequiv_swap_fun02_hom_l
    (G : Fun02 B (Fun02 A C))
    : NatEquiv (A := (Fun02 A (Fun02 B C))^op)
        (is0functor_F := @is0functor_compose
          ((Fun02 A (Fun02 B C))^op)
          ((Fun02 B (Fun02 A C))^op) ZeroGpd
          isgraph_op isgraph_op isgraph_0gpd
          (swap_fun02 A B C)
          (is0functor_op _ _ (swap_fun02 A B C))
          (yon_0gpd G) (is0functor_yon_0gpd G))
        (is0functor_G := is0functor_yon_0gpd
          (swap_fun02 B A C G))
        (yon_0gpd G o swap_fun02 A B C)
        (yon_0gpd (swap_fun02 B A C G)).
  Proof.
    snapply Build_NatEquiv.
    { exact (fun F => equiv_swap_fun02_hom_op F G). }
    exact (is1natural_equiv_swap_fun02_hom_l G).
  Defined.

  Definition natmod_swap_fun02_hom_to_postcompose_at
    {F : Fun02 A (Fun02 B C)}
    {G G' : Fun02 B (Fun02 A C)} (alpha : G $-> G')
    (beta : swap_fun02 A B C F $-> G) (a : A)
    : swap_fun02_hom_to_at (alpha $o beta) a
      $== nattrans_swap_fun02_at B A C alpha a
        $o swap_fun02_hom_to_at beta a.
  Proof.
    nrefine (natmod_swap_fun02_comp_at B A C beta alpha a).
  Defined.

  Definition cylinder_swap_fun02_hom_to_postcompose
    {F : Fun02 A (Fun02 B C)}
    {G G' : Fun02 B (Fun02 A C)} (alpha : G $-> G')
    (beta : swap_fun02 A B C F $-> G)
    {a a' : A} (f : a $-> a')
    : Cylinder
        (natmod_swap_fun02_hom_to_postcompose_at alpha beta a)
        (natmod_swap_fun02_hom_to_postcompose_at alpha beta a')
        (natmod_swap_fun02_hom_to_naturality (alpha $o beta) f)
        (natmod_swap_fun02_hom_to_naturality beta f $@v
          natmod_swap_fun02_naturality B A C alpha f).
  Proof.
    nrefine (natmod_isnatural _ _
      (natmod_swap_fun02_comp B A C beta alpha) f).
  Defined.

  Definition natmod_swap_fun02_hom_to_postcompose
    {F : Fun02 A (Fun02 B C)}
    {G G' : Fun02 B (Fun02 A C)} (alpha : G $-> G')
    (beta : swap_fun02 A B C F $-> G)
    : swap_fun02_hom_to F G' (alpha $o beta)
      $== nattrans_swap_fun02 B A C alpha
        $o swap_fun02_hom_to F G beta.
  Proof.
    snapply Build_NatModification.
    { exact (natmod_swap_fun02_hom_to_postcompose_at alpha beta). }
    intros a a' f.
    exact (cylinder_swap_fun02_hom_to_postcompose alpha beta f).
  Defined.

  Local Instance is1natural_equiv_swap_fun02_hom_r
    (F : Fun02 A (Fun02 B C))
    : Is1Natural
        (is0functor_F := is0functor_opyon_0gpd
          (swap_fun02 A B C F))
        (is0functor_G := is0functor_compose
          (A := Fun02 B (Fun02 A C))
          (B := Fun02 A (Fun02 B C))
          (C := ZeroGpd)
          (swap_fun02 B A C) (opyon_0gpd F))
        (opyon_0gpd (swap_fun02 A B C F))
        (opyon_0gpd F o swap_fun02 B A C)
        (fun G => cate_fun (equiv_swap_fun02_hom F G)).
  Proof.
    snapply Build_Is1Natural.
    intros G G' alpha beta.
    nrefine (natmod_swap_fun02_hom_to_postcompose alpha beta).
  Defined.

  Definition natequiv_swap_fun02_hom_r
    (F : Fun02 A (Fun02 B C))
    : NatEquiv
        (is0functor_F := is0functor_opyon_0gpd
          (swap_fun02 A B C F))
        (is0functor_G := is0functor_compose
          (A := Fun02 B (Fun02 A C))
          (B := Fun02 A (Fun02 B C))
          (C := ZeroGpd)
          (swap_fun02 B A C) (opyon_0gpd F))
        (opyon_0gpd (swap_fun02 A B C F))
        (opyon_0gpd F o swap_fun02 B A C).
  Proof.
    snapply Build_NatEquiv.
    { exact (equiv_swap_fun02_hom F). }
    exact (is1natural_equiv_swap_fun02_hom_r F).
  Defined.

  Definition gpd_adjunction_swap_fun02
    : GpdAdjunction
        (swap_fun02 A B C)
        (swap_fun02 B A C).
  Proof.
    snapply Build_GpdAdjunction.
    { exact equiv_swap_fun02_hom. }
    { exact is1natural_equiv_swap_fun02_hom_l. }
    exact is1natural_equiv_swap_fun02_hom_r.
  Defined.
End Swap02Adjunction.
