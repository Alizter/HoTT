Require Import Basics.Overture Basics.Tactics.
Require Import WildCat.Core WildCat.NatTrans WildCat.FunctorCat WildCat.TwoOneCat
  WildCat.Cylinder WildCat.Equiv WildCat.OneGroupoid WildCat.Square
  WildCat.TwoFunctor.

Set Typeclasses Depth 3.

(** * Coherent Yoneda lemmas valued in 1-groupoids *)

Definition opyon_1gpd {A : Type} `{Is21Cat A} (a b : A)
  : OneGpd.
Proof.
  napply (Build_OneGpd (a $-> b)).
  all: exact _.
Defined.

Instance is0functor_opyon_1gpd
  {A : Type} `{Is21Cat A} (a : A)
  : Is0Functor (opyon_1gpd a).
Proof.
  snapply Build_Is0Functor.
  intros b c f.
  napply (Build_Fun11 _ _ (cat_postcomp a f)).
  exact (is1functor_postcomp a b c f).
Defined.

Definition opyon0_1gpd
  {A : Type} `{Is21Cat A} (a : A)
  : Fun02 A OneGpd
  := Build_Fun02 (opyon_1gpd a).

Definition fmap2_opyon_1gpd
  {A : Type} `{Is21Cat A} (a : A)
  {b c : A} {f g : b $-> c} (p : f $== g)
  : fmap (opyon_1gpd a) f $== fmap (opyon_1gpd a) g.
Proof.
  snapply Build_NatTrans.
  1: exact (fun h => p $@R h).
  snapply Build_Is1Natural.
  intros h h' q.
  exact (bifunctor_coh_comp q p)^$.
Defined.

Definition fmap_id_opyon_1gpd
  {A : Type} `{Is21Cat A} (a b : A)
  : fmap (opyon_1gpd a) (Id b) $== Id (opyon_1gpd a b).
Proof.
  snapply Build_NatTrans.
  1: exact cat_idl.
  exact (is1natural_cat_idl a b).
Defined.

Definition fmap_comp_opyon_1gpd
  {A : Type} `{Is21Cat A} (a : A)
  {b c d : A} (f : b $-> c) (g : c $-> d)
  : fmap (opyon_1gpd a) (g $o f)
    $== fmap (opyon_1gpd a) g $o fmap (opyon_1gpd a) f.
Proof.
  snapply Build_NatTrans.
  1: exact (fun h => cat_assoc h f g).
  exact (is1natural_cat_assoc_r a b c d f g).
Defined.

Instance is1functor_opyon_1gpd
  {A : Type} `{Is21Cat A} (a : A)
  : Is1Functor (opyon_1gpd a).
Proof.
  snapply Build_Is1Functor.
  - exact (fun b c f g => fmap2_opyon_1gpd a).
  - exact (fmap_id_opyon_1gpd a).
  - exact (fun b c d => fmap_comp_opyon_1gpd a).
Defined.

Definition opyon1_1gpd
  {A : Type} `{Is21Cat A} (a : A)
  : Fun12 A OneGpd
  := Build_Fun12 (opyon_1gpd a).

Definition is1functor_fmap_opyon_1gpd
  {A : Type} `{Is21Cat A} (a b c : A)
  : Is1Functor (@fmap A OneGpd _ _ (opyon_1gpd a) _ b c).
Proof.
  snapply Build_Is1Functor.
  - intros f g p q r h.
    exact (fmap2 (cat_precomp c h) r).
  - intros f h.
    exact (fmap_id (cat_precomp c h) f).
  - intros f g k p q h.
    exact (fmap_comp (cat_precomp c h) p q).
Defined.

Definition fmap_comp_natural_opyon_1gpd
  {A : Type} `{Is21Cat A} (a : A)
  {b c d : A}
  {f f' : b $-> c} {g g' : c $-> d}
  (p : f $== f') (q : g $== g')
  : fmap2 (opyon_1gpd a) (p $@@ q)
      $@ fmap_comp (opyon_1gpd a) f' g'
    $== fmap_comp (opyon_1gpd a) f g
      $@ (fmap2 (opyon_1gpd a) p $@@
        fmap2 (opyon_1gpd a) q).
Proof.
  intro k.
  change ((((p $@@ q) $@R k) $@ cat_assoc k f' g')
    $== cat_assoc k f g $@
      ((q $@R (f $o k)) $@ (g' $@L (p $@R k)))).
  lhs' exact (cat_assoc k f' g' $@L
    cat_prewhisker_pp k (q $@R f) (g' $@L p)).
  lhs' exact (cat_assoc_opp
    ((q $@R f) $@R k)
    ((g' $@L p) $@R k)
    (cat_assoc k f' g')).
  lhs' exact (cat_assoc_natural_m k p g' $@R
    ((q $@R f) $@R k)).
  lhs' exact (cat_assoc
    ((q $@R f) $@R k)
    (cat_assoc k f g')
    (g' $@L (p $@R k))).
  lhs' exact ((g' $@L (p $@R k)) $@L
    cat_assoc_natural_l k f q).
  exact (cat_assoc_opp
    (cat_assoc k f g)
    (q $@R (f $o k))
    (g' $@L (p $@R k))).
Defined.

Definition fmap_assoc_opyon_1gpd
  {A : Type} `{Is21Cat A} (a : A)
  {b c d e : A}
  (f : b $-> c) (g : c $-> d) (h : d $-> e)
  : fmap2 (opyon_1gpd a) (cat_assoc f g h)
      $@ fmap_comp (opyon_1gpd a) (g $o f) h
      $@ (fmap (opyon_1gpd a) h $@L
        fmap_comp (opyon_1gpd a) f g)
    $== fmap_comp (opyon_1gpd a) f (h $o g)
      $@ (fmap_comp (opyon_1gpd a) g h $@R
        fmap (opyon_1gpd a) f)
      $@ cat_assoc
        (fmap (opyon_1gpd a) f)
        (fmap (opyon_1gpd a) g)
        (fmap (opyon_1gpd a) h).
Proof.
  intro k.
  change (((cat_assoc f g h $@R k)
      $@ cat_assoc k (g $o f) h
      $@ (h $@L cat_assoc k f g))
    $== (cat_assoc k f (h $o g)
      $@ cat_assoc (f $o k) g h
      $@ Id (h $o (g $o (f $o k))))).
  nrefine (cat_assoc_opp
    (cat_assoc f g h $@R k)
    (cat_assoc k (g $o f) h)
    (h $@L cat_assoc k f g) $@ _).
  nrefine (cat_pentagon
    (A := A) a b c d e k f g h $@ _).
  symmetry.
  rapply cat_idl.
Defined.

Definition fmap_idr_opyon_1gpd
  {A : Type} `{Is21Cat A} (a : A)
  {b c : A} (f : b $-> c)
  : fmap2 (opyon_1gpd a) (cat_idr f)
    $== fmap_comp (opyon_1gpd a) (Id b) f
      $@ (fmap (opyon_1gpd a) f $@L
        fmap_id (opyon_1gpd a) b)
      $@ cat_idr (fmap (opyon_1gpd a) f).
Proof.
  intro k.
  change ((cat_idr f $@R k)
    $== cat_assoc k (Id b) f
      $@ (f $@L cat_idl k)
      $@ Id (f $o k)).
  exact ((cat_tril (A := A) a b c k f)^$ $@ (cat_idl _)^$).
Defined.

Definition fmap_idl_opyon_1gpd
  {A : Type} `{Is21Cat A} (a : A)
  {b c : A} (f : b $-> c)
  : fmap2 (opyon_1gpd a) (cat_idl f)
    $== fmap_comp (opyon_1gpd a) f (Id c)
      $@ (fmap_id (opyon_1gpd a) c $@R
        fmap (opyon_1gpd a) f)
      $@ cat_idl (fmap (opyon_1gpd a) f).
Proof.
  intro k.
  change ((cat_idl f $@R k)
    $== cat_assoc k f (Id c)
      $@ cat_idl (f $o k)
      $@ Id (f $o k)).
  exact (cat_idl_assoc k f $@ (cat_idl _)^$).
Defined.

Instance is2functor_opyon_1gpd
  {A : Type} `{Is21Cat A} (a : A)
  : Is2Functor (opyon_1gpd a).
Proof.
  snapply Build_Is2Functor.
  - exact (is1functor_fmap_opyon_1gpd a).
  - exact (fun b c d f f' g g' =>
      fmap_comp_natural_opyon_1gpd a).
  - exact (fun b c d e => fmap_assoc_opyon_1gpd a).
  - exact (fun b c => fmap_idl_opyon_1gpd a).
  - exact (fun b c => fmap_idr_opyon_1gpd a).
Defined.

Definition opyon2_1gpd
  {A : Type} `{Is21Cat A} (a : A)
  : Fun22 A OneGpd
  := Build_Fun22 (opyon_1gpd a).

Definition pseudonat_1gpd
  {A : Type} `{Is21Cat A} (F G : Fun22 A OneGpd)
  : OneGpd.
Proof.
  napply (Build_OneGpd (PseudoNatTrans F G)).
  all: exact _.
Defined.

Definition un_opyoneda_1gpd
  {A : Type} `{Is21Cat A} (F : Fun22 A OneGpd) (a : A)
  : pseudonat_1gpd (opyon2_1gpd a) F -> F a
  := fun alpha => alpha a (Id a).

Instance is0functor_un_opyoneda_1gpd
  {A : Type} `{Is21Cat A} (F : Fun22 A OneGpd) (a : A)
  : Is0Functor (un_opyoneda_1gpd F a).
Proof.
  snapply Build_Is0Functor.
  intros alpha beta p.
  exact (modification_component p a (Id a)).
Defined.

Instance is1functor_un_opyoneda_1gpd
  {A : Type} `{Is21Cat A} (F : Fun22 A OneGpd) (a : A)
  : Is1Functor (un_opyoneda_1gpd F a).
Proof.
  snapply Build_Is1Functor.
  - intros alpha beta p q h.
    exact (h a (Id a)).
  - intros alpha.
    exact (Id _).
  - intros alpha beta gamma p q.
    exact (Id _).
Defined.

Definition un_opyoneda1_1gpd
  {A : Type} `{Is21Cat A} (F : Fun22 A OneGpd) (a : A)
  : pseudonat_1gpd (opyon2_1gpd a) F $-> F a
  := Build_Fun11 _ _ (un_opyoneda_1gpd F a).

Definition opyoneda_map_1gpd
  {A : Type} `{Is21Cat A} (F : Fun22 A OneGpd)
  (a : A) (x : F a) (b : A)
  : opyon_1gpd a b -> F b
  := fun f => fmap F f x.

Instance is0functor_opyoneda_map_1gpd
  {A : Type} `{Is21Cat A} (F : Fun22 A OneGpd)
  (a : A) (x : F a) (b : A)
  : Is0Functor (opyoneda_map_1gpd F a x b).
Proof.
  snapply Build_Is0Functor.
  intros f g p.
  exact (fmap2 F p x).
Defined.

Instance is1functor_opyoneda_map_1gpd
  {A : Type} `{Is21Cat A} (F : Fun22 A OneGpd)
  (a : A) (x : F a) (b : A)
  : Is1Functor (opyoneda_map_1gpd F a x b).
Proof.
  snapply Build_Is1Functor.
  - intros f g p q h.
    exact (fmap3 F h x).
  - intros f.
    exact (fmap_id (@fmap _ _ _ _ F _ a b) f x).
  - intros f g h p q.
    exact (fmap_comp (@fmap _ _ _ _ F _ a b) p q x).
Defined.

Definition opyoneda_component_1gpd
  {A : Type} `{Is21Cat A} (F : Fun22 A OneGpd)
  (a : A) (x : F a) (b : A)
  : opyon_1gpd a b $-> F b
  := Build_Fun11 _ _ (opyoneda_map_1gpd F a x b).

Definition opyoneda_naturality_1gpd
  {A : Type} `{Is21Cat A} (F : Fun22 A OneGpd)
  (a : A) (x : F a) {b c : A} (h : b $-> c)
  : opyoneda_component_1gpd F a x c $o
      fmap (opyon2_1gpd a) h
    $== fmap F h $o opyoneda_component_1gpd F a x b.
Proof.
  snapply Build_NatTrans.
  - exact (fun f => fmap_comp F f h x).
  - snapply Build_Is1Natural.
    intros f g p.
    cbn.
    exact ((@fmap2_postwhisker
      A OneGpd
      IsGraph0 Is2Graph0 Is01Cat0 H Is3Graph0 H0
      isgraph_1gpd is2graph_1gpd is01cat_1gpd is1cat_1gpd
      is3graph_1gpd is21cat_1gpd
      F _ _ _ a b c f g p h) x)^$.
Defined.

Definition opyoneda_nattrans_1gpd
  {A : Type} `{Is21Cat A} (F : Fun22 A OneGpd)
  (a : A) (x : F a)
  : NatTrans (opyon2_1gpd a) F.
Proof.
  snapply Build_NatTrans.
  - exact (opyoneda_component_1gpd F a x).
  - snapply Build_Is1Natural.
    intros b c f.
    exact (opyoneda_naturality_1gpd F a x f).
Defined.

Definition opyoneda_2cell_1gpd
  {A : Type} `{Is21Cat A} (F : Fun22 A OneGpd)
  (a : A) (x : F a)
  {b c : A} {f g : b $-> c} (p : f $== g)
  : Square
      (opyoneda_naturality_1gpd F a x f)
      (opyoneda_naturality_1gpd F a x g)
      (opyoneda_component_1gpd F a x c $@L
        fmap2 (opyon2_1gpd a) p)
      (fmap2 F p $@R opyoneda_component_1gpd F a x b).
Proof.
  intro k.
  exact ((@fmap2_prewhisker
    A OneGpd
    IsGraph0 Is2Graph0 Is01Cat0 H Is3Graph0 H0
    isgraph_1gpd is2graph_1gpd is01cat_1gpd is1cat_1gpd
    is3graph_1gpd is21cat_1gpd
    F _ _ _ a b c k f g p) x)^$.
Defined.

Definition opyoneda_id_1gpd
  {A : Type} `{Is21Cat A} (F : Fun22 A OneGpd)
  (a : A) (x : F a) (b : A)
  : isnat (opyoneda_nattrans_1gpd F a x) (Id b)
    $== (opyoneda_nattrans_1gpd F a x b $@L
          fmap_id (opyon2_1gpd a) b)
      $@ cat_idr (opyoneda_nattrans_1gpd F a x b)
      $@ (cat_idl (opyoneda_nattrans_1gpd F a x b))^$
      $@ ((fmap_id F b $@R
          opyoneda_nattrans_1gpd F a x b)^$).
Proof.
  intro k.
  change (GpdHom
    (A := @Hom (F b) _
      (fmap F (Id b $o k) x)
      (fmap F (Id b) (fmap F k x)))
    (fmap_comp F k (Id b) x)
    (@gpd_comp (F b) _ _ _
      (fmap F (Id b $o k) x)
      (fmap F k x)
      (fmap F (Id b) (fmap F k x))
      (@gpd_comp (F b) _ _ _
        (fmap F (Id b $o k) x)
        (fmap F k x)
        (fmap F k x)
        (@gpd_comp (F b) _ _ _
          (fmap F (Id b $o k) x)
          (fmap F k x)
          (fmap F k x)
          (fmap2 F (cat_idl k) x)
          (@Id (F b) _ _ (fmap F k x)))
        (@gpd_rev (F b) _ _ _ _ _
          (@Id (F b) _ _ (fmap F k x))))
      (@gpd_rev (F b) _ _ _ _ _
        (fmap_id F b (fmap F k x))))).
  apply gpd_moveL_Vh.
  lhs' exact (cat_idl _)^$.
  lhs' exact ((fmap_idl (F := F) k)^$ x).
  symmetry.
  exact (gpd_V_hh
    (A := F b)
    (a := fmap F (Id b $o k) x)
    (b := fmap F k x)
    (c := fmap F k x)
    (@Id (F b) _ _ (fmap F k x))
    (fmap2 F (cat_idl k) x)).
Defined.

Definition opyoneda_comp_1gpd
  {A : Type} `{Is21Cat A} (F : Fun22 A OneGpd)
  (a : A) (x : F a)
  {b c d : A} (f : b $-> c) (g : c $-> d)
  : isnat (opyoneda_nattrans_1gpd F a x) (g $o f)
    $== (opyoneda_nattrans_1gpd F a x d $@L
          fmap_comp (opyon2_1gpd a) f g)
      $@ cat_assoc_opp
          (fmap (opyon2_1gpd a) f)
          (fmap (opyon2_1gpd a) g)
          (opyoneda_nattrans_1gpd F a x d)
      $@ (isnat (opyoneda_nattrans_1gpd F a x) g $@R
          fmap (opyon2_1gpd a) f)
      $@ cat_assoc
          (fmap (opyon2_1gpd a) f)
          (opyoneda_nattrans_1gpd F a x c)
          (fmap F g)
      $@ (fmap F g $@L
          isnat (opyoneda_nattrans_1gpd F a x) f)
      $@ cat_assoc_opp
          (opyoneda_nattrans_1gpd F a x b)
          (fmap F f) (fmap F g)
      $@ ((fmap_comp F f g)^$ $@R
          opyoneda_nattrans_1gpd F a x b).
Proof.
  intro k.
  change (GpdHom
    (A := @Hom (F d) _
      (fmap F ((g $o f) $o k) x)
      (fmap F (g $o f) (fmap F k x)))
    (fmap_comp F k (g $o f) x)
    (@gpd_comp (F d) _ _ _
      (fmap F ((g $o f) $o k) x)
      (fmap F g (fmap F f (fmap F k x)))
      (fmap F (g $o f) (fmap F k x))
      (@gpd_comp (F d) _ _ _
        (fmap F ((g $o f) $o k) x)
        (fmap F g (fmap F f (fmap F k x)))
        (fmap F g (fmap F f (fmap F k x)))
        (@gpd_comp (F d) _ _ _
          (fmap F ((g $o f) $o k) x)
          (fmap F g (fmap F (f $o k) x))
          (fmap F g (fmap F f (fmap F k x)) )
          (@gpd_comp (F d) _ _ _
            (fmap F ((g $o f) $o k) x)
            (fmap F g (fmap F (f $o k) x))
            (fmap F g (fmap F (f $o k) x))
            (@gpd_comp (F d) _ _ _
              (fmap F ((g $o f) $o k) x)
              (fmap F (g $o (f $o k)) x)
              (fmap F g (fmap F (f $o k) x))
              (@gpd_comp (F d) _ _ _
                (fmap F ((g $o f) $o k) x)
                (fmap F (g $o (f $o k)) x)
                (fmap F (g $o (f $o k)) x)
                (fmap2 F (cat_assoc k f g) x)
                (@gpd_rev (F d) _ _ _ _ _
                  (@Id (F d) _ _
                    (fmap F (g $o (f $o k)) x))))
              (fmap_comp F (f $o k) g x))
            (@Id (F d) _ _
              (fmap F g (fmap F (f $o k) x))))
          (@fmap (F c) (F d) _ _ (fmap F g) _
            (fmap F (f $o k) x)
            (fmap F f (fmap F k x))
            (fmap_comp F k f x)))
        (@gpd_rev (F d) _ _ _ _ _
          (@Id (F d) _ _
            (fmap F g (fmap F f (fmap F k x))))))
      (@gpd_rev (F d) _ _ _ _ _
        (fmap_comp F f g (fmap F k x))))).
  apply gpd_moveL_Vh.
  lhs' exact (cat_idl _)^$.
  lhs' exact ((fmap_assoc (F := F) k f g)^$ x).
  rhs' exact (gpd_comp
    (A := @Hom (F d) _
      (fmap F ((g $o f) $o k) x)
      (fmap F g (fmap F f (fmap F k x))))
    (cat_prewhisker (A := F d) (gpd_rev_1
      (A := F d)
      (a := fmap F g (fmap F f (fmap F k x)))) _)
    (cat_idl _)).
  rhs' exact (cat_postwhisker (A := F d) _ (cat_idl _)).
  rhs' exact (cat_postwhisker (A := F d) _
    (cat_postwhisker (A := F d) _
      (gpd_comp
        (A := @Hom (F d) _
          (fmap F ((g $o f) $o k) x)
          (fmap F (g $o (f $o k)) x))
        (cat_prewhisker (A := F d) (gpd_rev_1
          (A := F d)
          (a := fmap F (g $o (f $o k)) x)) _)
        (cat_idl _)))).
  rapply Id.
Defined.

Definition opyoneda_pseudonat_1gpd
  {A : Type} `{Is21Cat A} (F : Fun22 A OneGpd)
  (a : A) (x : F a)
  : PseudoNatTrans (opyon2_1gpd a) F.
Proof.
  snapply Build_PseudoNatTrans.
  - exact (opyoneda_nattrans_1gpd F a x).
  - intros b c f g p.
    exact (opyoneda_2cell_1gpd F a x p).
  - intro b.
    exact (opyoneda_id_1gpd F a x b).
  - intros b c d f g.
    exact (opyoneda_comp_1gpd F a x f g).
Defined.

Definition opyoneda_1gpd
  {A : Type} `{Is21Cat A} (F : Fun22 A OneGpd) (a : A)
  : F a -> pseudonat_1gpd (opyon2_1gpd a) F
  := opyoneda_pseudonat_1gpd F a.

Definition opyoneda_modification_component_1gpd
  {A : Type} `{Is21Cat A} (F : Fun22 A OneGpd) (a : A)
  {x y : F a} (p : x $== y) (b : A)
  : opyoneda_1gpd F a x b $== opyoneda_1gpd F a y b.
Proof.
  snapply Build_NatTrans.
  - exact (fun f => @fmap (F a) (F b) _ _
      (fmap F f) _ x y p).
  - snapply Build_Is1Natural.
    intros f g q.
    exact (isnat_tr (A := F a) (B := F b)
      (F := fun11_fun (F a) (F b) (fmap F f))
      (G := fun11_fun (F a) (F b) (fmap F g))
      (trans_nattrans
        (A := F a) (B := F b)
        (F := fun11_fun (F a) (F b) (fmap F f))
        (G := fun11_fun (F a) (F b) (fmap F g))
        (fmap2 F q : NatTrans
          (A := F a) (B := F b)
          (fun11_fun (F a) (F b) (fmap F f))
          (fun11_fun (F a) (F b) (fmap F g)))) p).
Defined.

Definition opyoneda_modification_1gpd
  {A : Type} `{Is21Cat A} (F : Fun22 A OneGpd) (a : A)
  {x y : F a} (p : x $== y)
  : opyoneda_1gpd F a x $== opyoneda_1gpd F a y.
Proof.
  snapply Build_Modification.
  - exact (opyoneda_modification_component_1gpd F a p).
  - intros b c h.
    unfold Cylinder.
    intro k.
    exact (isnat_tr (A := F a) (B := F c)
      (F := fun11_fun (F a) (F c) (fmap F (h $o k)))
      (G := fun11_fun (F a) (F c) (fmap F h $o fmap F k))
      (trans_nattrans
        (A := F a) (B := F c)
        (F := fun11_fun (F a) (F c) (fmap F (h $o k)))
        (G := fun11_fun (F a) (F c) (fmap F h $o fmap F k))
        (fmap_comp F k h : NatTrans
          (A := F a) (B := F c)
          (fun11_fun (F a) (F c) (fmap F (h $o k)))
          (fun11_fun (F a) (F c) (fmap F h $o fmap F k)))) p).
Defined.

Instance is0functor_opyoneda_1gpd
  {A : Type} `{Is21Cat A} (F : Fun22 A OneGpd) (a : A)
  : Is0Functor (opyoneda_1gpd F a).
Proof.
  snapply Build_Is0Functor.
  intros x y p.
  exact (opyoneda_modification_1gpd F a p).
Defined.

Instance is1functor_opyoneda_1gpd
  {A : Type} `{Is21Cat A} (F : Fun22 A OneGpd) (a : A)
  : Is1Functor (opyoneda_1gpd F a).
Proof.
  snapply Build_Is1Functor.
  - intros x y p q r b k.
    exact (fmap2 (A := F a) (B := F b)
      (fun11_fun (F a) (F b) (fmap F k)) r).
  - intros x b k.
    exact (fmap_id (A := F a) (B := F b)
      (fun11_fun (F a) (F b) (fmap F k)) x).
  - intros x y z p q b k.
    exact (fmap_comp (A := F a) (B := F b)
      (fun11_fun (F a) (F b) (fmap F k)) p q).
Defined.

Definition opyoneda1_1gpd
  {A : Type} `{Is21Cat A} (F : Fun22 A OneGpd) (a : A)
  : F a $-> pseudonat_1gpd (opyon2_1gpd a) F
  := Build_Fun11 _ _ (opyoneda_1gpd F a).

Definition opyoneda_issect_1gpd
  {A : Type} `{Is21Cat A} (F : Fun22 A OneGpd) (a : A)
  : un_opyoneda1_1gpd F a $o opyoneda1_1gpd F a
    $== Id (F a).
Proof.
  exact (fmap_id F a).
Defined.

Definition opyoneda_isretr_component_1gpd
  {A : Type} `{Is21Cat A} (F : Fun22 A OneGpd) (a : A)
  (alpha : PseudoNatTrans (opyon2_1gpd a) F) (b : A)
  : opyoneda_1gpd F a (un_opyoneda_1gpd F a alpha) b
    $== alpha b.
Proof.
  snapply Build_NatTrans.
  - intro k.
    exact (gpd_comp (A := F b)
      (gpd_rev (A := F b) (isnat alpha k (Id a)))
      (@fmap (opyon_1gpd a b) (F b) _ _ (alpha b) _
        (k $o Id a) k (cat_idr k))).
  - snapply Build_Is1Natural.
    intros k l p.
    exact ((vinverse_square_gpd (pseudonat_2cell alpha p)) (Id a)
      $@v fmap_square
        (fun11_fun (opyon_1gpd a b) (F b) (alpha b))
        (cat_idr_natural p)).
Defined.

Definition opyoneda_isretr_modification_1gpd
  {A : Type} `{Is21Cat A} (F : Fun22 A OneGpd) (a : A)
  (alpha : PseudoNatTrans (opyon2_1gpd a) F)
  : opyoneda_1gpd F a (un_opyoneda_1gpd F a alpha) $== alpha.
Proof.
  snapply Build_Modification.
  - exact (opyoneda_isretr_component_1gpd F a alpha).
  - intros b c h.
    (* A modification cylinder is pointwise in the represented arrow [k]. *)
    unfold Cylinder.
    intro k.
    unfold opyoneda_isretr_component_1gpd.
    unfold opyoneda_1gpd, opyoneda_pseudonat_1gpd.
    unfold opyoneda_nattrans_1gpd, opyoneda_naturality_1gpd.
    unfold un_opyoneda_1gpd.
    change (GpdHom
      (A := @Hom (F c) _
        (fmap F (h $o k) (alpha a (Id a)))
        (fmap F h (alpha b k)))
      (gpd_comp (A := F c)
        (fmap_comp F k h (alpha a (Id a)))
        (fmap (A := F b) (B := F c)
          (fun11_fun (F b) (F c) (fmap F h))
          (gpd_comp (A := F b)
            (gpd_rev (A := F b) (isnat alpha k (Id a)))
            (fmap (A := opyon_1gpd a b) (B := F b)
              (fun11_fun (opyon_1gpd a b) (F b) (alpha b))
              (cat_idr k)))))
      (gpd_comp (A := F c)
        (gpd_comp (A := F c)
          (gpd_rev (A := F c) (isnat alpha (h $o k) (Id a)))
          (fmap (A := opyon_1gpd a c) (B := F c)
            (fun11_fun (opyon_1gpd a c) (F c) (alpha c))
            (cat_idr (h $o k))))
        (isnat alpha h k))).
    (* Move the last pseudonaturality cell to the left and expand the compositor law for [alpha]. *)
    rhs' exact (cat_assoc_opp (A := F c)
      (gpd_rev (A := F c) (isnat alpha (h $o k) (Id a)))
      (fmap (A := opyon_1gpd a c) (B := F c)
        (fun11_fun (opyon_1gpd a c) (F c) (alpha c))
        (cat_idr (h $o k)))
      (isnat alpha h k)).
    apply gpd_moveL_hV.
    lhs' exact (cat_postwhisker (A := F c)
      (gpd_comp (A := F c)
        (fmap_comp F k h (alpha a (Id a)))
        (fmap (A := F b) (B := F c)
          (fun11_fun (F b) (F c) (fmap F h))
          (gpd_comp (A := F b)
            (gpd_rev (A := F b) (isnat alpha k (Id a)))
            (fmap (A := opyon_1gpd a b) (B := F b)
              (fun11_fun (opyon_1gpd a b) (F b) (alpha b))
              (cat_idr k)))))
      (pseudonat_comp
        (opyon2_1gpd a) F alpha k h (Id a))).
    unfold trans_comp.
    (* Cancel the two inverse pairs contributed by that compositor law. *)
    lhs' rapply cat_assoc.
    lhs' napply cat_postwhisker.
    2: rapply gpd_h_Vh.
    lhs' rapply gpd_h_Vh.
    apply gpd_moveL_Vh.
    change (GpdHom
      (A := @Hom (F c) _
        (alpha c ((h $o k) $o Id a))
        (fmap F h (alpha b k)))
      (gpd_comp (A := F c)
        (gpd_comp (A := F c)
          (gpd_comp (A := F c)
            (gpd_comp (A := F c)
              (gpd_comp (A := F c)
                (gpd_comp (A := F c)
                  (fmap (A := opyon_1gpd a c) (B := F c)
                    (fun11_fun (opyon_1gpd a c) (F c) (alpha c))
                  (cat_assoc (Id a) k h))
                  (gpd_rev (A := F c)
                    (@Id (F c) _ _
                      (alpha c (h $o (k $o Id a))))))
                (isnat alpha h (k $o Id a)))
              (@Id (F c) _ _
                (fmap F h (alpha b (k $o Id a)))))
            (fmap (A := F b) (B := F c)
              (fun11_fun (F b) (F c) (fmap F h))
              (isnat alpha k (Id a))))
          (gpd_rev (A := F c)
            (@Id (F c) _ _
              (fmap F h (fmap F k (alpha a (Id a)))))))
        (fmap (A := F b) (B := F c)
          (fun11_fun (F b) (F c) (fmap F h))
          (gpd_comp (A := F b)
            (gpd_rev (A := F b) (isnat alpha k (Id a)))
            (fmap (A := opyon_1gpd a b) (B := F b)
              (fun11_fun (opyon_1gpd a b) (F b) (alpha b))
              (cat_idr k)))))
      (gpd_comp (A := F c)
        (fmap (A := opyon_1gpd a c) (B := F c)
          (fun11_fun (opyon_1gpd a c) (F c) (alpha c))
          (cat_idr (h $o k)))
        (isnat alpha h k))).
    lhs' rapply cat_assoc_opp.
    lhs' napply cat_prewhisker.
    { lhs' exact (cat_postwhisker (A := F c)
        (fmap (A := F b) (B := F c)
          (fun11_fun (F b) (F c) (fmap F h))
          (gpd_comp (A := F b)
            (gpd_rev (A := F b) (isnat alpha k (Id a)))
            (fmap (A := opyon_1gpd a b) (B := F b)
              (fun11_fun (opyon_1gpd a b) (F b) (alpha b))
              (cat_idr k))))
        (gpd_rev_1 (A := F c))).
      exact (cat_idr _). }
    lhs' rapply cat_assoc_opp.
    lhs' napply cat_prewhisker.
    { lhs' exact (gpd_rev
        (A := @Hom (F c) _
          (fmap F h (alpha b (k $o Id a)))
          (fmap F h (alpha b k)))
        (fmap_comp (A := F b) (B := F c)
          (fun11_fun (F b) (F c) (fmap F h))
          (isnat alpha k (Id a))
          (gpd_comp (A := F b)
            (gpd_rev (A := F b) (isnat alpha k (Id a)))
            (fmap (A := opyon_1gpd a b) (B := F b)
              (fun11_fun (opyon_1gpd a b) (F b) (alpha b))
              (cat_idr k))))).
      rapply fmap2.
      rapply gpd_hV_h. }
    lhs' rapply cat_assoc_opp.
    lhs' napply cat_prewhisker.
    { exact (cat_idr _). }
    lhs' rapply cat_assoc_opp.
    lhs' napply cat_prewhisker.
    { exact (isnat_tr (A := opyon_1gpd a b) (B := F c)
        (F := fun11_fun (opyon_1gpd a b) (F c)
          (alpha c $o fmap (opyon2_1gpd a) h))
        (G := fun11_fun (opyon_1gpd a b) (F c)
          (fmap F h $o alpha b))
        (trans_nattrans
          (A := opyon_1gpd a b) (B := F c)
          (F := fun11_fun (opyon_1gpd a b) (F c)
            (alpha c $o fmap (opyon2_1gpd a) h))
          (G := fun11_fun (opyon_1gpd a b) (F c)
            (fmap F h $o alpha b))
          (isnat alpha h : NatTrans
            (fun11_fun (opyon_1gpd a b) (F c)
              (alpha c $o fmap (opyon2_1gpd a) h))
            (fun11_fun (opyon_1gpd a b) (F c)
              (fmap F h $o alpha b))))
        (cat_idr k)). }
    lhs' napply cat_postwhisker.
    { lhs' exact (cat_prewhisker (A := F c)
        (gpd_rev_1 (A := F c))
        (fmap (A := opyon_1gpd a c) (B := F c)
          (fun11_fun (opyon_1gpd a c) (F c) (alpha c))
          (cat_assoc (Id a) k h))).
      exact (cat_idl _). }
    lhs' rapply cat_assoc.
    (* The remaining inner face is naturality of [alpha h] at [cat_idr k]. *)
    nrefine (cat_postwhisker (A := F c)
      (is1natural_nattrans alpha b c h k) _).
    lhs' exact (fmap_comp
      (A := opyon_1gpd a c) (B := F c)
      (fun11_fun (opyon_1gpd a c) (F c) (alpha c))
      (cat_assoc (Id a) k h)
      (h $@L cat_idr k))^$.
    rapply fmap2.
    lhs' exact (cat_prewhisker (A := a $-> c)
      (cat_idr_assoc k h) (cat_assoc (Id a) k h)).
    (* Convert [cat_assoc_opp] to the actual inverse and cancel. *)
    lhs' exact (cat_prewhisker (A := a $-> c)
      (cat_postwhisker (A := a $-> c)
        (cat_idr (h $o k))
        (cat_assoc_opp_is_rev a a b c (Id a) k h))
      (cat_assoc (Id a) k h)).
    exact (gpd_hV_h (cat_idr (h $o k))
      (cat_assoc (Id a) k h)).
Defined.

Definition opyoneda_isretr_1gpd
  {A : Type} `{Is21Cat A} (F : Fun22 A OneGpd) (a : A)
  : opyoneda1_1gpd F a $o un_opyoneda1_1gpd F a
    $== Id (pseudonat_1gpd (opyon2_1gpd a) F).
Proof.
  snapply Build_NatTrans.
  - exact (opyoneda_isretr_modification_1gpd F a).
  - snapply Build_Is1Natural.
    intros alpha beta p.
    intro b.
    intro k.
    unfold opyoneda_isretr_modification_1gpd.
    unfold opyoneda_isretr_component_1gpd.
    change (GpdHom
      (A := @Hom (F b) _
        (fmap F k (alpha a (Id a)))
        (beta b k))
      (gpd_comp (A := F b)
        (fmap (A := F a) (B := F b)
          (fun11_fun (F a) (F b) (fmap F k))
          (modification_component p a (Id a)))
        (gpd_comp (A := F b)
          (gpd_rev (A := F b) (isnat beta k (Id a)))
          (fmap (A := opyon_1gpd a b) (B := F b)
            (fun11_fun (opyon_1gpd a b) (F b) (beta b))
            (cat_idr k))))
      (gpd_comp (A := F b)
        (gpd_comp (A := F b)
          (gpd_rev (A := F b) (isnat alpha k (Id a)))
          (fmap (A := opyon_1gpd a b) (B := F b)
            (fun11_fun (opyon_1gpd a b) (F b) (alpha b))
            (cat_idr k)))
        (modification_component p b k))).
    (* Use the modification cylinder at [k], evaluated at the identity of [a], to commute evaluation with [p]. *)
    lhs' rapply cat_assoc.
    lhs' exact (cat_postwhisker (A := F b)
      (fmap (A := opyon_1gpd a b) (B := F b)
        (fun11_fun (opyon_1gpd a b) (F b) (beta b))
        (cat_idr k))
      (gpd_rev
        (A := @Hom (F b) _
          (fmap F k (alpha a (Id a)))
          (beta b (k $o Id a)))
        ((hinverse_square_gpd (modification_isnatural p k)) (Id a)))).
    unfold trans_comp.
    unfold trans_prewhisker, nattrans_inverse_gpd.
    lhs' rapply cat_assoc_opp.
    rhs' rapply cat_assoc_opp.
    (* The last face is ordinary naturality of the component [p b]. *)
    nrefine (cat_prewhisker (A := F b) _
      (gpd_rev (A := F b)
        (is1natural_nattrans alpha a b k (Id a)))).
    exact (isnat_tr (A := opyon_1gpd a b) (B := F b)
      (F := fun11_fun (opyon_1gpd a b) (F b) (alpha b))
      (G := fun11_fun (opyon_1gpd a b) (F b) (beta b))
      (trans_nattrans
        (A := opyon_1gpd a b) (B := F b)
        (F := fun11_fun (opyon_1gpd a b) (F b) (alpha b))
        (G := fun11_fun (opyon_1gpd a b) (F b) (beta b))
        (modification_component p b : NatTrans
          (fun11_fun (opyon_1gpd a b) (F b) (alpha b))
          (fun11_fun (opyon_1gpd a b) (F b) (beta b))))
      (cat_idr k)).
Defined.

Instance catie_opyoneda1_1gpd
  {A : Type} `{Is21Cat A} (F : Fun22 A OneGpd) (a : A)
  : CatIsEquiv (opyoneda1_1gpd F a)
  := catie_adjointify
    (opyoneda1_1gpd F a)
    (un_opyoneda1_1gpd F a)
    (opyoneda_isretr_1gpd F a)
    (opyoneda_issect_1gpd F a).

Definition opyoneda_equiv_1gpd
  {A : Type} `{Is21Cat A} (F : Fun22 A OneGpd) (a : A)
  : F a $<~> pseudonat_1gpd (opyon2_1gpd a) F
  := Build_CatEquiv (opyoneda1_1gpd F a).
