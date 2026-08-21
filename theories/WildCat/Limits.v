Require Import Basics.Overture Basics.PathGroupoids Basics.Tactics.
Require Import WildCat.Core WildCat.Cylinder WildCat.Equiv
  WildCat.FunctorCat WildCat.NatTrans WildCat.OneGroupoid WildCat.Square
  WildCat.TwoFunctor WildCat.TwoOneCat WildCat.TwoYoneda.

Set Typeclasses Depth 3.

(** * Limits in wild categories *)

(** A limit is a specified universal cone over a coherent graph-shaped
    diagram.  Choice and functoriality are derived separately from this local
    universal property. *)

(** ** The coherent diagonal *)

Section Diagonal02.
  Context (A J : Type) `{Is21Cat A, IsGraph J}.

  Definition diagonal02 : A -> Fun02 J A
    := fun x => Build_Fun02 (fun _ => x).

  Global Instance is0functor_diagonal02
    : Is0Functor diagonal02.
  Proof.
    snapply Build_Is0Functor.
    intros a b f.
    snapply Build_NatTrans.
    { exact (fun _ => f). }
    snapply Build_Is1Natural.
    intros i j g.
    exact (hrefl f).
  Defined.

  Definition natmod_diagonal02
    {a b : A} {f g : a $-> b} (p : f $== g)
    : fmap diagonal02 f $== fmap diagonal02 g.
  Proof.
    snapply Build_NatModification.
    { exact (fun _ => p). }
    intros i j h.
    exact (cylinder_hrefl p).
  Defined.

  Definition natmod_diagonal02_id
    (a : A)
    : NatModification
        (F := diagonal02 a)
        (G := diagonal02 a)
        (fmap diagonal02 (Id a))
        (nattrans_id (diagonal02 a)).
  Proof.
    snapply Build_NatModification.
    { exact (fun _ => Id _). }
    intros i j f.
    cbn.
    unfold Cylinder.
    rapply (hconcatL
      (fmap_id (cat_precomp a (Id a)) (Id a)) _).
    rapply (hconcatR _
      (fmap_id (cat_postcomp a (Id a)) (Id a))).
    unfold hrefl, vrefl.
    napply Build_Square.
    lhs' rapply cat_idl.
    rhs' rapply cat_idr.
    exact (((cat_idl (Id a))^$ $@L (cat_idl_idr_id a)^$)
      $@ (gpd_rev2 (cat_idl_idr_id a) $@R cat_idl (Id a))).
  Defined.

  Local Definition hrefl_vconcat_head
    {a b c : A} (f : a $-> b) (g : b $-> c)
    : cat_assoc (Id a) f g $@
        (g $@L cat_idr f)
      $== cat_idr (g $o f)
    := cat_assoc_idr f g.

  Local Definition hrefl_vconcat_tail
    {a b c : A} (f : a $-> b) (g : b $-> c)
    : (cat_idl g $@R f)^$ $@
        cat_assoc f g (Id c)
      $== (cat_idl (g $o f))^$.
  Proof.
    lhs' exact (cat_assoc f g (Id c) $@L
      gpd_rev2 (cat_idl_assoc f g)).
    lhs' exact (cat_assoc f g (Id c) $@L
      gpd_rev_pp (cat_idl (g $o f))
        (cat_assoc f g (Id c))).
    lhs' exact (cat_assoc
      (cat_idl (g $o f))^$
      (cat_assoc f g (Id c))^$
      (cat_assoc f g (Id c)))^$.
    lhs' exact (gpd_isretr (cat_assoc f g (Id c))
      $@R (cat_idl (g $o f))^$).
    exact (cat_idl (cat_idl (g $o f))^$).
  Defined.

  Local Definition hrefl_vconcat_triangle
    {a b c : A} (f : a $-> b) (g : b $-> c)
    : cat_assoc_opp f (Id b) g $@
        (cat_idr g $@R f)
      $== g $@L cat_idl f.
  Proof.
    lhs' exact ((cat_idr g $@R f) $@L
      cat_assoc_opp_is_rev a b b c f (Id b) g).
    exact (gpd_moveL_hV
      (cat_tril (A := A) a b c f g))^$.
  Defined.

  Local Definition hrefl_vconcat_middle
    {a b c : A} (f : a $-> b) (g : b $-> c)
    : (g $@L cat_idl f)^$ $@
        (cat_assoc_opp f (Id b) g $@
          (cat_idr g $@R f))
      $== Id _.
  Proof.
    lhs' exact (hrefl_vconcat_triangle f g
      $@R (g $@L cat_idl f)^$).
    exact (gpd_isretr (g $@L cat_idl f)).
  Defined.

  Local Definition hrefl_vconcat_expanded
    {a b c : A} (f : a $-> b) (g : b $-> c)
    : (cat_assoc (Id a) f g $@
        ((g $@L cat_idr f) $@
          (g $@L cat_idl f)^$)) $@
      ((cat_assoc_opp f (Id b) g $@
        ((cat_idr g $@R f) $@
          (cat_idl g $@R f)^$)) $@
        cat_assoc f g (Id c))
      $== cat_idr (g $o f) $@
        (cat_idl (g $o f))^$.
  Proof.
    pose (aa := cat_assoc (Id a) f g).
    pose (rf := g $@L cat_idr f).
    pose (lf := (g $@L cat_idl f)^$).
    pose (am := cat_assoc_opp f (Id b) g).
    pose (rg := cat_idr g $@R f).
    pose (lg := (cat_idl g $@R f)^$).
    pose (al := cat_assoc f g (Id c)).
    pose (rr := cat_idr (g $o f)).
    pose (ll := (cat_idl (g $o f))^$).
    change ((aa $@ (rf $@ lf)) $@
      ((am $@ (rg $@ lg)) $@ al) $== rr $@ ll).
    lhs' exact (((am $@ (rg $@ lg)) $@ al) $@L
      cat_assoc aa rf lf).
    lhs' exact (cat_assoc (aa $@ rf) lf
      ((am $@ (rg $@ lg)) $@ al))^$.
    lhs' exact (cat_assoc lf (am $@ (rg $@ lg)) al
      $@R (aa $@ rf)).
    lhs' exact ((al $@L
      (cat_assoc am rg lg $@R lf))
      $@R (aa $@ rf)).
    lhs' exact ((al $@L
      cat_assoc lf (am $@ rg) lg)
      $@R (aa $@ rf)).
    lhs' exact ((cat_assoc (lf $@ (am $@ rg)) lg al)^$
      $@R (aa $@ rf)).
    lhs' exact (((lf $@ (am $@ rg)) $@ (lg $@ al)) $@L
      hrefl_vconcat_head f g).
    lhs' exact (((lg $@ al) $@L
      hrefl_vconcat_middle f g) $@R rr).
    lhs' exact (cat_idr (lg $@ al) $@R rr).
    exact (hrefl_vconcat_tail f g $@R rr).
  Defined.

  Local Definition postwhisker_hrefl_components
    {a b c : A} (f : a $-> b) (g : b $-> c)
    : g $@L (cat_idr f $@ (cat_idl f)^$)
      $== (g $@L cat_idr f) $@
        (g $@L cat_idl f)^$.
  Proof.
    lhs' exact (cat_postwhisker_pp g
      (cat_idr f) (cat_idl f)^$).
    exact (gpd_1functor_V (cat_postcomp a g) (cat_idl f)
      $@R (g $@L cat_idr f)).
  Defined.

  Local Definition prewhisker_hrefl_components
    {a b c : A} (f : a $-> b) (g : b $-> c)
    : (cat_idr g $@ (cat_idl g)^$) $@R f
      $== (cat_idr g $@R f) $@
        (cat_idl g $@R f)^$.
  Proof.
    lhs' exact (cat_prewhisker_pp f
      (cat_idr g) (cat_idl g)^$).
    exact (gpd_1functor_V (cat_precomp c f) (cat_idl g)
      $@R (cat_idr g $@R f)).
  Defined.

  Definition natmod_diagonal02_comp
    {a b c : A} (f : a $-> b) (g : b $-> c)
    : NatModification
        (F := diagonal02 a)
        (G := diagonal02 c)
        (fmap diagonal02 (g $o f))
        (nattrans_comp (fmap diagonal02 g) (fmap diagonal02 f)).
  Proof.
    snapply Build_NatModification.
    { exact (fun _ => Id _). }
    intros i j h.
    cbn.
    unfold Cylinder.
    rapply (hconcatL
      (fmap_id (cat_precomp c (Id a)) (g $o f)) _).
    rapply (hconcatR _
      (fmap_id (cat_postcomp a (Id c)) (g $o f))).
    napply Build_Square.
    lhs' rapply cat_idl.
    rhs' rapply cat_idr.
    unfold hrefl, vconcat.
    symmetry.
    lhs' exact
      (((cat_assoc_opp f (Id b) g $@
          ((cat_idr g $@ (cat_idl g)^$) $@R f)) $@
        cat_assoc f g (Id c)) $@L
      (postwhisker_hrefl_components f g $@R
        cat_assoc (Id a) f g)).
    lhs' exact
      ((cat_assoc f g (Id c) $@L
        (prewhisker_hrefl_components f g $@R
          cat_assoc_opp f (Id b) g)) $@R
      (cat_assoc (Id a) f g $@
        ((g $@L cat_idr f) $@
          (g $@L cat_idl f)^$))).
    exact (hrefl_vconcat_expanded f g).
  Defined.

  Definition is1functor_diagonal02_generic
    : Is1Functor diagonal02.
  Proof.
    snapply Build_Is1Functor.
    - intros a b f g p.
      exact (natmod_diagonal02 p).
    - exact natmod_diagonal02_id.
    - intros a b c f g.
      exact (natmod_diagonal02_comp f g).
  Defined.

  Local Existing Instance is1functor_diagonal02_generic.

  Definition is1functor_fmap_diagonal02_generic
    (a b : A)
    : Is1Functor (@fmap A (Fun02 J A) _ _
        diagonal02 _ a b).
  Proof.
    snapply Build_Is1Functor.
    - intros f g p q h j.
      exact h.
    - intros f j.
      exact (Id _).
    - intros f g h p q j.
      exact (Id _).
  Defined.

  Definition is2functor_diagonal02_generic
    : Is2Functor diagonal02.
  Proof.
    snapply Build_Is2Functor.
    - exact is1functor_fmap_diagonal02_generic.
    - intros a b c f f' g g' p q j.
      cbn.
      unfold "$@@".
      lhs' rapply cat_idl.
      rhs' rapply cat_idr.
      exact (Id _).
    - intros a b c d f g h j.
      cbn.
      lhs' exact ((h $@L Id (g $o f)) $@L
        cat_idl (cat_assoc f g h)).
      lhs' exact (fmap_id (cat_postcomp a h) (g $o f)
        $@R cat_assoc f g h).
      lhs' exact (cat_idl (cat_assoc f g h)).
      rhs' exact (cat_assoc f g h $@L
        (fmap_id (cat_precomp d f) (h $o g)
          $@R Id (h $o g $o f))).
      rhs' exact (cat_assoc f g h $@L
        cat_idl (Id ((h $o g) $o f))).
      rhs' exact (cat_idr (cat_assoc f g h)).
      exact (Id _).
    - intros a b f j.
      cbn.
      rhs' exact (cat_idl f $@L
        (fmap_id (cat_precomp b f) (Id b)
          $@R Id (Id b $o f))).
      rhs' exact (cat_idl f $@L
        cat_idl (Id (Id b $o f))).
      rhs' exact (cat_idr (cat_idl f)).
      exact (Id _).
    - intros a b f j.
      cbn.
      rhs' exact (cat_idr f $@L
        (fmap_id (cat_postcomp a f) (Id a)
          $@R Id (f $o Id a))).
      rhs' exact (cat_idr f $@L
        cat_idl (Id (f $o Id a))).
      rhs' exact (cat_idr (cat_idr f)).
      exact (Id _).
  Defined.

  Definition fun02_diagonal : Fun02 A (Fun02 J A)
    := Build_Fun02 diagonal02.

  Global Instance is1functor_diagonal02
    : Is1Functor diagonal02
    := is1functor_diagonal02_generic.

  Global Instance is2functor_diagonal02
    : Is2Functor diagonal02
    := is2functor_diagonal02_generic.

  Definition fun22_diagonal02
    : Fun22 A (Fun02 J A)
    := Build_Fun22 diagonal02.
End Diagonal02.

(** ** Cone mapping 1-groupoids *)

Definition cone_1gpd
  {A J : Type} `{Is21Cat A, IsGraph J}
  (X : Fun02 J A) (a : A) : OneGpd
  := hom_1gpd (diagonal02 A J a) X.

(** Composition with a specified cone. *)
Definition limit_cone_map
  {A J : Type} `{Is21Cat A, IsGraph J}
  (X : Fun02 J A) (l : A)
  (lambda : diagonal02 A J l $-> X) (a : A)
  : Fun11 (hom_1gpd a l) (cone_1gpd X a).
Proof.
  napply fun11_compose.
  - exact (Build_Fun11 _ _
      (cat_postcomp (diagonal02 A J a) lambda)).
  - napply (Build_Fun11 _ _
      (@fmap A (Fun02 J A) _ _ (diagonal02 A J)
        (is0functor_diagonal02 A J) a l)).
    exact (is1functor_fmap_diagonal02_generic A J a l).
Defined.

Definition IsLimitCone
  {A J : Type} `{Is21Cat A, IsGraph J}
  (X : Fun02 J A) (l : A)
  (lambda : diagonal02 A J l $-> X) : Type
  := forall a : A, CatIsEquiv (limit_cone_map X l lambda a).

Class Limit
  (J : Type) {A : Type} `{IsGraph J, Is21Cat A}
  (X : Fun02 J A) := Build_Limit {
  cat_limit : A;
  cat_limit_cone : diagonal02 A J cat_limit $-> X;
  cat_islimit_cone : IsLimitCone X cat_limit cat_limit_cone;
}.

Arguments cat_limit J {A _ _ _ _ _ _ _} X {limit} : rename.
Arguments cat_limit_cone J {A _ _ _ _ _ _ _} X {limit} : rename.
Arguments cat_islimit_cone J {A _ _ _ _ _ _ _} X {limit} : rename.

(** ** Local universal-cone API *)

Definition cate_limit_cone_map
  {A J : Type} `{Is21Cat A, IsGraph J}
  (X : Fun02 J A) `{!Limit J X} (a : A)
  : hom_1gpd a (cat_limit J X) $<~> cone_1gpd X a.
Proof.
  napply Build_CatEquiv.
  exact (cat_islimit_cone J X a).
Defined.

Definition limit_corec
  {A J : Type} `{Is21Cat A, IsGraph J}
  (X : Fun02 J A) `{!Limit J X}
  {a : A} (alpha : diagonal02 A J a $-> X)
  : a $-> cat_limit J X.
Proof.
  exact (cate_fun (cate_limit_cone_map X a)^-1$ alpha).
Defined.

Definition limit_beta
  {A J : Type} `{Is21Cat A, IsGraph J}
  (X : Fun02 J A) `{!Limit J X}
  {a : A} (alpha : diagonal02 A J a $-> X)
  : limit_cone_map X (cat_limit J X) (cat_limit_cone J X) a
      (limit_corec X alpha) $== alpha.
Proof.
  exact (cate_isretr (cate_limit_cone_map X a) alpha).
Defined.

Definition limit_eta
  {A J : Type} `{Is21Cat A, IsGraph J}
  (X : Fun02 J A) `{!Limit J X}
  {a : A} (k : a $-> cat_limit J X)
  : limit_corec X
      (limit_cone_map X (cat_limit J X) (cat_limit_cone J X) a k)
    $== k.
Proof.
  exact (cate_issect (cate_limit_cone_map X a) k).
Defined.

Definition limit_corec_modification
  {A J : Type} `{Is21Cat A, IsGraph J}
  (X : Fun02 J A) `{!Limit J X}
  {a : A} {alpha beta : diagonal02 A J a $-> X}
  (p : alpha $== beta)
  : limit_corec X alpha $== limit_corec X beta.
Proof.
  exact (fmap (cate_fun (cate_limit_cone_map X a)^-1$) p).
Defined.

Definition limit_corec_3cell
  {A J : Type} `{Is21Cat A, IsGraph J}
  (X : Fun02 J A) `{!Limit J X}
  {a : A} {alpha beta : diagonal02 A J a $-> X}
  {p q : alpha $== beta} (h : p $== q)
  : limit_corec_modification X p $== limit_corec_modification X q.
Proof.
  exact (fmap2 (cate_fun (cate_limit_cone_map X a)^-1$) h).
Defined.

Definition limit_corec_unique
  {A J : Type} `{Is21Cat A, IsGraph J}
  (X : Fun02 J A) `{!Limit J X}
  {a : A} (alpha : diagonal02 A J a $-> X)
  (k : a $-> cat_limit J X)
  (p : limit_cone_map X (cat_limit J X) (cat_limit_cone J X) a k
       $== alpha)
  : k $== limit_corec X alpha.
Proof.
  exact ((limit_eta X k)^$
    $@ fmap (cate_fun (cate_limit_cone_map X a)^-1$) p).
Defined.
