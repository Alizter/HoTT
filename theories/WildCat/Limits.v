Require Import Basics.Overture Basics.PathGroupoids Basics.Tactics.
Require Import WildCat.Adjoint WildCat.Core WildCat.Cylinder WildCat.Equiv
  WildCat.FunctorCat WildCat.NatTrans WildCat.OneGroupoid WildCat.Opposite
  WildCat.Square WildCat.TwoFunctor WildCat.TwoOneCat WildCat.TwoYoneda.

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

(** In the apex variable, cones form the composite contravariant functor
    [A^op -> (Fun02 J A)^op -> OneGpd] given by the opposite diagonal followed
    by the representable hom functor. *)
Definition fun12_diagonal02_op
  {A J : Type} `{Is21Cat A, IsGraph J}
  : Fun12 A^op (Fun02 J A)^op
  := Build_Fun12 (diagonal02 A J : A^op -> (Fun02 J A)^op).

Definition fun12_cone_1gpd
  {A J : Type} `{Is21Cat A, IsGraph J} (X : Fun02 J A)
  : Fun12 A^op OneGpd
  := fun12_compose (yon1_1gpd X) fun12_diagonal02_op.

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

Definition limit_cone_map_homotopic
  {A J : Type} `{Is21Cat A, IsGraph J}
  {X : Fun02 J A} {l : A}
  {alpha beta : diagonal02 A J l $-> X}
  (h : alpha $== beta) (a : A)
  : limit_cone_map X l alpha a
    $== limit_cone_map X l beta a.
Proof.
  snapply Build_NatTrans.
  - intro k.
    change (a $-> l) in k.
    exact (natmod_precompose (fmap (diagonal02 A J) k) h).
  - snapply Build_Is1Natural.
    intros k k' p.
    exact (bifunctor_coh_comp
      (fmap2 (diagonal02 A J) p) h)^$.
Defined.

Definition islimitcone_homotopic
  {A J : Type} `{Is21Cat A, IsGraph J}
  {X : Fun02 J A} {l : A}
  {alpha beta : diagonal02 A J l $-> X}
  (h : alpha $== beta) (Halpha : IsLimitCone X l alpha)
  : IsLimitCone X l beta.
Proof.
  intro a.
  pose (e := Build_CatEquiv (fe := Halpha a)
    (limit_cone_map X l alpha a)).
  napply (catie_homotopic (cate_fun e)).
  - exact _.
  - exact (limit_cone_map_homotopic h a).
Defined.

Local Definition limit_cone_map_cate_of_islimitcone
  {A J : Type} `{Is21Cat A, IsGraph J}
  {X : Fun02 J A} {l : A}
  (lambda : diagonal02 A J l $-> X)
  (Hlambda : IsLimitCone X l lambda) (a : A)
  : hom_1gpd a l $<~> cone_1gpd X a
  := Build_CatEquiv (fe := Hlambda a)
      (limit_cone_map X l lambda a).

(** The inverse mapping functor associated to an explicitly universal cone. *)
Definition limit_cone_map_inv_of_islimitcone
  {A J : Type} `{Is21Cat A, IsGraph J}
  {X : Fun02 J A} {l : A}
  (lambda : diagonal02 A J l $-> X)
  (Hlambda : IsLimitCone X l lambda) (a : A)
  : Fun11 (cone_1gpd X a) (hom_1gpd a l)
  := cate_fun (cate_inv
      (limit_cone_map_cate_of_islimitcone lambda Hlambda a)).

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

(** A coherent choice of a universal cone for every diagram of shape [J]. *)
Class HasLimits
  (J A : Type) `{IsGraph J, Is21Cat A}
  := has_limits :: forall X : Fun02 J A, Limit J X.

(** ** Local universal-cone API *)

Definition limit_cone_map_inv
  {A J : Type} `{Is21Cat A, IsGraph J}
  (X : Fun02 J A) `{!Limit J X} (a : A)
  : Fun11 (cone_1gpd X a) (hom_1gpd a (cat_limit J X))
  := limit_cone_map_inv_of_islimitcone
      (cat_limit_cone J X) (cat_islimit_cone J X) a.

Definition limit_corec
  {A J : Type} `{Is21Cat A, IsGraph J}
  (X : Fun02 J A) `{!Limit J X}
  {a : A} (alpha : diagonal02 A J a $-> X)
  : a $-> cat_limit J X.
Proof.
  exact (limit_cone_map_inv X a alpha).
Defined.

Definition limit_beta
  {A J : Type} `{Is21Cat A, IsGraph J}
  (X : Fun02 J A) `{!Limit J X}
  {a : A} (alpha : diagonal02 A J a $-> X)
  : limit_cone_map X (cat_limit J X) (cat_limit_cone J X) a
      (limit_corec X alpha) $== alpha.
Proof.
  exact (cate_isretr
    (limit_cone_map_cate_of_islimitcone
      (cat_limit_cone J X) (cat_islimit_cone J X) a) alpha).
Defined.

Definition limit_eta
  {A J : Type} `{Is21Cat A, IsGraph J}
  (X : Fun02 J A) `{!Limit J X}
  {a : A} (k : a $-> cat_limit J X)
  : limit_corec X
      (limit_cone_map X (cat_limit J X) (cat_limit_cone J X) a k)
    $== k.
Proof.
  exact (cate_issect
    (limit_cone_map_cate_of_islimitcone
      (cat_limit_cone J X) (cat_islimit_cone J X) a) k).
Defined.

Definition limit_corec_modification
  {A J : Type} `{Is21Cat A, IsGraph J}
  (X : Fun02 J A) `{!Limit J X}
  {a : A} {alpha beta : diagonal02 A J a $-> X}
  (p : alpha $== beta)
  : limit_corec X alpha $== limit_corec X beta.
Proof.
  exact (fmap (limit_cone_map_inv X a) p).
Defined.

Definition limit_corec_3cell
  {A J : Type} `{Is21Cat A, IsGraph J}
  (X : Fun02 J A) `{!Limit J X}
  {a : A} {alpha beta : diagonal02 A J a $-> X}
  {p q : alpha $== beta} (h : p $== q)
  : limit_corec_modification X p $== limit_corec_modification X q.
Proof.
  exact (fmap2 (limit_cone_map_inv X a) h).
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
    $@ fmap (limit_cone_map_inv X a) p).
Defined.

(** ** Categorical unicity of universal cones *)

(** The canonical map from one universal-cone apex to another. *)
Definition limit_apex_map
  {A J : Type} `{Is21Cat A, IsGraph J}
  {X : Fun02 J A} {l m : A}
  (lambda : diagonal02 A J l $-> X)
  (mu : diagonal02 A J m $-> X)
  (Hmu : IsLimitCone X m mu)
  : l $-> m
  := limit_cone_map_inv_of_islimitcone mu Hmu l lambda.

Definition limit_apex_map_beta
  {A J : Type} `{Is21Cat A, IsGraph J}
  {X : Fun02 J A} {l m : A}
  (lambda : diagonal02 A J l $-> X)
  (mu : diagonal02 A J m $-> X)
  (Hmu : IsLimitCone X m mu)
  : limit_cone_map X m mu l (limit_apex_map lambda mu Hmu)
    $== lambda.
Proof.
  exact (cate_isretr
    (limit_cone_map_cate_of_islimitcone mu Hmu l) lambda).
Defined.

Definition limit_cone_map_id
  {A J : Type} `{Is21Cat A, IsGraph J}
  {X : Fun02 J A} {l : A}
  (lambda : diagonal02 A J l $-> X)
  : limit_cone_map X l lambda l (Id l) $== lambda.
Proof.
  exact ((lambda $@L fmap_id (diagonal02 A J) l)
    $@ cat_idr lambda).
Defined.

(** The mapping equivalence reflects modifications between mediating maps. *)
Definition limit_cone_map_reflects
  {A J : Type} `{Is21Cat A, IsGraph J}
  {X : Fun02 J A} {l a : A}
  (lambda : diagonal02 A J l $-> X)
  (Hlambda : IsLimitCone X l lambda)
  {f g : a $-> l}
  (p : limit_cone_map X l lambda a f
    $== limit_cone_map X l lambda a g)
  : f $== g.
Proof.
  pose (e := limit_cone_map_cate_of_islimitcone lambda Hlambda a).
  exact ((cate_issect e f)^$
    $@ fmap (cate_fun (cate_inv e)) p
    $@ cate_issect e g).
Defined.

Local Definition limit_apex_map_composite_cone
  {A J : Type} `{Is21Cat A, IsGraph J}
  {X : Fun02 J A} {l m : A}
  (lambda : diagonal02 A J l $-> X)
  (mu : diagonal02 A J m $-> X)
  (Hlambda : IsLimitCone X l lambda)
  (Hmu : IsLimitCone X m mu)
  : limit_cone_map X l lambda l
      (limit_apex_map mu lambda Hlambda
        $o limit_apex_map lambda mu Hmu)
    $== lambda.
Proof.
  pose (f := limit_apex_map lambda mu Hmu).
  pose (g := limit_apex_map mu lambda Hlambda).
  change (lambda $o fmap (diagonal02 A J) (g $o f) $== lambda).
  exact ((lambda $@L fmap_comp (diagonal02 A J) f g)
    $@ cat_assoc_opp (fmap (diagonal02 A J) f)
      (fmap (diagonal02 A J) g) lambda
    $@ (limit_apex_map_beta mu lambda Hlambda
      $@R fmap (diagonal02 A J) f)
    $@ limit_apex_map_beta lambda mu Hmu).
Defined.

Definition limit_apex_map_sect
  {A J : Type} `{Is21Cat A, IsGraph J}
  {X : Fun02 J A} {l m : A}
  (lambda : diagonal02 A J l $-> X)
  (mu : diagonal02 A J m $-> X)
  (Hlambda : IsLimitCone X l lambda)
  (Hmu : IsLimitCone X m mu)
  : limit_apex_map mu lambda Hlambda
      $o limit_apex_map lambda mu Hmu
    $== Id l.
Proof.
  napply (limit_cone_map_reflects lambda Hlambda).
  exact (limit_apex_map_composite_cone lambda mu Hlambda Hmu
    $@ (limit_cone_map_id lambda)^$).
Defined.

(** The apexes of two universal cones are canonically equivalent. *)
Definition limit_apex_equiv
  {A J : Type} `{Is21Cat A} `{!HasEquivs A, IsGraph J}
  {X : Fun02 J A} {l m : A}
  (lambda : diagonal02 A J l $-> X)
  (mu : diagonal02 A J m $-> X)
  (Hlambda : IsLimitCone X l lambda)
  (Hmu : IsLimitCone X m mu)
  : l $<~> m.
Proof.
  exact (cate_adjointify
    (limit_apex_map lambda mu Hmu)
    (limit_apex_map mu lambda Hlambda)
    (limit_apex_map_sect mu lambda Hmu Hlambda)
    (limit_apex_map_sect lambda mu Hlambda Hmu)).
Defined.

(** The canonical apex equivalence carries the second cone to the first. *)
Definition limit_apex_equiv_cone
  {A J : Type} `{Is21Cat A} `{!HasEquivs A, IsGraph J}
  {X : Fun02 J A} {l m : A}
  (lambda : diagonal02 A J l $-> X)
  (mu : diagonal02 A J m $-> X)
  (Hlambda : IsLimitCone X l lambda)
  (Hmu : IsLimitCone X m mu)
  : limit_cone_map X m mu l
      (cate_fun (limit_apex_equiv lambda mu Hlambda Hmu))
    $== lambda.
Proof.
  exact (fmap (limit_cone_map X m mu l)
      (cate_buildequiv_fun
        (limit_apex_map lambda mu Hmu))
    $@ limit_apex_map_beta lambda mu Hmu).
Defined.

(** ** Chosen limit functor *)

(** A transformation of diagrams induces the unique map between their chosen
    limit apexes whose composite with the target cone is the transformed source
    cone. *)
Definition cat_limit_map
  {A J : Type} `{Is21Cat A, IsGraph J, !HasLimits J A}
  {X Y : Fun02 J A} (f : X $-> Y)
  : cat_limit J X $-> cat_limit J Y
  := limit_corec Y (f $o cat_limit_cone J X).

Definition cat_limit_map_beta
  {A J : Type} `{Is21Cat A, IsGraph J, !HasLimits J A}
  {X Y : Fun02 J A} (f : X $-> Y)
  : limit_cone_map Y (cat_limit J Y) (cat_limit_cone J Y)
      (cat_limit J X) (cat_limit_map f)
    $== f $o cat_limit_cone J X
  := limit_beta Y (f $o cat_limit_cone J X).

(** The higher-cell action is inherited from the inverse of the cone-mapping
    equivalence, rather than chosen independently. *)
Definition cat_limit_map_modification
  {A J : Type} `{Is21Cat A, IsGraph J, !HasLimits J A}
  {X Y : Fun02 J A} {f g : X $-> Y} (p : f $== g)
  : cat_limit_map f $== cat_limit_map g
  := limit_corec_modification Y (p $@R cat_limit_cone J X).

Definition cat_limit_map_3cell
  {A J : Type} `{Is21Cat A, IsGraph J, !HasLimits J A}
  {X Y : Fun02 J A} {f g : X $-> Y}
  {p q : f $== g} (h : p $== q)
  : cat_limit_map_modification p
    $== cat_limit_map_modification q
  := limit_corec_3cell Y
      (fmap2 (cat_precomp Y (cat_limit_cone J X)) h).

(** Identity and composition coherence are forced by uniqueness of maps into
    the chosen universal cones. *)
Definition cat_limit_map_id
  {A J : Type} `{Is21Cat A, IsGraph J, !HasLimits J A}
  (X : Fun02 J A)
  : cat_limit_map (Id X) $== Id (cat_limit J X).
Proof.
  exact ((limit_corec_unique X
    (Id X $o cat_limit_cone J X)
    (Id (cat_limit J X))
    (limit_cone_map_id (cat_limit_cone J X)
      $@ (cat_idl (cat_limit_cone J X))^$))^$).
Defined.

Definition cat_limit_map_comp
  {A J : Type} `{Is21Cat A, IsGraph J, !HasLimits J A}
  {X Y Z : Fun02 J A} (f : X $-> Y) (g : Y $-> Z)
  : cat_limit_map (g $o f)
    $== cat_limit_map g $o cat_limit_map f.
Proof.
  pose (lf := cat_limit_map f).
  pose (lg := cat_limit_map g).
  exact ((limit_corec_unique Z
    ((g $o f) $o cat_limit_cone J X) (lg $o lf)
    ((cat_limit_cone J Z $@L fmap_comp (diagonal02 A J) lf lg)
      $@ cat_assoc_opp
        (fmap (diagonal02 A J) lf)
        (fmap (diagonal02 A J) lg)
        (cat_limit_cone J Z)
      $@ (cat_limit_map_beta g $@R fmap (diagonal02 A J) lf)
      $@ cat_assoc
        (fmap (diagonal02 A J) lf)
        (cat_limit_cone J Y) g
      $@ (g $@L cat_limit_map_beta f)
      $@ cat_assoc_opp (cat_limit_cone J X) f g))^$).
Defined.

Global Instance is0functor_cat_limit
  {A J : Type} `{Is21Cat A, IsGraph J, !HasLimits J A}
  : Is0Functor (fun X : Fun02 J A => cat_limit J X)
  := Build_Is0Functor _ (fun _ _ => cat_limit_map).

Global Instance is1functor_cat_limit
  {A J : Type} `{Is21Cat A, IsGraph J, !HasLimits J A}
  : Is1Functor (fun X : Fun02 J A => cat_limit J X).
Proof.
  snapply Build_Is1Functor.
  - exact (fun X Y f g => cat_limit_map_modification).
  - exact cat_limit_map_id.
  - exact (fun X Y Z => cat_limit_map_comp).
Defined.

Definition fun12_cat_limit
  {A J : Type} `{Is21Cat A, IsGraph J, !HasLimits J A}
  : Fun12 (Fun02 J A) A
  := Build_Fun12 (fun X => cat_limit J X).

(** ** The diagonal-limit adjunction *)

(** The chosen cones assemble into the counit. *)
Definition cat_limit_counit
  {A J : Type} `{Is21Cat A, IsGraph J, !HasLimits J A}
  : NatTrans
      (fun12_compose (fun12_fun22 (fun22_diagonal02 A J))
        fun12_cat_limit)
      fun12_id.
Proof.
  snapply Build_NatTrans.
  - exact (fun X => cat_limit_cone J X).
  - snapply Build_Is1Natural.
    intros X Y f.
    exact (cat_limit_map_beta f).
Defined.

(** The unit is the map induced by the identity cone on a constant diagram. *)
Definition cat_limit_unit
  {A J : Type} `{Is21Cat A, IsGraph J, !HasLimits J A}
  (a : A)
  : a $-> cat_limit J (diagonal02 A J a)
  := limit_corec (diagonal02 A J a) (Id (diagonal02 A J a)).

Definition cat_limit_unit_beta
  {A J : Type} `{Is21Cat A, IsGraph J, !HasLimits J A}
  (a : A)
  : limit_cone_map
      (diagonal02 A J a)
      (cat_limit J (diagonal02 A J a))
      (cat_limit_cone J (diagonal02 A J a))
      a (cat_limit_unit (J := J) a)
    $== Id (diagonal02 A J a)
  := limit_beta (diagonal02 A J a) (Id (diagonal02 A J a)).

Definition cat_limit_unit_naturality
  {A J : Type} `{Is21Cat A, IsGraph J, !HasLimits J A}
  {a b : A} (f : a $-> b)
  : cat_limit_unit (J := J) b $o f
    $== cat_limit_map (fmap (diagonal02 A J) f)
      $o cat_limit_unit (J := J) a.
Proof.
  pose (df := fmap (diagonal02 A J) f).
  pose (ua := cat_limit_unit (J := J) a).
  pose (ub := cat_limit_unit (J := J) b).
  pose (lf := cat_limit_map df).
  change (ub $o f $== lf $o ua).
  napply (limit_cone_map_reflects
    (cat_limit_cone J (diagonal02 A J b))
    (cat_islimit_cone J (diagonal02 A J b))).
  exact (
    (cat_limit_cone J (diagonal02 A J b)
      $@L fmap_comp (diagonal02 A J) f ub)
    $@ cat_assoc_opp
      (fmap (diagonal02 A J) f)
      (fmap (diagonal02 A J) ub)
      (cat_limit_cone J (diagonal02 A J b))
    $@ (cat_limit_unit_beta (J := J) b
      $@R fmap (diagonal02 A J) f)
    $@ cat_idl (fmap (diagonal02 A J) f)
    $@ (
      (cat_limit_cone J (diagonal02 A J b)
        $@L fmap_comp (diagonal02 A J) ua lf)
      $@ cat_assoc_opp
        (fmap (diagonal02 A J) ua)
        (fmap (diagonal02 A J) lf)
        (cat_limit_cone J (diagonal02 A J b))
      $@ (cat_limit_map_beta df
        $@R fmap (diagonal02 A J) ua)
      $@ cat_assoc
        (fmap (diagonal02 A J) ua)
        (cat_limit_cone J (diagonal02 A J a)) df
      $@ (df $@L cat_limit_unit_beta (J := J) a)
      $@ cat_idr df)^$).
Defined.

Definition cat_limit_unit_nattrans
  {A J : Type} `{Is21Cat A, IsGraph J, !HasLimits J A}
  : NatTrans fun12_id
      (fun12_compose fun12_cat_limit
        (fun12_fun22 (fun22_diagonal02 A J))).
Proof.
  snapply Build_NatTrans.
  - exact (fun a => cat_limit_unit (J := J) a).
  - snapply Build_Is1Natural.
    exact (fun a b => cat_limit_unit_naturality (J := J)).
Defined.

Definition cat_limit_triangle_l
  {A J : Type} `{Is21Cat A, IsGraph J, !HasLimits J A}
  (a : A)
  : (cat_limit_counit (J := J)) (diagonal02 A J a)
      $o fmap (diagonal02 A J) (cat_limit_unit (J := J) a)
    $== Id (diagonal02 A J a)
  := cat_limit_unit_beta (J := J) a.

Definition cat_limit_triangle_r
  {A J : Type} `{Is21Cat A, IsGraph J, !HasLimits J A}
  (X : Fun02 J A)
  : cat_limit_map (cat_limit_cone J X)
      $o cat_limit_unit (J := J) (cat_limit J X)
    $== Id (cat_limit J X).
Proof.
  pose (c := cat_limit_cone J X).
  pose (u := cat_limit_unit (J := J) (cat_limit J X)).
  pose (lc := cat_limit_map c).
  change (lc $o u $== Id (cat_limit J X)).
  napply (limit_cone_map_reflects c (cat_islimit_cone J X)).
  exact (
    (c $@L fmap_comp (diagonal02 A J) u lc)
    $@ cat_assoc_opp
      (fmap (diagonal02 A J) u)
      (fmap (diagonal02 A J) lc) c
    $@ (cat_limit_map_beta c $@R fmap (diagonal02 A J) u)
    $@ cat_assoc
      (fmap (diagonal02 A J) u)
      (cat_limit_cone J (diagonal02 A J (cat_limit J X))) c
    $@ (c $@L cat_limit_unit_beta (J := J) (cat_limit J X))
    $@ cat_idr c
    $@ (limit_cone_map_id c)^$).
Defined.

(** A coherent choice of local universal cones therefore determines the
    diagonal-limit adjunction; the adjunction is derived data, not an
    additional field of [HasLimits]. *)
Definition gpd_adjunction_cat_limit
  {A J : Type} `{Is21Cat A, IsGraph J, !HasLimits J A}
  : GpdAdjunction
      (fun12_fun22 (fun22_diagonal02 A J))
      (fun12_cat_limit (J := J)).
Proof.
  napply (Build_GpdAdjunction_unit_counit
    (fun12_fun22 (fun22_diagonal02 A J))
    (fun12_cat_limit (J := J))
    (cat_limit_counit (J := J))
    (cat_limit_unit_nattrans (J := J))).
  - exact (cat_limit_triangle_l (J := J)).
  - exact (cat_limit_triangle_r (J := J)).
  Unshelve.
  all: exact _.
Defined.
