Require Import Basics.Overture Basics.Tactics.
Require Import WildCat.Core WildCat.Equiv WildCat.FunctorCat WildCat.Induced
  WildCat.NatTrans.
Require Import WildCat.Cylinder WildCat.Square WildCat.TwoOneCat
  WildCat.Universe WildCat.OneGroupoid.

Set Typeclasses Depth 3.


(** * Coherent functors between wild (2,1)-categories *)

(** An [Is1Functor] acts on 2-cells, but the action is not currently bundled as a 0-functor between hom-categories. *)
Instance is0functor_fmap
  {A B : Type} `{Is1Cat A} `{Is1Cat B}
  (F : A -> B) `{!Is0Functor F, !Is1Functor F} (a b : A)
  : Is0Functor (@fmap A B _ _ F _ a b).
Proof.
  snapply Build_Is0Functor.
  exact (fun f g p => fmap2 F p).
Defined.

(** A 2-coherent 1-functor between [(2,1)]-categories.  In addition to acting functorially on each hom-category, its compositor is natural in 2-cells and satisfies the pseudofunctor associativity and unit laws. *)
Class Is2Functor {A B : Type} `{Is21Cat A} `{Is21Cat B}
  (F : A -> B)
  `{!Is0Functor F, !Is1Functor F} := {
  is1functor_fmap :: forall a b,
    Is1Functor (@fmap A B _ _ F _ a b);

  fmap_comp_natural : forall {a b c : A}
      {f f' : a $-> b} {g g' : b $-> c}
      (p : f $== f') (q : g $== g'),
    fmap2 F (p $@@ q) $@ fmap_comp F f' g'
    $== fmap_comp F f g $@ (fmap2 F p $@@ fmap2 F q);

  fmap_assoc : forall {a b c d : A}
      (f : a $-> b) (g : b $-> c) (h : c $-> d),
    fmap2 F (cat_assoc f g h)
      $@ fmap_comp F (g $o f) h
      $@ (fmap F h $@L fmap_comp F f g)
    $== fmap_comp F f (h $o g)
      $@ (fmap_comp F g h $@R fmap F f)
      $@ cat_assoc (fmap F f) (fmap F g) (fmap F h);

  fmap_idl : forall {a b : A} (f : a $-> b),
    fmap2 F (cat_idl f)
    $== fmap_comp F f (Id b)
      $@ (fmap_id F b $@R fmap F f)
      $@ cat_idl (fmap F f);

  fmap_idr : forall {a b : A} (f : a $-> b),
    fmap2 F (cat_idr f)
    $== fmap_comp F (Id a) f
      $@ (fmap F f $@L fmap_id F a)
      $@ cat_idr (fmap F f);
}.

Arguments fmap_comp_natural
  {A B _ _ _ _ _ _ _ _ _ _ _ _ F _ _ _ a b c f f' g g'} p q.
Arguments fmap_assoc
  {A B _ _ _ _ _ _ _ _ _ _ _ _ F _ _ _ a b c d} f g h.
Arguments fmap_idl
  {A B _ _ _ _ _ _ _ _ _ _ _ _ F _ _ _ a b} f.
Arguments fmap_idr
  {A B _ _ _ _ _ _ _ _ _ _ _ _ F _ _ _ a b} f.

Definition fmap3
  {A B : Type} `{Is21Cat A, Is21Cat B}
  (F : A -> B) `{!Is0Functor F, !Is1Functor F, !Is2Functor F}
  {a b : A} {f g : a $-> b} {p q : f $== g}
  (h : p $== q)
  : fmap2 F p $== fmap2 F q.
Proof.
  exact (fmap2 (@fmap _ _ _ _ F _ a b) h).
Defined.

(** Naturality of a pseudofunctor compositor when only the first
    morphism varies. *)
Definition fmap2_postwhisker
  {A B : Type} `{Is21Cat A, Is21Cat B}
  (F : A -> B) `{!Is0Functor F, !Is1Functor F, !Is2Functor F}
  {a b c : A} {f f' : a $-> b} (p : f $== f') (g : b $-> c)
  : fmap_comp F f g $@ (fmap F g $@L fmap2 F p)
    $== fmap2 F (g $@L p) $@ fmap_comp F f' g.
Proof.
  symmetry.
  lhs' exact (fmap_comp F f' g $@L
    (fmap3 F (cat_comp2_idr p g))^$).
  lhs' exact (fmap_comp_natural p (Id g)).
  rapply cat_prewhisker.
  napply cat_comp2_homotopic_idr.
  exact (fmap_id (@fmap _ _ _ _ F _ b c) g).
Defined.

(** The opposite orientation of compositor naturality, convenient when
    the compositor is the naturality cell of a pseudonatural
    transformation. *)
Definition fmap2_postwhisker_opp
  {A B : Type} `{Is21Cat A, Is21Cat B}
  (F : A -> B) `{!Is0Functor F, !Is1Functor F, !Is2Functor F}
  {a b c : A} {f f' : a $-> b} (p : f $== f') (g : b $-> c)
  : fmap2 F (g $@L p) $@ fmap_comp F f' g
    $== fmap_comp F f g $@ (fmap F g $@L fmap2 F p)
  := (fmap2_postwhisker F p g)^$.

(** Naturality of a pseudofunctor compositor when only the second
    morphism varies. *)
Definition fmap2_prewhisker
  {A B : Type} `{Is21Cat A, Is21Cat B}
  (F : A -> B) `{!Is0Functor F, !Is1Functor F, !Is2Functor F}
  {a b c : A} (f : a $-> b) {g g' : b $-> c} (q : g $== g')
  : fmap_comp F f g $@ (fmap2 F q $@R fmap F f)
    $== fmap2 F (q $@R f) $@ fmap_comp F f g'.
Proof.
  symmetry.
  lhs' exact (fmap_comp F f g' $@L
    (fmap3 F (cat_comp2_idl f q))^$).
  lhs' exact (fmap_comp_natural (Id f) q).
  rapply cat_prewhisker.
  napply cat_comp2_homotopic_idl.
  exact (fmap_id (@fmap _ _ _ _ F _ a b) f).
Defined.

(** The opposite orientation of [fmap2_prewhisker]. *)
Definition fmap2_prewhisker_opp
  {A B : Type} `{Is21Cat A, Is21Cat B}
  (F : A -> B) `{!Is0Functor F, !Is1Functor F, !Is2Functor F}
  {a b c : A} (f : a $-> b) {g g' : b $-> c} (q : g $== g')
  : fmap2 F (q $@R f) $@ fmap_comp F f g'
    $== fmap_comp F f g $@ (fmap2 F q $@R fmap F f)
  := (fmap2_prewhisker F f q)^$.

Definition fmap_cylinder
  {A B : Type} `{Is21Cat A, Is21Cat B}
  (F : A -> B) `{!Is0Functor F, !Is1Functor F, !Is2Functor F}
  {x00 x20 x02 x22 : A}
  {f : x00 $-> x20} {g : x02 $-> x22}
  {u0 u1 : x00 $-> x02} {v0 v1 : x20 $-> x22}
  {p : u0 $== u1} {q : v0 $== v1}
  {s0 : Square u0 v0 f g} {s1 : Square u1 v1 f g}
  (c : Cylinder p q s0 s1)
  : Cylinder
      (fmap2 F p) (fmap2 F q)
      (fmap_square F s0) (fmap_square F s1).
Proof.
  unfold Cylinder, fmap_square, Square in *.
  lhs' exact (cat_assoc_opp _ _ _).
  lhs' exact (fmap2_postwhisker F p g $@R _).
  lhs' exact (cat_assoc _ _ _).
  lhs' exact (_ $@L cat_assoc_opp _ _ _).
  lhs' napply (fun h =>
    _ $@L (h $@R (fmap_comp F f v0)^$)).
  { lhs' exact (fmap_comp
      (@fmap _ _ _ _ F _ x00 x22) s0 (g $@L p))^$.
    lhs' exact (fmap3 F c).
    exact (fmap_comp
      (@fmap _ _ _ _ F _ x00 x22) (q $@R f) s1). }
  lhs' exact (_ $@L cat_assoc _ _ _).
  lhs' exact (_ $@L (_ $@L
    hinverse_square_gpd (fmap2_prewhisker F f q))).
  lhs' exact (_ $@L cat_assoc_opp _ _ _).
  exact (cat_assoc_opp _ _ _).
Defined.

(** [Fun22] bundles a fully coherent pseudofunctor between wild
    [(2,1)]-categories.  Its underlying object data agrees with the
    2-coherent end of the [Fun01]/[Fun11] hierarchy, while its second
    index records that genuine higher cells will be retained. *)
Record Fun22 (A B : Type) `{Is21Cat A} `{Is21Cat B} := {
  fun22_fun : A -> B;
  is0functor_fun22 :: Is0Functor fun22_fun;
  is1functor_fun22 :: Is1Functor fun22_fun;
  is2functor_fun22 :: Is2Functor fun22_fun;
}.

Coercion fun22_fun : Fun22 >-> Funclass.

Arguments Build_Fun22 {A B} {_ _ _ _ _ _ _ _ _ _ _ _}
  fun22_fun
  {is0functor_fun22 is1functor_fun22 is2functor_fun22} : rename.
Arguments fun22_fun {A B} {_ _ _ _ _ _ _ _ _ _ _ _} : rename.

Definition fun11_fun22 {A B : Type} `{Is21Cat A} `{Is21Cat B}
  (F : Fun22 A B) : Fun11 A B
  := Build_Fun11 _ _ F.

Coercion fun11_fun22 : Fun22 >-> Fun11.

(** A pseudonatural transformation has the usual naturality 2-cell, naturality in 2-cells, and compatibility with identities and composition. *)
Record PseudoNatTrans {A B : Type} `{Is21Cat A} `{Is21Cat B}
  (F G : Fun22 A B) := {
  nattrans_pseudonat :> NatTrans F G;

  pseudonat_2cell : forall {a b : A} {f g : a $-> b}
      (p : f $== g),
    Square
      (isnat nattrans_pseudonat f)
      (isnat nattrans_pseudonat g)
      (nattrans_pseudonat b $@L fmap2 F p)
      (fmap2 G p $@R nattrans_pseudonat a);

  pseudonat_id : forall a : A,
    isnat nattrans_pseudonat (Id a)
    $== (nattrans_pseudonat a $@L fmap_id F a)
      $@ cat_idr (nattrans_pseudonat a)
      $@ (cat_idl (nattrans_pseudonat a))^$
      $@ ((fmap_id G a $@R nattrans_pseudonat a)^$);

  pseudonat_comp : forall {a b c : A}
      (f : a $-> b) (g : b $-> c),
    isnat nattrans_pseudonat (g $o f)
    $== (nattrans_pseudonat c $@L fmap_comp F f g)
      $@ cat_assoc_opp (fmap F f) (fmap F g)
            (nattrans_pseudonat c)
      $@ (isnat nattrans_pseudonat g $@R fmap F f)
      $@ cat_assoc (fmap F f) (nattrans_pseudonat b) (fmap G g)
      $@ (fmap G g $@L isnat nattrans_pseudonat f)
      $@ cat_assoc_opp (nattrans_pseudonat a)
            (fmap G f) (fmap G g)
      $@ ((fmap_comp G f g)^$ $@R nattrans_pseudonat a);
}.

Arguments PseudoNatTrans {A B _ _ _ _ _ _ _ _ _ _ _ _} F G.
Arguments nattrans_pseudonat
  {A B _ _ _ _ _ _ _ _ _ _ _ _ F G} p : rename.
Arguments pseudonat_2cell
  {A B _ _ _ _ _ _ _ _ _ _ _ _ F G} p {a b f g} q : rename.
Arguments pseudonat_id
  {A B _ _ _ _ _ _ _ _ _ _ _ _ F G} p a : rename.
Arguments pseudonat_comp
  {A B _ _ _ _ _ _ _ _ _ _ _ _ F G} p {a b c} f g : rename.

Definition pseudonat_comp_component_1gpd
  {A : Type} `{Is21Cat A}
  {F G : Fun22 A OneGpd} (alpha : PseudoNatTrans F G)
  {a b c : A} (f : a $-> b) (g : b $-> c) (x : F a)
  : OneGpdHom
      (isnat alpha (g $o f) x)
      (onegpd_comp
        (onegpd_comp
          (onegpd_comp
            (onegpd_fmap (alpha c) (fmap_comp F f g x))
            (isnat alpha g (fmap F f x)))
          (onegpd_fmap (fmap G g) (isnat alpha f x)))
        (onegpd_rev (fmap_comp G f g (alpha a x)))).
Proof.
  rapply onegpd_hom_comp.
  - exact ((pseudonat_comp alpha f g) x).
  - cbn.
    lhs' exact (_ $@L (_ $@L (_ $@L (_ $@L (_ $@L
      ((gpd_rev_1 $@R _) $@ cat_idl _)))))).
    lhs' exact (_ $@L (_ $@L (_ $@L cat_idl _))).
    lhs' exact (_ $@L ((gpd_rev_1 $@R _) $@ cat_idl _)).
    rapply onegpd_hom_id.
Defined.

(** Solving the compositor law for the target compositor gives the
    form used when a pseudonatural transformation is evaluated at an
    identity morphism. *)
Definition pseudonat_comp_cancel_component_1gpd
  {A : Type} `{Is21Cat A}
  {F G : Fun22 A OneGpd} (alpha : PseudoNatTrans F G)
  {a b c : A} (f : a $-> b) (g : b $-> c) (x : F a)
  : OneGpdHom
      (onegpd_comp
        (fmap_comp G f g (alpha a x))
        (onegpd_fmap (fmap G g)
          (onegpd_rev (isnat alpha f x))))
      (onegpd_comp
        (onegpd_comp
          (onegpd_rev (isnat alpha (g $o f) x))
          (onegpd_fmap (alpha c) (fmap_comp F f g x)))
        (isnat alpha g (fmap F f x))).
Proof.
  lhs' exact (onegpd_hom_prewhisker
    (onegpd_fmap_rev (fmap G g) (isnat alpha f x)) _).
  pose (coh := pseudonat_comp_component_1gpd alpha f g x).
  pose (move := onegpd_solve_inverse_left coh).
  lhs' exact (onegpd_hom_postwhisker _ move).
  lhs' exact (onegpd_hom_assoc _ _ _).
  lhs' exact (onegpd_hom_prewhisker (onegpd_hom_V_hh _ _) _).
  exact (onegpd_hom_assoc_opp _ _ _).
Defined.

(** A modification is a pointwise 2-cell satisfying the cylinder condition between the naturality 2-cells. *)
Record Modification {A B : Type} `{Is21Cat A} `{Is21Cat B}
  {F G : Fun22 A B} (alpha beta : PseudoNatTrans F G) := {
  modification_component : forall a, alpha a $== beta a;
  modification_isnatural : forall {a b : A} (f : a $-> b),
    Cylinder
      (modification_component a)
      (modification_component b)
      (isnat alpha f) (isnat beta f);
}.

Arguments Modification
  {A B _ _ _ _ _ _ _ _ _ _ _ _ F G} alpha beta.
Arguments modification_component
  {A B _ _ _ _ _ _ _ _ _ _ _ _ F G alpha beta} m a : rename.
Arguments modification_isnatural
  {A B _ _ _ _ _ _ _ _ _ _ _ _ F G alpha beta} m {a b} f : rename.

(** Solving a modification cylinder for the inverse of the lower
    naturality cell. *)
Definition modification_isnatural_cancel_component_1gpd
  {A : Type} `{Is21Cat A}
  {F G : Fun22 A OneGpd}
  {alpha beta : PseudoNatTrans F G}
  (p : Modification alpha beta)
  {a b : A} (f : a $-> b) (x : F a)
  : OneGpdHom
      (onegpd_comp
        (onegpd_fmap (fmap G f) (modification_component p a x))
        (onegpd_rev (isnat beta f x)))
      (onegpd_comp
        (onegpd_rev (isnat alpha f x))
        (modification_component p b (fmap F f x))).
Proof.
  exact (onegpd_hom_rev
    ((hinverse_square_gpd (modification_isnatural p f)) x)).
Defined.

Definition modification_id
  {A B : Type} `{Is21Cat A} `{Is21Cat B}
  {F G : Fun22 A B} (alpha : PseudoNatTrans F G)
  : Modification alpha alpha.
Proof.
  snapply Build_Modification.
  - exact (fun a => Id (alpha a)).
  - intros a b f.
    apply cylinder_refl.
Defined.

Definition modification_comp
  {A B : Type} `{Is21Cat A} `{Is21Cat B}
  {F G : Fun22 A B}
  {alpha beta gamma : PseudoNatTrans F G}
  (q : Modification beta gamma) (p : Modification alpha beta)
  : Modification alpha gamma.
Proof.
  snapply Build_Modification.
  - exact (fun a =>
      modification_component p a $@ modification_component q a).
  - intros a b f.
    exact (cylinder_comp
      (modification_isnatural p f)
      (modification_isnatural q f)).
Defined.

Definition modification_inverse
  {A B : Type} `{Is21Cat A} `{Is21Cat B}
  {F G : Fun22 A B} {alpha beta : PseudoNatTrans F G}
  (p : Modification alpha beta)
  : Modification beta alpha.
Proof.
  snapply Build_Modification.
  - exact (fun a => (modification_component p a)^$).
  - intros a b f.
    exact (cylinder_inverse (modification_isnatural p f)).
Defined.

Instance isgraph_pseudonat
  {A B : Type} `{Is21Cat A} `{Is21Cat B}
  (F G : Fun22 A B)
  : IsGraph (PseudoNatTrans F G).
Proof.
  snapply Build_IsGraph.
  exact Modification.
Defined.

Instance is01cat_pseudonat
  {A B : Type} `{Is21Cat A} `{Is21Cat B}
  (F G : Fun22 A B)
  : Is01Cat (PseudoNatTrans F G).
Proof.
  snapply Build_Is01Cat.
  - exact modification_id.
  - exact (fun alpha beta gamma => modification_comp).
Defined.

Instance is0gpd_pseudonat
  {A B : Type} `{Is21Cat A} `{Is21Cat B}
  (F G : Fun22 A B)
  : Is0Gpd (PseudoNatTrans F G).
Proof.
  snapply Build_Is0Gpd.
  exact (fun alpha beta => modification_inverse).
Defined.

Instance is2graph_pseudonat
  {A B : Type} `{Is21Cat A} `{Is21Cat B}
  (F G : Fun22 A B)
  : Is2Graph (PseudoNatTrans F G).
Proof.
  intros alpha beta.
  snapply Build_IsGraph.
  intros p q.
  exact (forall a,
    modification_component p a $== modification_component q a).
Defined.

Instance is1cat_pseudonat
  {A B : Type} `{Is21Cat A} `{Is21Cat B}
  (F G : Fun22 A B)
  : Is1Cat (PseudoNatTrans F G).
Proof.
  snapply Build_Is1Cat.
  { intros alpha beta.
    snapply Build_Is01Cat.
    { intros p a.
      exact (Id (modification_component p a)). }
    intros p q r h k a.
    exact (k a $@ h a). }
  { intros alpha beta.
    snapply Build_Is0Gpd.
    intros p q h a.
    exact ((h a)^$). }
  { intros alpha beta gamma q.
    snapply Build_Is0Functor.
    intros p r h a.
    exact (modification_component q a $@L h a). }
  { intros alpha beta gamma p.
    snapply Build_Is0Functor.
    intros q r h a.
    exact (h a $@R modification_component p a). }
  { intros alpha beta gamma delta p q r a.
    exact (cat_assoc
      (modification_component p a)
      (modification_component q a)
      (modification_component r a)). }
  { intros alpha beta gamma delta p q r a.
    exact (cat_assoc_opp
      (modification_component p a)
      (modification_component q a)
      (modification_component r a)). }
  { intros alpha beta p a.
    exact (cat_idl (modification_component p a)). }
  intros alpha beta p a.
  exact (cat_idr (modification_component p a)).
Defined.

Instance is1gpd_pseudonat
  {A B : Type} `{Is21Cat A} `{Is21Cat B}
  (F G : Fun22 A B)
  : Is1Gpd (PseudoNatTrans F G).
Proof.
  snapply Build_Is1Gpd.
  { intros alpha beta p a.
    exact (gpd_issect (modification_component p a)). }
  intros alpha beta p a.
  exact (gpd_isretr (modification_component p a)).
Defined.

(** The hom 1-groupoid between coherent functors.  Its objects are
    pseudonatural transformations, its morphisms are modifications, and
    its higher morphisms are pointwise 3-cells. *)
Definition pseudonat_1gpd
  {A B : Type} `{Is21Cat A} `{Is21Cat B}
  (F G : Fun22 A B)
  : OneGpd.
Proof.
  napply (Build_OneGpd (PseudoNatTrans F G)).
  all: exact _.
Defined.

(** ** The coherent-functor hierarchy *)

(** [Fun02] has the same object-level data as [Fun01].  It is kept as a
    distinct type because its 2-cells are modifications satisfying a
    cylinder condition, rather than arbitrary pointwise 2-cells. *)
Record Fun02 (A B : Type) `{IsGraph A} `{IsGraph B} := {
  fun02_fun : A -> B;
  is0functor_fun02 :: Is0Functor fun02_fun;
}.

Coercion fun02_fun : Fun02 >-> Funclass.

Arguments Build_Fun02 {A B _ _} fun02_fun
  {is0functor_fun02} : rename.
Arguments fun02_fun {A B _ _} : rename.

Definition fun01_fun02 {A B : Type} `{IsGraph A} `{IsGraph B}
  (F : Fun02 A B) : Fun01 A B
  := Build_Fun01 F.

(** [Fun12] similarly has the object-level data of [Fun11], but lives
    in the coherent second column of the hierarchy. *)
Record Fun12 (A B : Type) `{Is1Cat A} `{Is1Cat B} := {
  fun12_fun : A -> B;
  is0functor_fun12 :: Is0Functor fun12_fun;
  is1functor_fun12 :: Is1Functor fun12_fun;
}.

Coercion fun12_fun : Fun12 >-> Funclass.

Arguments Build_Fun12 {A B _ _ _ _ _ _ _ _} fun12_fun
  {is0functor_fun12 is1functor_fun12} : rename.
Arguments fun12_fun {A B _ _ _ _ _ _ _ _} : rename.

Definition fun02_fun12 {A B : Type} `{Is1Cat A} `{Is1Cat B}
  (F : Fun12 A B) : Fun02 A B
  := Build_Fun02 F.

Definition fun11_fun12 {A B : Type} `{Is1Cat A} `{Is1Cat B}
  (F : Fun12 A B) : Fun11 A B
  := Build_Fun11 _ _ F.

Definition fun12_fun22 {A B : Type} `{Is21Cat A} `{Is21Cat B}
  (F : Fun22 A B) : Fun12 A B
  := Build_Fun12 F.

(** A cubical transformation retains precisely the naturality cube
    needed when postcomposition acts on coherent graph-indexed
    diagrams.  Its endpoints only need their [Fun12] structure. *)
Record CubicalNatTrans12
  {A B : Type} `{Is21Cat A} `{Is21Cat B}
  (F G : Fun12 A B) := {
  nattrans_cubical12 :> NatTrans F G;
  cubical12_naturality : forall
      {x00 x20 x02 x22 : A}
      {f : x00 $-> x20} {g : x02 $-> x22}
      {u : x00 $-> x02} {v : x20 $-> x22}
      (s : Square u v f g),
    Cylinder
      (isnat nattrans_cubical12 u)
      (isnat nattrans_cubical12 v)
      (fmap_square F s $@v isnat nattrans_cubical12 g)
      (isnat nattrans_cubical12 f $@v fmap_square G s);
}.

Arguments CubicalNatTrans12
  {A B _ _ _ _ _ _ _ _ _ _ _ _} F G.
Arguments nattrans_cubical12
  {A B _ _ _ _ _ _ _ _ _ _ _ _ F G} p : rename.
Arguments cubical12_naturality
  {A B _ _ _ _ _ _ _ _ _ _ _ _ F G} alpha
  {x00 x20 x02 x22 f g u v} s : rename.

(** ** Coherent 2-cells between graph-indexed diagrams *)

(** For a graph-shaped diagram no coherence is required of its action on
    arrows.  Nevertheless, a 2-cell between natural transformations must
    remember the usual modification square. *)
Record NatModification {A B : Type} `{IsGraph A} `{Is21Cat B}
  {F G : A -> B} `{!Is0Functor F, !Is0Functor G}
  (alpha beta : NatTrans F G) := {
  natmod_component : forall a, alpha a $== beta a;
  natmod_isnatural : forall {a b : A} (f : a $-> b),
    Cylinder
      (natmod_component a)
      (natmod_component b)
      (isnat alpha f) (isnat beta f);
}.

Definition natmod_id {A B : Type} `{IsGraph A} `{Is21Cat B}
  {F G : A -> B} `{!Is0Functor F, !Is0Functor G}
  (alpha : NatTrans F G)
  : NatModification alpha alpha.
Proof.
  snapply Build_NatModification.
  - exact (fun a => Id (alpha a)).
  - intros a b f.
    apply cylinder_refl.
Defined.

Definition natmod_comp {A B : Type} `{IsGraph A} `{Is21Cat B}
  {F G : A -> B} `{!Is0Functor F, !Is0Functor G}
  {alpha beta gamma : NatTrans F G}
  (q : NatModification beta gamma) (p : NatModification alpha beta)
  : NatModification alpha gamma.
Proof.
  snapply Build_NatModification.
  - exact (fun a =>
      natmod_component alpha beta p a
      $@ natmod_component beta gamma q a).
  - intros a b f.
    exact (cylinder_comp
      (natmod_isnatural alpha beta p f)
      (natmod_isnatural beta gamma q f)).
Defined.

Instance transitive_natmodification
  {A B : Type} `{IsGraph A} `{Is21Cat B}
  {F G : A -> B} `{!Is0Functor F, !Is0Functor G}
  : Transitive (NatModification (F := F) (G := G)).
Proof.
  intros alpha beta gamma p q.
  exact (natmod_comp q p).
Defined.

Definition natmod_inverse {A B : Type} `{IsGraph A} `{Is21Cat B}
  {F G : A -> B} `{!Is0Functor F, !Is0Functor G}
  {alpha beta : NatTrans F G}
  (p : NatModification alpha beta)
  : NatModification beta alpha.
Proof.
  snapply Build_NatModification.
  - exact (fun a =>
      (natmod_component alpha beta p a)^$).
  - intros a b f.
    exact (cylinder_inverse
      (natmod_isnatural alpha beta p f)).
Defined.

Definition natmod_prewhisker
  {A B C : Type} `{IsGraph A, Is1Cat B, Is21Cat C}
  {F G : B -> C} `{!Is0Functor F, !Is0Functor G}
  {alpha beta : NatTrans F G} (p : NatModification alpha beta)
  (K : Fun02 A B)
  : NatModification
      (nattrans_prewhisker alpha K)
      (nattrans_prewhisker beta K).
Proof.
  snapply Build_NatModification.
  { exact (fun a => natmod_component alpha beta p (K a)). }
  intros a b f.
  exact (natmod_isnatural alpha beta p (fmap K f)).
Defined.

Definition natmod_postcompose {A B : Type} `{IsGraph A} `{Is21Cat B}
  {F G K : A -> B}
  `{!Is0Functor F, !Is0Functor G, !Is0Functor K}
  (delta : NatTrans G K)
  {alpha beta : NatTrans F G} (p : NatModification alpha beta)
  : NatModification (nattrans_comp delta alpha) (nattrans_comp delta beta).
Proof.
  snapply Build_NatModification.
  { exact (fun a => delta a $@L natmod_component alpha beta p a). }
  intros a b f.
  cbn beta.
  exact (cylinder_vconcat_below
    (isnat delta f)
    (natmod_isnatural alpha beta p f)).
Defined.

Definition natmod_precompose {A B : Type} `{IsGraph A} `{Is21Cat B}
  {K F G : A -> B}
  `{!Is0Functor K, !Is0Functor F, !Is0Functor G}
  (delta : NatTrans K F)
  {alpha beta : NatTrans F G} (p : NatModification alpha beta)
  : NatModification (nattrans_comp alpha delta) (nattrans_comp beta delta).
Proof.
  snapply Build_NatModification.
  { exact (fun a => natmod_component alpha beta p a $@R delta a). }
  intros a b f.
  cbn beta.
  exact (cylinder_vconcat_above
    (isnat delta f)
    (natmod_isnatural alpha beta p f)).
Defined.

(** ** Remaining proof skeleton *)

(** The target of the graph-indexed part of this file is
    [Is21Cat (Fun02 A B)].  The construction is deliberately split as
    follows.

    1. The graph, composition of natural transformations, vertical
       composition of modifications, and whiskering of modifications
       are defined directly.
    2. The only non-pointwise inputs needed for [Is1Cat (Fun02 A B)]
       are the following three statements:

       [natmod_assoc :
          ((gamma $o beta) $o alpha)
          $-> (gamma $o (beta $o alpha))]

       [natmod_idl : (Id G $o alpha) $-> alpha]

       [natmod_idr : (alpha $o Id F) $-> alpha].

       Their components are respectively [cat_assoc], [cat_idl], and
       [cat_idr].  Proving their cylinder conditions is the hard
       coherence calculation and is intentionally deferred.
    3. Given those three inputs, the remaining [Is1Cat] and [Is21Cat]
       fields are pointwise consequences of the structure on [B].
    4. The structure on [Fun12] is induced from [Fun02].  The [Fun22]
       pseudofunctor layer is separate and comes afterwards. *)

(** ** Categorical operations in [Fun02] *)

Instance isgraph_fun02
  (A B : Type) `{IsGraph A} `{Is1Cat B}
  : IsGraph (Fun02 A B)
  := isgraph_induced fun01_fun02.

Instance is01cat_fun02
  (A B : Type) `{IsGraph A} `{Is1Cat B}
  : Is01Cat (Fun02 A B)
  := is01cat_induced fun01_fun02.

Instance is2graph_fun02
  (A B : Type) `{IsGraph A} `{Is21Cat B}
  : Is2Graph (Fun02 A B).
Proof.
  intros [F fF] [G fG].
  snapply Build_IsGraph.
  intros alpha beta.
  exact (NatModification alpha beta).
Defined.

Definition natmod_assoc_from_cylinder
  {A B : Type} `{IsGraph A} `{Is21Cat B}
  {F G K L : Fun02 A B}
  (alpha : F $-> G) (beta : G $-> K) (gamma : K $-> L)
  : ((gamma $o beta) $o alpha)
    $-> (gamma $o (beta $o alpha)).
Proof.
  snapply Build_NatModification.
  { exact (fun a => cat_assoc (alpha a) (beta a) (gamma a)). }
  intros a b f.
  cbn beta.
  exact (square_vconcat_assoc
    (isnat alpha f) (isnat beta f) (isnat gamma f)).
Defined.

Definition natmod_idl_from_cylinder
  {A B : Type} `{IsGraph A} `{Is21Cat B}
  {F G : Fun02 A B} (alpha : F $-> G)
  : (Id G $o alpha) $-> alpha.
Proof.
  snapply Build_NatModification.
  { exact (fun a => cat_idl (alpha a)). }
  intros a b f.
  cbn beta.
  exact (square_vconcat_idl (isnat alpha f)).
Defined.

Definition natmod_idr_from_cylinder
  {A B : Type} `{IsGraph A} `{Is21Cat B}
  {F G : Fun02 A B} (alpha : F $-> G)
  : (alpha $o Id F) $-> alpha.
Proof.
  snapply Build_NatModification.
  { exact (fun a => cat_idr (alpha a)). }
  intros a b f.
  cbn beta.
  exact (square_vconcat_idr (isnat alpha f)).
Defined.

Instance is01cat_hom_fun02
  {A B : Type} `{IsGraph A} `{Is21Cat B}
  (F G : Fun02 A B)
  : Is01Cat (F $-> G).
Proof.
  snapply Build_Is01Cat.
  { exact natmod_id. }
  intros alpha beta gamma q p.
  exact (natmod_comp q p).
Defined.

Instance is0gpd_hom_fun02
  {A B : Type} `{IsGraph A} `{Is21Cat B}
  (F G : Fun02 A B)
  : Is0Gpd (F $-> G).
Proof.
  snapply Build_Is0Gpd.
  intros alpha beta p.
  exact (natmod_inverse p).
Defined.

Instance is0functor_postcomp_fun02
  {A B : Type} `{IsGraph A} `{Is21Cat B}
  (F G K : Fun02 A B) (delta : G $-> K)
  : Is0Functor (cat_postcomp F delta).
Proof.
  snapply Build_Is0Functor.
  intros alpha beta p.
  exact (natmod_postcompose delta p).
Defined.

Instance is0functor_precomp_fun02
  {A B : Type} `{IsGraph A} `{Is21Cat B}
  (F G K : Fun02 A B) (delta : F $-> G)
  : Is0Functor (cat_precomp K delta).
Proof.
  snapply Build_Is0Functor.
  intros alpha beta p.
  exact (natmod_precompose delta p).
Defined.

(** Three-cells between modifications are pointwise three-cells. *)
Instance is3graph_fun02
  (A B : Type) `{IsGraph A} `{Is21Cat B}
  : Is3Graph (Fun02 A B).
Proof.
  intros [F fF] [G fG] alpha beta.
  snapply Build_IsGraph.
  intros p q.
  exact (forall a,
    natmod_component alpha beta p a
      $== natmod_component alpha beta q a).
Defined.

(** The homs in [Fun02] are already honest 1-groupoids before the
    outer associativity and unit modifications have been constructed. *)
Instance is1cat_hom_fun02
  {A B : Type} `{IsGraph A} `{Is21Cat B}
  (F G : Fun02 A B)
  : Is1Cat (F $-> G).
Proof.
  snapply Build_Is1Cat.
  { intros alpha beta.
    snapply Build_Is01Cat.
    { intros p a.
      exact (Id (natmod_component alpha beta p a)). }
    intros p q r h k a.
    exact (k a $@ h a). }
  { intros alpha beta.
    snapply Build_Is0Gpd.
    intros p q h a.
    exact ((h a)^$). }
  { intros alpha beta gamma q.
    snapply Build_Is0Functor.
    intros p r h a.
    exact (natmod_component beta gamma q a $@L h a). }
  { intros alpha beta gamma p.
    snapply Build_Is0Functor.
    intros q r h a.
    exact (h a $@R natmod_component alpha beta p a). }
  { intros alpha beta gamma delta p q r a.
    exact (cat_assoc
      (natmod_component alpha beta p a)
      (natmod_component beta gamma q a)
      (natmod_component gamma delta r a)). }
  { intros alpha beta gamma delta p q r a.
    exact (cat_assoc_opp
      (natmod_component alpha beta p a)
      (natmod_component beta gamma q a)
      (natmod_component gamma delta r a)). }
  { intros alpha beta p a.
    exact (cat_idl (natmod_component alpha beta p a)). }
  intros alpha beta p a.
  exact (cat_idr (natmod_component alpha beta p a)).
Defined.

Instance is1gpd_hom_fun02
  {A B : Type} `{IsGraph A} `{Is21Cat B}
  (F G : Fun02 A B)
  : Is1Gpd (F $-> G).
Proof.
  snapply Build_Is1Gpd.
  { intros alpha beta p a.
    exact (gpd_issect (natmod_component alpha beta p a)). }
  intros alpha beta p a.
  exact (gpd_isretr (natmod_component alpha beta p a)).
Defined.

Instance is1functor_postcomp_fun02
  {A B : Type} `{IsGraph A} `{Is21Cat B}
  (F G K : Fun02 A B) (delta : G $-> K)
  : Is1Functor (cat_postcomp F delta).
Proof.
  snapply Build_Is1Functor.
  { intros alpha beta p q h a.
    exact (fmap2 (cat_postcomp _ (delta a)) (h a)). }
  { intros alpha a.
    exact (fmap_id (cat_postcomp _ (delta a))
      (alpha a)). }
  intros alpha beta gamma p q a.
  exact (fmap_comp (cat_postcomp _ (delta a))
    (natmod_component alpha beta p a)
    (natmod_component beta gamma q a)).
Defined.

Instance is1functor_precomp_fun02
  {A B : Type} `{IsGraph A} `{Is21Cat B}
  (F G K : Fun02 A B) (delta : F $-> G)
  : Is1Functor (cat_precomp K delta).
Proof.
  snapply Build_Is1Functor.
  { intros alpha beta p q h a.
    exact (fmap2 (cat_precomp _ (delta a)) (h a)). }
  { intros alpha a.
    exact (fmap_id (cat_precomp _ (delta a))
      (alpha a)). }
  intros alpha beta gamma p q a.
  exact (fmap_comp (cat_precomp _ (delta a))
    (natmod_component alpha beta p a)
    (natmod_component beta gamma q a)).
Defined.

(** The following section states the three hard inputs in full.  The
    constructor following them verifies that nothing else is needed
    for the outer 1-category structure. *)
Section Fun02CoherenceSkeleton.

  Context {A B : Type} `{IsGraph A} `{Is21Cat B}.

  Context
    (natmod_assoc : forall {F G K L : Fun02 A B}
      (alpha : F $-> G) (beta : G $-> K) (gamma : K $-> L),
      ((gamma $o beta) $o alpha)
        $-> (gamma $o (beta $o alpha)))
    (natmod_idl : forall {F G : Fun02 A B} (alpha : F $-> G),
      (Id G $o alpha) $-> alpha)
    (natmod_idr : forall {F G : Fun02 A B} (alpha : F $-> G),
      (alpha $o Id F) $-> alpha).

  Definition is1cat_fun02_from_coherence
    : Is1Cat (Fun02 A B).
  Proof.
    snapply Build_Is1Cat'.
    { intros F G.
      exact (is01cat_hom_fun02 F G). }
    { intros F G.
      exact (is0gpd_hom_fun02 F G). }
    { intros F G K delta.
      exact (is0functor_postcomp_fun02 F G K delta). }
    { intros F G K delta.
      exact (is0functor_precomp_fun02 F G K delta). }
    { intros F G K L alpha beta gamma.
      exact (natmod_assoc F G K L alpha beta gamma). }
    { intros F G alpha.
      exact (natmod_idl F G alpha). }
    intros F G alpha.
    exact (natmod_idr F G alpha).
  Defined.

End Fun02CoherenceSkeleton.

(** The two unit fields below currently depend on the corresponding
    TODOs in [Cylinder.v]. *)
Instance is1cat_fun02
  (A B : Type) `{IsGraph A} `{Is21Cat B}
  : Is1Cat (Fun02 A B).
Proof.
  napply is1cat_fun02_from_coherence.
  - intros F G K L alpha beta gamma.
    exact (natmod_assoc_from_cylinder alpha beta gamma).
  - intros F G alpha.
    exact (natmod_idl_from_cylinder alpha).
  - intros F G alpha.
    exact (natmod_idr_from_cylinder alpha).
Defined.

Instance hasequivs_fun02
  (A B : Type) `{IsGraph A} `{Is21Cat B}
  : HasEquivs (Fun02 A B)
  := cat_hasequivs (Fun02 A B).

(** All remaining coherences are checked pointwise in the codomain. *)
Instance is21cat_fun02
  (A B : Type) `{IsGraph A} `{Is21Cat B}
  : Is21Cat (Fun02 A B).
Proof.
  snapply Build_Is21Cat.
  - intros F G.
    exact (is1cat_hom_fun02 F G).
  - intros F G.
    exact (is1gpd_hom_fun02 F G).
  - intros F G K beta.
    exact (is1functor_postcomp_fun02 F G K beta).
  - intros F G K alpha.
    exact (is1functor_precomp_fun02 F G K alpha).
  - intros F G K alpha alpha' beta beta' p q a.
    exact (bifunctor_coh_comp
      (natmod_component alpha alpha' p a)
      (natmod_component beta beta' q a)).
  - intros F G K L alpha beta.
    snapply Build_Is1Natural.
    intros gamma gamma' p a.
    exact (isnat
      (alnat := is1natural_cat_assoc_l
        (F a) (G a) (K a) (L a) (alpha a) (beta a))
      (fun k => cat_assoc (alpha a) (beta a) k)
      (natmod_component gamma gamma' p a)).
  - intros F G K L alpha gamma.
    snapply Build_Is1Natural.
    intros beta beta' p a.
    exact (isnat
      (alnat := is1natural_cat_assoc_m
        (F a) (G a) (K a) (L a) (alpha a) (gamma a))
      (fun k => cat_assoc (alpha a) k (gamma a))
      (natmod_component beta beta' p a)).
  - intros F G K L beta gamma.
    snapply Build_Is1Natural.
    intros alpha alpha' p a.
    exact (isnat
      (alnat := is1natural_cat_assoc_r
        (F a) (G a) (K a) (L a) (beta a) (gamma a))
      (fun k => cat_assoc k (beta a) (gamma a))
      (natmod_component alpha alpha' p a)).
  - intros F G.
    snapply Build_Is1Natural.
    intros alpha beta p a.
    exact (isnat
      (alnat := is1natural_cat_idl (F a) (G a))
      cat_idl
      (natmod_component alpha beta p a)).
  - intros F G.
    snapply Build_Is1Natural.
    intros alpha beta p a.
    exact (isnat
      (alnat := is1natural_cat_idr (F a) (G a))
      cat_idr
      (natmod_component alpha beta p a)).
  - intros F G K L alpha beta gamma a.
    reflexivity.
  - intros F G K L M alpha beta gamma delta a.
    exact (cat_pentagon
      (F a) (G a) (K a) (L a) (M a)
      (alpha a) (beta a) (gamma a) (delta a)).
  - intros F G K alpha beta a.
    exact (cat_tril
      (F a) (G a) (K a) (alpha a) (beta a)).
Defined.

(** Cylinders in a graph-indexed functor category are constructed
    pointwise. *)
Definition Build_Cylinder_fun02
  {A B : Type} `{IsGraph A} `{Is21Cat B}
  {F00 F20 F02 F22 : Fun02 A B}
  {f : F00 $-> F20} {g : F02 $-> F22}
  {u0 u1 : F00 $-> F02} {v0 v1 : F20 $-> F22}
  {p : u0 $== u1} {q : v0 $== v1}
  {s0 : Square u0 v0 f g} {s1 : Square u1 v1 f g}
  (c : forall a,
    Cylinder
      (natmod_component u0 u1 p a)
      (natmod_component v0 v1 q a)
      (natmod_component (v0 $o f) (g $o u0) s0 a)
      (natmod_component (v1 $o f) (g $o u1) s1 a))
  : Cylinder p q s0 s1.
Proof.
  intro a.
  exact (c a).
Defined.

(** ** The inherited lower structure of [Fun12] *)

Instance isgraph_fun12
  {A B : Type} `{Is1Cat A} `{Is1Cat B}
  : IsGraph (Fun12 A B)
  := isgraph_induced fun02_fun12.

Instance is01cat_fun12
  {A B : Type} `{Is1Cat A} `{Is1Cat B}
  : Is01Cat (Fun12 A B)
  := is01cat_induced fun02_fun12.

Instance is2graph_fun12
  {A B : Type} `{Is1Cat A} `{Is21Cat B}
  : Is2Graph (Fun12 A B)
  := is2graph_induced fun02_fun12.

Instance is3graph_fun12
  {A B : Type} `{Is1Cat A} `{Is21Cat B}
  : Is3Graph (Fun12 A B)
  := is3graph_induced fun02_fun12.

Instance is1cat_fun12
  {A B : Type} `{Is1Cat A} `{Is21Cat B}
  : Is1Cat (Fun12 A B)
  := is1cat_induced fun02_fun12.

Instance is21cat_fun12
  {A B : Type} `{Is1Cat A} `{Is21Cat B}
  : Is21Cat (Fun12 A B)
  := is21cat_induced fun02_fun12.

(** ** Composition of coherent graph-indexed functors *)

Definition fun02_compose
  {A B C : Type} `{IsGraph A, IsGraph B, IsGraph C}
  : Fun02 B C -> Fun02 A B -> Fun02 A C
  := fun G F => Build_Fun02 (G o F).

Definition fun02_postcomp
  {A B C : Type} `{IsGraph A, Is1Cat B, Is1Cat C}
  (F : Fun12 B C)
  : Fun02 A B -> Fun02 A C
  := fun02_compose (A := A) (fun02_fun12 F).

Instance is0functor_fun02_postcomp
  {A B C : Type} `{IsGraph A, Is1Cat B, Is1Cat C}
  (F : Fun12 B C)
  : Is0Functor (fun02_postcomp (A := A) F).
Proof.
  snapply Build_Is0Functor.
  intros X Y alpha.
  exact (nattrans_postwhisker F alpha).
Defined.

Definition fun02_fun02_postcomp
  {A B C : Type} `{IsGraph A, Is1Cat B, Is1Cat C}
  (F : Fun12 B C)
  : Fun02 (Fun02 A B) (Fun02 A C)
  := Build_Fun02 (fun02_postcomp (A := A) F).

Definition natmod_fun02_postcomp
  {A B C : Type} `{IsGraph A, Is21Cat B, Is21Cat C}
  (F : Fun22 B C)
  {X Y : Fun02 A B} {alpha beta : X $-> Y}
  (p : alpha $== beta)
  : NatModification
      (nattrans_postwhisker (fun12_fun22 F) alpha)
      (nattrans_postwhisker (fun12_fun22 F) beta).
Proof.
  snapply Build_NatModification.
  { exact (fun a => fmap2 F (natmod_component alpha beta p a)). }
  intros a b f.
  exact (fmap_cylinder F (natmod_isnatural alpha beta p f)).
Defined.

Definition fmap_vrefl
  {A B : Type} `{Is21Cat A, Is21Cat B}
  (F : Fun22 A B) {a b : A} (f : a $-> b)
  : fmap2 F (vrefl f)
    $== fmap2 F (cat_idl f) $@ (fmap2 F (cat_idr f))^$.
Proof.
  unfold vrefl.
  lhs' exact (fmap_comp (@fmap _ _ _ _ F _ a b)
    (cat_idl f) (cat_idr f)^$).
  exact (gpd_1functor_V (@fmap _ _ _ _ F _ a b) (cat_idr f)
    $@R fmap2 F (cat_idl f)).
Defined.

Local Definition fmap_idl_cancel
  {A B : Type} `{Is21Cat A, Is21Cat B}
  (F : Fun22 A B) {a b : A} (f : a $-> b)
  : (fmap_comp F f (Id b))^$ $@ fmap2 F (cat_idl f)
    $== (fmap_id F b $@R fmap F f) $@
      cat_idl (fmap F f).
Proof.
  rapply gpd_moveR_hV.
  exact (fmap_idl (F := F) f $@
    cat_assoc_opp
      (fmap_comp F f (Id b))
      (fmap_id F b $@R fmap F f)
      (cat_idl (fmap F f))).
Defined.

Local Definition fmap_idr_cancel
  {A B : Type} `{Is21Cat A, Is21Cat B}
  (F : Fun22 A B) {a b : A} (f : a $-> b)
  : (fmap2 F (cat_idr f))^$ $@
      fmap_comp F (Id a) f $@
      (fmap F f $@L fmap_id F a)
    $== (cat_idr (fmap F f))^$.
Proof.
  lhs' exact (cat_assoc_opp
    (fmap2 F (cat_idr f))^$
    (fmap_comp F (Id a) f)
    (fmap F f $@L fmap_id F a)).
  rapply gpd_moveR_hV.
  rapply gpd_moveL_Vh.
  exact (fmap_idr (F := F) f)^$.
Defined.

Definition fmap_id_cylinder
  {A B : Type} `{Is21Cat A, Is21Cat B}
  (F : Fun22 A B) {a b : A} (f : a $-> b)
  : Cylinder
      (fmap_id F a) (fmap_id F b)
      ((fmap_comp F f (Id b))^$
        $@ fmap2 F (vrefl f)
        $@ fmap_comp F (Id a) f)
      (vrefl (fmap F f)).
Proof.
  napply Build_Cylinder.
  unfold vrefl.
  lhs' exact (cat_assoc_opp
    ((fmap_comp F f (Id b))^$ $@ fmap2 F
      (cat_idl f $@ (cat_idr f)^$))
    (fmap_comp F (Id a) f)
    (fmap F f $@L fmap_id F a)).
  lhs' exact (cat_assoc_opp
    (fmap_comp F f (Id b))^$
    (fmap2 F (cat_idl f $@ (cat_idr f)^$))
    (fmap_comp F (Id a) f $@
      (fmap F f $@L fmap_id F a))).
  lhs' exact (((fmap_comp F (Id a) f $@
      (fmap F f $@L fmap_id F a)) $@L fmap_vrefl F f)
    $@R (fmap_comp F f (Id b))^$).
  lhs' exact (cat_assoc_opp
    (fmap2 F (cat_idl f))
    (fmap2 F (cat_idr f))^$
    (fmap_comp F (Id a) f $@
      (fmap F f $@L fmap_id F a))
    $@R (fmap_comp F f (Id b))^$).
  lhs' exact (cat_assoc
    (fmap_comp F f (Id b))^$
    (fmap2 F (cat_idl f))
    ((fmap2 F (cat_idr f))^$ $@
      (fmap_comp F (Id a) f $@
        (fmap F f $@L fmap_id F a)))).
  lhs' exact (cat_assoc
    (fmap2 F (cat_idr f))^$
    (fmap_comp F (Id a) f)
    (fmap F f $@L fmap_id F a)
    $@R ((fmap_comp F f (Id b))^$ $@
      fmap2 F (cat_idl f))).
  lhs' exact (fmap_idl_cancel F f $@@ fmap_idr_cancel F f).
  exact (cat_assoc_opp
    (fmap_id F b $@R fmap F f)
    (cat_idl (fmap F f))
    (cat_idr (fmap F f))^$).
Defined.

Definition natmod_fun02_postcomp_id
  {A B C : Type} `{IsGraph A, Is21Cat B, Is21Cat C}
  (F : Fun22 B C) (X : Fun02 A B)
  : NatModification
      (nattrans_postwhisker (fun12_fun22 F) (nattrans_id X))
      (nattrans_id (fun02_postcomp (A := A) (fun12_fun22 F) X)).
Proof.
  snapply Build_NatModification.
  { exact (fun a => fmap_id F (X a)). }
  intros a b f.
  unfold nattrans_postwhisker, trans_postwhisker.
  cbn beta.
  nrefine (fmap_id_cylinder F (fmap X f)).
Defined.

Definition fmap_assoc_opp
  {A B : Type} `{Is21Cat A, Is21Cat B}
  (F : Fun22 A B)
  {a b c d : A} (f : a $-> b) (g : b $-> c) (h : c $-> d)
  : fmap2 F (cat_assoc_opp f g h)
      $@ fmap_comp F f (h $o g)
      $@ (fmap_comp F g h $@R fmap F f)
      $@ cat_assoc (fmap F f) (fmap F g) (fmap F h)
    $== fmap_comp F (g $o f) h
      $@ (fmap F h $@L fmap_comp F f g).
Proof.
  lhs' exact (cat_assoc (fmap F f) (fmap F g) (fmap F h)
    $@L cat_assoc_opp
      (fmap2 F (cat_assoc_opp f g h))
      (fmap_comp F f (h $o g))
      (fmap_comp F g h $@R fmap F f)).
  lhs' exact (cat_assoc_opp
    (fmap2 F (cat_assoc_opp f g h))
    (fmap_comp F f (h $o g)
      $@ (fmap_comp F g h $@R fmap F f))
    (cat_assoc (fmap F f) (fmap F g) (fmap F h))).
  lhs' exact ((fmap_comp F f (h $o g)
      $@ (fmap_comp F g h $@R fmap F f)
      $@ cat_assoc (fmap F f) (fmap F g) (fmap F h))
    $@L fmap3 F (cat_assoc_opp_is_rev a b c d f g h)).
  lhs' exact ((fmap_comp F f (h $o g)
      $@ (fmap_comp F g h $@R fmap F f)
      $@ cat_assoc (fmap F f) (fmap F g) (fmap F h))
    $@L gpd_1functor_V
      (@fmap _ _ _ _ F _ a d) (cat_assoc f g h)).
  lhs' exact ((fmap_assoc (F := F) f g h)^$
    $@R (fmap2 F (cat_assoc f g h))^$).
  lhs' exact (cat_assoc_opp
    (fmap2 F (cat_assoc f g h))
    (fmap_comp F (g $o f) h)
    (fmap F h $@L fmap_comp F f g)
    $@R (fmap2 F (cat_assoc f g h))^$).
  exact (gpd_hh_V
    (fmap_comp F (g $o f) h
      $@ (fmap F h $@L fmap_comp F f g))
    (fmap2 F (cat_assoc f g h))).
Defined.

Definition fmap_assoc_pasting
  {A B : Type} `{Is21Cat A, Is21Cat B}
  (F : Fun22 A B)
  {a b c d : A} (f : a $-> b) (g : b $-> c) (h : c $-> d)
  : (fmap_comp F f (h $o g))^$
      $@ fmap2 F (cat_assoc f g h)
    $== (fmap_comp F g h $@R fmap F f)
      $@ cat_assoc (fmap F f) (fmap F g) (fmap F h)
      $@ (fmap F h $@L fmap_comp F f g)^$
      $@ (fmap_comp F (g $o f) h)^$.
Proof.
  rapply gpd_moveL_Vh.
  rapply gpd_moveL_Vh.
  lhs' exact ((fmap F h $@L fmap_comp F f g)
    $@L cat_assoc_opp
      (fmap_comp F f (h $o g))^$
      (fmap2 F (cat_assoc f g h))
      (fmap_comp F (g $o f) h)).
  lhs' exact (cat_assoc_opp
    (fmap_comp F f (h $o g))^$
    (fmap2 F (cat_assoc f g h)
      $@ fmap_comp F (g $o f) h)
    (fmap F h $@L fmap_comp F f g)).
  lhs' exact (fmap_assoc (F := F) f g h
    $@R (fmap_comp F f (h $o g))^$).
  lhs' exact (cat_assoc
    (fmap_comp F f (h $o g))^$
    (fmap_comp F f (h $o g)
      $@ (fmap_comp F g h $@R fmap F f))
    (cat_assoc (fmap F f) (fmap F g) (fmap F h))).
  lhs' exact (cat_assoc (fmap F f) (fmap F g) (fmap F h)
    $@L cat_assoc
      (fmap_comp F f (h $o g))^$
      (fmap_comp F f (h $o g))
      (fmap_comp F g h $@R fmap F f)).
  lhs' exact (cat_assoc (fmap F f) (fmap F g) (fmap F h)
    $@L ((fmap_comp F g h $@R fmap F f)
      $@L gpd_isretr (fmap_comp F f (h $o g)))).
  exact (cat_assoc (fmap F f) (fmap F g) (fmap F h)
    $@L cat_idr (fmap_comp F g h $@R fmap F f)).
Defined.

Definition fmap2_postwhisker_pasting
  {A B : Type} `{Is21Cat A, Is21Cat B}
  (F : Fun22 A B)
  {a b c : A} {f f' : a $-> b} (p : f $== f') (g : b $-> c)
  : (fmap_comp F f g)^$ $@ fmap2 F (g $@L p)
    $== (fmap F g $@L fmap2 F p) $@ (fmap_comp F f' g)^$.
Proof.
  rapply gpd_moveL_Vh.
  lhs' exact (cat_assoc_opp
    (fmap_comp F f g)^$
    (fmap2 F (g $@L p))
    (fmap_comp F f' g)).
  lhs' exact ((fmap2_postwhisker F p g)^$
    $@R (fmap_comp F f g)^$).
  exact (gpd_hh_V
    (fmap F g $@L fmap2 F p)
    (fmap_comp F f g)).
Defined.

Definition fmap2_prewhisker_pasting
  {A B : Type} `{Is21Cat A, Is21Cat B}
  (F : Fun22 A B)
  {a b c : A} (f : a $-> b) {g g' : b $-> c} (q : g $== g')
  : (fmap_comp F f g)^$ $@ fmap2 F (q $@R f)
    $== (fmap2 F q $@R fmap F f) $@ (fmap_comp F f g')^$.
Proof.
  rapply gpd_moveL_Vh.
  lhs' exact (cat_assoc_opp
    (fmap_comp F f g)^$
    (fmap2 F (q $@R f))
    (fmap_comp F f g')).
  lhs' exact ((fmap2_prewhisker F f q)^$
    $@R (fmap_comp F f g)^$).
  exact (gpd_hh_V
    (fmap2 F q $@R fmap F f)
    (fmap_comp F f g)).
Defined.

Definition fmap_assoc_opp_pasting
  {A B : Type} `{Is21Cat A, Is21Cat B}
  (F : Fun22 A B)
  {a b c d : A} (f : a $-> b) (g : b $-> c) (h : c $-> d)
  : (fmap_comp F (g $o f) h)^$
      $@ fmap2 F (cat_assoc_opp f g h)
    $== (fmap F h $@L fmap_comp F f g)
      $@ (cat_assoc (fmap F f) (fmap F g) (fmap F h))^$
      $@ (fmap_comp F g h $@R fmap F f)^$
      $@ (fmap_comp F f (h $o g))^$.
Proof.
  rapply gpd_moveL_Vh.
  rapply gpd_moveL_Vh.
  rapply gpd_moveL_Vh.
  lhs' exact (cat_assoc (fmap F f) (fmap F g) (fmap F h)
    $@L ((fmap_comp F g h $@R fmap F f)
      $@L cat_assoc_opp
        (fmap_comp F (g $o f) h)^$
        (fmap2 F (cat_assoc_opp f g h))
        (fmap_comp F f (h $o g)))).
  lhs' exact (cat_assoc (fmap F f) (fmap F g) (fmap F h)
    $@L cat_assoc_opp
      (fmap_comp F (g $o f) h)^$
      (fmap2 F (cat_assoc_opp f g h)
        $@ fmap_comp F f (h $o g))
      (fmap_comp F g h $@R fmap F f)).
  lhs' exact (cat_assoc_opp
    (fmap_comp F (g $o f) h)^$
    (fmap2 F (cat_assoc_opp f g h)
      $@ fmap_comp F f (h $o g)
      $@ (fmap_comp F g h $@R fmap F f))
    (cat_assoc (fmap F f) (fmap F g) (fmap F h))).
  lhs' exact (fmap_assoc_opp F f g h
    $@R (fmap_comp F (g $o f) h)^$).
  exact (gpd_hh_V
    (fmap F h $@L fmap_comp F f g)
    (fmap_comp F (g $o f) h)).
Defined.

Definition fmap_vconcat_cylinder
  {A B : Type} `{Is21Cat A, Is21Cat B}
  (F : Fun22 A B)
  {x00 x20 x02 x22 x04 x24 : A}
  {f0 : x00 $-> x20} {f1 : x02 $-> x22} {f2 : x04 $-> x24}
  {u0 : x00 $-> x02} {v0 : x20 $-> x22}
  (s0 : Square u0 v0 f0 f1)
  {u1 : x02 $-> x04} {v1 : x22 $-> x24}
  (s1 : Square u1 v1 f1 f2)
  : Cylinder
      (fmap_comp F u0 u1) (fmap_comp F v0 v1)
      (fmap_square F (s0 $@v s1))
      (fmap_square F s0 $@v fmap_square F s1).
Proof.
  napply Build_Cylinder.
  unfold fmap_square, vconcat.
  lhs' exact (cat_assoc_opp
    ((fmap_comp F f0 (v1 $o v0))^$ $@
      fmap2 F
        ((cat_assoc f0 v0 v1 $@ (v1 $@L s0)) $@
          ((cat_assoc_opp u0 f1 v1 $@ (s1 $@R u0)) $@
            cat_assoc u0 u1 f2)))
    (fmap_comp F (u1 $o u0) f2)
    (fmap F f2 $@L fmap_comp F u0 u1)).
  lhs' napply (fun h =>
    (fmap_comp F (u1 $o u0) f2
      $@ (fmap F f2 $@L fmap_comp F u0 u1))
    $@L (h $@R (fmap_comp F f0 (v1 $o v0))^$)).
  { exact (fmap_vconcat_composite
      (@fmap _ _ _ _ F _ x00 x24)
      (cat_assoc f0 v0 v1) (v1 $@L s0)
      (cat_assoc_opp u0 f1 v1) (s1 $@R u0)
      (cat_assoc u0 u1 f2)). }
  lhs' exact (cat_assoc _ _ _).
  lhs' exact (_ $@L (_ $@L cat_assoc _ _ _)).
  lhs' exact (_ $@L (_ $@L (_ $@L cat_assoc _ _ _))).
  lhs' exact (_ $@L (_ $@L cat_assoc _ _ _)).
  lhs' exact (_ $@L (_ $@L (_ $@L cat_assoc _ _ _))).
  lhs' exact (_ $@L (_ $@L (_ $@L (_ $@L (_ $@L (_ $@L
    fmap_assoc_pasting F f0 v0 v1)))))).
  lhs' exact (_ $@L (_ $@L (_ $@L (_ $@L (_ $@L
    cat_assoc_opp _ _ _))))).
  lhs' exact (_ $@L (_ $@L (_ $@L (_ $@L (_ $@L
    (fmap2_postwhisker_pasting F s0 v1 $@R _)))))).
  lhs' exact (_ $@L (_ $@L (_ $@L (_ $@L (_ $@L
    cat_assoc _ _ _))))).
  lhs' exact (_ $@L (_ $@L (_ $@L (_ $@L
    cat_assoc_opp _ _ _)))).
  lhs' exact (_ $@L (_ $@L (_ $@L (_ $@L
    (fmap_assoc_opp_pasting F u0 f1 v1 $@R _))))).
  lhs' exact (_ $@L (_ $@L (_ $@L (_ $@L
    cat_assoc _ _ _)))).
  lhs' exact (_ $@L (_ $@L (_ $@L
    cat_assoc_opp _ _ _))).
  lhs' exact (_ $@L (_ $@L (_ $@L
    (fmap2_prewhisker_pasting F u0 s1 $@R _)))).
  lhs' exact (_ $@L (_ $@L (_ $@L
    cat_assoc _ _ _))).
  lhs' exact (_ $@L (_ $@L
    cat_assoc_opp _ _ _)).
  lhs' exact (_ $@L (_ $@L
    (fmap_assoc_pasting F u0 u1 f2 $@R _))).
  lhs' exact (_ $@L (_ $@L cat_assoc _ _ _)).
  lhs' exact (_ $@L (_ $@L (_ $@L cat_assoc _ _ _))).
  lhs' exact (_ $@L (_ $@L (_ $@L (_ $@L cat_assoc _ _ _)))).
  lhs' exact (_ $@L gpd_h_Vh _ _).
  lhs' exact (gpd_h_Vh _ _).
  lhs' exact (_ $@L (_ $@L (_ $@L cat_assoc _ _ _))).
  lhs' exact (_ $@L (_ $@L (_ $@L (_ $@L cat_assoc _ _ _)))).
  lhs' exact (_ $@L (_ $@L (_ $@L (_ $@L
    ((cat_assoc_opp_is_rev _ _ _ _
      (fmap F u0) (fmap F f1) (fmap F v1))^$ $@R _))))).
  rhs' exact (cat_assoc _ _ _).
  rhs' exact (_ $@L cat_assoc _ _ _).
  rhs' exact (cat_assoc _ _ _).
  rhs' exact (_ $@L cat_assoc _ _ _).
  rhs' exact (_ $@L (_ $@L (_ $@L
    (fmap_Vpp (cat_postcomp _ (fmap F v1))
      (fmap_comp F f0 v0) (fmap2 F s0) (fmap_comp F u0 f1)
      $@R _)))).
  rhs' exact (_ $@L (_ $@L (_ $@L cat_assoc _ _ _))).
  rhs' exact (_ $@L (_ $@L (_ $@L (_ $@L cat_assoc _ _ _)))).
  rhs' exact (_ $@L
    (fmap_Vpp (cat_precomp _ (fmap F u0))
      (fmap_comp F f1 v1) (fmap2 F s1) (fmap_comp F u1 f2)
      $@R _)).
  rhs' exact (_ $@L cat_assoc _ _ _).
  rhs' exact (_ $@L (_ $@L cat_assoc _ _ _)).
  exact (Id _).
Defined.

Definition natmod_fun02_postcomp_comp
  {A B C : Type} `{IsGraph A, Is21Cat B, Is21Cat C}
  (F : Fun22 B C)
  {X Y Z : Fun02 A B} (alpha : X $-> Y) (beta : Y $-> Z)
  : NatModification
      (nattrans_postwhisker (fun12_fun22 F)
        (nattrans_comp beta alpha))
      (nattrans_comp
        (nattrans_postwhisker (fun12_fun22 F) beta)
        (nattrans_postwhisker (fun12_fun22 F) alpha)).
Proof.
  snapply Build_NatModification.
  { exact (fun a => fmap_comp F (alpha a) (beta a)). }
  intros a b f.
  unfold nattrans_postwhisker, trans_postwhisker.
  cbn beta.
  nrefine (fmap_vconcat_cylinder F (isnat alpha f) (isnat beta f)).
Defined.

Global Instance is1functor_fun02_postcomp
  {A B C : Type} `{IsGraph A, Is21Cat B, Is21Cat C}
  (F : Fun22 B C)
  : Is1Functor (fun02_postcomp (A := A) (fun12_fun22 F)).
Proof.
  snapply Build_Is1Functor.
  { intros X Y alpha beta p.
    exact (natmod_fun02_postcomp F p). }
  { intro X.
    exact (natmod_fun02_postcomp_id F X). }
  intros X Y Z alpha beta.
  exact (natmod_fun02_postcomp_comp F alpha beta).
Defined.

Definition fun12_fun02_postcomp
  {A B C : Type} `{IsGraph A, Is21Cat B, Is21Cat C}
  (F : Fun22 B C)
  : Fun12 (Fun02 A B) (Fun02 A C)
  := Build_Fun12 (fun02_postcomp (A := A) (fun12_fun22 F)).

Definition nattrans_fun02_postcomp_cubical12
  {A B C : Type} `{IsGraph A, Is21Cat B, Is21Cat C}
  (F G : Fun12 B C)
  (alpha : CubicalNatTrans12 F G)
  : NatTrans
      (fun02_postcomp (A := A) F)
      (fun02_postcomp (A := A) G).
Proof.
  snapply Build_NatTrans.
  - intro X.
    exact (nattrans_prewhisker alpha X).
  - snapply Build_Is1Natural.
    intros X Y theta.
    snapply Build_NatModification.
    { exact (fun a => isnat alpha (theta a)). }
    intros a b f.
    unfold nattrans_prewhisker, trans_prewhisker.
    unfold nattrans_postwhisker, trans_postwhisker.
    unfold is1natural_comp, is1natural_prewhisker.
    unfold is1natural_postwhisker.
    cbn.
    exact (cubical12_naturality alpha (isnat theta f)).
Defined.

Definition fun12_compose
  {A B C : Type} `{Is1Cat A, Is1Cat B, Is1Cat C}
  : Fun12 B C -> Fun12 A B -> Fun12 A C.
Proof.
  intros F G.
  napply Build_Fun12.
  exact (is1functor_compose G F).
Defined.

Definition fun12_id
  {A : Type} `{Is1Cat A}
  : Fun12 A A
  := Build_Fun12 idmap.

Definition fmap_square_compose
  {A B C : Type} `{Is21Cat A, Is21Cat B, Is21Cat C}
  (F : Fun22 A B) (G : Fun22 B C)
  {x00 x20 x02 x22 : A}
  {f : x00 $-> x20} {g : x02 $-> x22}
  {u : x00 $-> x02} {v : x20 $-> x22}
  (s : Square u v f g)
  : fmap_square G (fmap_square F s)
    $== fmap_square
      (fun12_compose (fun12_fun22 G) (fun12_fun22 F)) s.
Proof.
  unfold fmap_square, fun12_compose.
  cbn.
  lhs' exact (fmap_comp G (fmap F u) (fmap F g) $@L
    (fmap_Vpp (@fmap _ _ _ _ G _ _ _)
      (fmap_comp F f v) (fmap2 F s) (fmap_comp F u g)
    $@R (fmap_comp G (fmap F f) (fmap F v))^$)).
  rhs' exact
    ((fmap2 G (fmap_comp F u g) $@
        fmap_comp G (fmap F u) (fmap F g)) $@L
      (fmap2 G (fmap2 F s) $@L
        gpd_rev_pp
          (fmap_comp G (fmap F f) (fmap F v))
          (fmap2 G (fmap_comp F f v)))).
  lhs' exact (fmap_comp G (fmap F u) (fmap F g) $@L
    cat_assoc
      (fmap_comp G (fmap F f) (fmap F v))^$
      ((fmap2 G (fmap_comp F f v))^$ $@ fmap2 G (fmap2 F s))
      (fmap2 G (fmap_comp F u g))).
  lhs' exact (fmap_comp G (fmap F u) (fmap F g) $@L
    (fmap2 G (fmap_comp F u g) $@L
      cat_assoc
        (fmap_comp G (fmap F f) (fmap F v))^$
        (fmap2 G (fmap_comp F f v))^$
        (fmap2 G (fmap2 F s)))).
  exact (cat_assoc_opp _ _ _).
Defined.

Definition fmap_square_id
  {A : Type} `{Is21Cat A}
  {x00 x20 x02 x22 : A}
  {f : x00 $-> x20} {g : x02 $-> x22}
  {u : x00 $-> x02} {v : x20 $-> x22}
  (s : Square u v f g)
  : fmap_square (@fun12_id A _ _ _ _) s $== s.
Proof.
  unfold fmap_square, fun12_id.
  cbn.
  lhs' exact (Id _ $@L (s $@L gpd_rev_1)).
  lhs' exact (Id _ $@L cat_idr s).
  exact (cat_idl s).
Defined.
