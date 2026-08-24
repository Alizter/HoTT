Require Import Basics.Utf8 Basics.Overture Basics.Tactics Basics.Equivalences.
Require Import WildCat.Core.
Require Import WildCat.NatTrans.
Require Import WildCat.Equiv.
Require Import WildCat.EquivGpd.
Require Import WildCat.Prod.
Require Import WildCat.Opposite.
Require Import WildCat.Yoneda WildCat.ZeroGroupoid.
Require Import WildCat.FunctorCat.
Require Import WildCat.Universe.
Require Import WildCat.Cylinder WildCat.Square WildCat.TwoFunctor
  WildCat.TwoOneCat.
Require Import Types.Prod.

Generalizable Variables C D F G.

(** ** Notions of adjunctions in wild categories. *)

(** We try to capture a wild notion of (oo,1)-adjunctions since these are the ones that commonly appear in practice. Special cases include the standard 1-categorical adjunction.

There are notions of 2-adjunction/biadjunction/higher adjunction but it is not clear if this generality is useful.

We will define an adjunction to be an equivalence (in Type) between corresponding hom-types. This is a more immediately useful definition than others we can consider.

We should also be able to define "F having a left adjoint" as the initial object of a slice category C / F. However this seems like too much work for now, and it is not immediately obvious how it ties back to the adjunction isomorphism.

In the future, it ought to be possible to generalize this definition to live inside a given bicategory, however due to current structural issues in the WildCat library, writing down a usable definition of bicategory requires a lot of effort.
*)

(** * Definition of adjunction *)

(** ** Definition of adjunction *)

Record Adjunction {C D : Type} (F : C -> D) (G : D -> C)
  `{Is1Cat C, Is1Cat D, !Is0Functor F, !Is0Functor G} :=
{
  equiv_adjunction (x : C) (y : D) : (F x $-> y) <~> (x $-> G y) ;
  (** Naturality condition in both variables separately. *)
  (** The left variable is a bit trickier to state since we have opposite categories involved. *)
  is1natural_equiv_adjunction_l (y : D)
    :: Is1Natural (A := C^op) (yon y o F)
        (** We have to explicitly give a witness to the functoriality of [yon y o F]. *)
        (is0functor_F := is0functor_compose (A:=C^op) (B:=D^op) (C:=Type) _ _)
        (yon (G y)) (fun x => equiv_adjunction x y) ;
  (** Naturality in the right variable *)
  is1natural_equiv_adjunction_r (x : C)
    :: Is1Natural (opyon (F x)) (opyon x o G) (equiv_adjunction x) ;
}.

Arguments equiv_adjunction {C D F G
  isgraph_C is2graph_C is01cat_C is1cat_C
  isgraph_D is2graph_D is01cat_D is1cat_D
  is0functor_F is0functor_G} adj x y : rename.
Arguments is1natural_equiv_adjunction_l {C D F G
  isgraph_C is2graph_C is01cat_C is1cat_C
  isgraph_D is2graph_D is01cat_D is1cat_D
  is0functor_F is0functor_G} adj y : rename.
Arguments is1natural_equiv_adjunction_r {C D F G
  isgraph_C is2graph_C is01cat_C is1cat_C
  isgraph_D is2graph_D is01cat_D is1cat_D
  is0functor_F is0functor_G} adj x : rename.

Notation "F ⊣ G" := (Adjunction F G).

(** ** Adjunctions enriched in 0-groupoids *)

(** This form retains homotopies between morphisms and does not require
    morphism extensionality. *)
Record GpdAdjunction {A B : Type} (F : A -> B) (G : B -> A)
  `{Is1Cat A, Is1Cat B, !Is0Functor F, !Is0Functor G} := {
  equiv_gpd_adjunction (x : A) (y : B)
    : opyon_0gpd (F x) y $<~> opyon_0gpd x (G y);
  is1natural_equiv_gpd_adjunction_l (y : B)
    :: Is1Natural (A := A^op)
         (isgraph_A := isgraph_op)
         (is0functor_F := is0functor_compose
           (A := A^op) (B := B^op) (C := ZeroGpd)
           F (yon_0gpd y))
         (is0functor_G := is0functor_yon_0gpd (G y))
         (yon_0gpd y o F) (yon_0gpd (G y))
         (fun x => cate_fun (equiv_gpd_adjunction x y));
  is1natural_equiv_gpd_adjunction_r (x : A)
    :: Is1Natural
         (is0functor_F := is0functor_opyon_0gpd (F x))
         (is0functor_G := is0functor_compose
           (A := B) (B := A) (C := ZeroGpd)
           G (opyon_0gpd x))
         (opyon_0gpd (F x)) (opyon_0gpd x o G)
         (fun y => cate_fun (equiv_gpd_adjunction x y));
}.

Section BuildGpdAdjunction.
  Context {A B : Type} (F : A -> B) (G : B -> A)
    `{Is1Cat A, Is1Cat B,
      !Is0Functor F, !Is1Functor F,
      !Is0Functor G, !Is1Functor G}
    (epsilon : NatTrans (F o G) idmap)
    (eta : NatTrans idmap (G o F))
    (triangle1 : Transformation
      (nattrans_comp
        (nattrans_prewhisker epsilon F)
        (nattrans_postwhisker F eta))
      (nattrans_id F))
    (triangle2 : Transformation
      (nattrans_comp
        (nattrans_postwhisker G epsilon)
        (nattrans_prewhisker eta G))
      (nattrans_id G)).

  Local Definition gpd_adjunction_hom (x : A) (y : B)
    : opyon_0gpd (F x) y $<~> opyon_0gpd x (G y).
  Proof.
    snapply cate_adjointify.
    - snapply Build_Fun01'.
      + exact (fun f => fmap G f $o eta x).
      + intros f g p.
        exact (fmap2 G p $@R eta x).
    - snapply Build_Fun01'.
      + exact (fun g => epsilon y $o fmap F g).
      + intros f g p.
        exact (epsilon y $@L fmap2 F p).
    - intro f.
      lhs' exact (fmap_comp G _ _ $@R _).
      lhs' exact (cat_assoc _ _ _).
      lhs' exact (_ $@L (isnat eta f)^$).
      lhs' exact (cat_assoc_opp _ _ _).
      lhs' exact (triangle2 y $@R _).
      exact (cat_idl _).
    - intro g.
      lhs' exact (_ $@L fmap_comp F _ _).
      lhs' exact (cat_assoc_opp _ _ _).
      lhs' exact (isnat epsilon g $@R _).
      lhs' exact (cat_assoc _ _ _).
      lhs' exact (_ $@L triangle1 x).
      exact (cat_idr _).
  Defined.

  Local Instance is1natural_gpd_adjunction_hom_l
    : forall y : B, Is1Natural (A := A^op)
        (isgraph_A := isgraph_op)
        (is0functor_F := is0functor_compose
          (A := A^op) (B := B^op) (C := ZeroGpd)
          F (yon_0gpd y))
        (is0functor_G := is0functor_yon_0gpd (G y))
        (yon_0gpd y o F) (yon_0gpd (G y))
        (fun x => cate_fun (gpd_adjunction_hom x y)).
  Proof.
    intro y.
    snapply Build_Is1Natural.
    intros x' x f h.
    unfold op in x', x, f.
    cbn.
    refine ((fmap_comp G _ _ $@R _) $@ _).
    refine (cat_assoc _ _ _ $@ _).
    pose (p := isnat_tr (alnat := is1natural_nattrans eta)
      (a := x) (a' := x') eta f).
    refine ((_ $@L p) $@ _).
    exact (cat_assoc_opp _ _ _).
  Defined.

  Local Instance is1natural_gpd_adjunction_hom_r
    : forall x : A, Is1Natural
        (is0functor_F := is0functor_opyon_0gpd (F x))
        (is0functor_G := is0functor_compose
          (A := B) (B := A) (C := ZeroGpd)
          G (opyon_0gpd x))
        (opyon_0gpd (F x)) (opyon_0gpd x o G)
        (fun y => cate_fun (gpd_adjunction_hom x y)).
  Proof.
    intro x.
    snapply Build_Is1Natural.
    intros y y' g h.
    cbn.
    refine ((fmap_comp G _ _ $@R _) $@ _).
    exact (cat_assoc _ _ _).
  Defined.

  Definition Build_GpdAdjunction_unit_counit
    : GpdAdjunction F G.
  Proof.
    snapply Build_GpdAdjunction.
    - exact gpd_adjunction_hom.
    - exact is1natural_gpd_adjunction_hom_l.
    - exact is1natural_gpd_adjunction_hom_r.
  Defined.
End BuildGpdAdjunction.

(** A coherent adjunction whose adjoints only act through 2-cells.  The
    cubical naturality of the unit and counit records the selected 3-cells
    needed by coherent diagram arguments, without requiring either adjoint to
    act on every 3-cell in its source. *)
Record CubicalAdjunction12
  {A B : Type} `{Is21Cat A, Is21Cat B}
  (F : Fun12 A B) (G : Fun12 B A) := {
  cubical12_adjunction_counit
    : CubicalNatTrans12
        (fun12_compose F G)
        fun12_id;
  cubical12_adjunction_unit
    : CubicalNatTrans12
        fun12_id
        (fun12_compose G F);
  cubical12_adjunction_triangle_l
    : NatModification
        (nattrans_comp
          (nattrans_prewhisker cubical12_adjunction_counit F)
          (nattrans_postwhisker F cubical12_adjunction_unit))
        (nattrans_id F);
  cubical12_adjunction_triangle_r
    : NatModification
        (nattrans_comp
          (nattrans_postwhisker G cubical12_adjunction_counit)
          (nattrans_prewhisker cubical12_adjunction_unit G))
        (nattrans_id G);
}.

Definition gpd_adjunction_cubical12
  {A B : Type} `{Is21Cat A, Is21Cat B}
  (F : Fun12 A B) (G : Fun12 B A)
  (adj : CubicalAdjunction12 F G)
  : GpdAdjunction F G.
Proof.
  napply (Build_GpdAdjunction_unit_counit F G
    (cubical12_adjunction_counit F G adj)
    (cubical12_adjunction_unit F G adj)).
  - intro a.
    exact (natmod_component _ _
      (cubical12_adjunction_triangle_l F G adj) a).
  - intro b.
    exact (natmod_component _ _
      (cubical12_adjunction_triangle_r F G adj) b).
Defined.

(** A cubical adjunction stores exactly the higher naturality needed to lift
    its unit and counit through coherent graph-indexed functor categories. *)
Record CubicalAdjunction
  {A B : Type} `{Is21Cat A, Is21Cat B}
  (F : Fun22 A B) (G : Fun22 B A) := {
  cubical_adjunction_counit
    : CubicalNatTrans12
        (fun12_compose (fun12_fun22 F) (fun12_fun22 G))
        fun12_id;
  cubical_adjunction_unit
    : CubicalNatTrans12
        fun12_id
        (fun12_compose (fun12_fun22 G) (fun12_fun22 F));
  cubical_adjunction_triangle_l
    : NatModification
        (nattrans_comp
          (nattrans_prewhisker cubical_adjunction_counit F)
          (nattrans_postwhisker F cubical_adjunction_unit))
        (nattrans_id F);
  cubical_adjunction_triangle_r
    : NatModification
        (nattrans_comp
          (nattrans_postwhisker G cubical_adjunction_counit)
          (nattrans_prewhisker cubical_adjunction_unit G))
        (nattrans_id G);
}.

Definition gpd_adjunction_cubical
  {A B : Type} `{Is21Cat A, Is21Cat B}
  (F : Fun22 A B) (G : Fun22 B A)
  (adj : CubicalAdjunction F G)
  : GpdAdjunction F G.
Proof.
  napply (Build_GpdAdjunction_unit_counit F G
    (cubical_adjunction_counit F G adj)
    (cubical_adjunction_unit F G adj)).
  - intro a.
    exact (natmod_component _ _
      (cubical_adjunction_triangle_l F G adj) a).
  - intro b.
    exact (natmod_component _ _
      (cubical_adjunction_triangle_r F G adj) b).
Defined.

Section CubicalAdjunctionPostcomp.
  Context (A B J : Type)
    `{Is21Cat A, Is21Cat B, IsGraph J}
    (F : Fun22 A B) (G : Fun22 B A)
    (adj : CubicalAdjunction F G).

  Definition nattrans_cubical_adjunction_counit_postcomp
    : NatTrans
        (fun02_postcomp (A := J) (fun12_fun22 F) o
          fun02_postcomp (A := J) (fun12_fun22 G))
        idmap.
  Proof.
    snapply Build_NatTrans.
    - intro X.
      exact (nattrans_prewhisker
        (cubical_adjunction_counit F G adj) X).
    - snapply Build_Is1Natural.
      intros X Y alpha.
      snapply Build_NatModification.
      { exact (fun j => isnat
          (cubical_adjunction_counit F G adj) (alpha j)). }
      intros j j' f.
      unfold nattrans_prewhisker, trans_prewhisker.
      unfold nattrans_postwhisker, trans_postwhisker.
      unfold is1natural_comp, is1natural_prewhisker.
      unfold is1natural_postwhisker.
      cbn.
      rapply cylinder_rewrite_front.
      { exact (square_vconcat_natural_above
          (fmap_square_compose G F (isnat alpha f))
          (isnat (cubical_adjunction_counit F G adj) (fmap Y f))). }
      rapply cylinder_rewrite_back.
      { exact (square_vconcat_natural_below
          (isnat (cubical_adjunction_counit F G adj) (fmap X f))
          (fmap_square_id (isnat alpha f))^$). }
      exact (cubical12_naturality
        (cubical_adjunction_counit F G adj) (isnat alpha f)).
  Defined.

  Definition nattrans_cubical_adjunction_unit_postcomp
    : NatTrans
        idmap
        (fun02_postcomp (A := J) (fun12_fun22 G) o
          fun02_postcomp (A := J) (fun12_fun22 F)).
  Proof.
    snapply Build_NatTrans.
    - intro X.
      exact (nattrans_prewhisker
        (cubical_adjunction_unit F G adj) X).
    - snapply Build_Is1Natural.
      intros X Y alpha.
      snapply Build_NatModification.
      { exact (fun j => isnat
          (cubical_adjunction_unit F G adj) (alpha j)). }
      intros j j' f.
      unfold nattrans_prewhisker, trans_prewhisker.
      unfold nattrans_postwhisker, trans_postwhisker.
      unfold is1natural_comp, is1natural_prewhisker.
      unfold is1natural_postwhisker.
      cbn.
      rapply cylinder_rewrite_front.
      { exact (square_vconcat_natural_above
          (fmap_square_id (isnat alpha f))^$
          (isnat (cubical_adjunction_unit F G adj) (fmap Y f))). }
      rapply cylinder_rewrite_back.
      { exact (square_vconcat_natural_below
          (isnat (cubical_adjunction_unit F G adj) (fmap X f))
          (fmap_square_compose F G (isnat alpha f))). }
      exact (cubical12_naturality
        (cubical_adjunction_unit F G adj) (isnat alpha f)).
  Defined.

  Definition gpd_adjunction_fun02_postcomp_cubical
    : GpdAdjunction
        (fun12_fun02_postcomp (A := J) F)
        (fun12_fun02_postcomp (A := J) G).
  Proof.
    napply (Build_GpdAdjunction_unit_counit
      (fun12_fun02_postcomp (A := J) F)
      (fun12_fun02_postcomp (A := J) G)
      nattrans_cubical_adjunction_counit_postcomp
      nattrans_cubical_adjunction_unit_postcomp).
    - intro X.
      exact (natmod_prewhisker
        (cubical_adjunction_triangle_l F G adj) X).
    - intro X.
      exact (natmod_prewhisker
        (cubical_adjunction_triangle_r F G adj) X).
    Unshelve.
    { exact (is1functor_fun02_postcomp (A := J) F). }
    exact (is1functor_fun02_postcomp (A := J) G).
  Defined.
End CubicalAdjunctionPostcomp.

(** ** Coherent adjunction data and combinators *)

Section GpdAdjunctionData.
  Context {A B : Type} {F : A -> B} {G : B -> A}
    `{Is1Cat A, Is1Cat B,
      !Is0Functor F, !Is1Functor F,
      !Is0Functor G, !Is1Functor G}
    (adj : GpdAdjunction F G).

  Definition natequiv_gpd_adjunction_l (y : B)
    : NatEquiv (A := A^op) (yon_0gpd y o F) (yon_0gpd (G y))
        (is0functor_F := is0functor_compose
          (A := A^op) (B := B^op) (C := ZeroGpd)
          F (yon_0gpd y))
        (is0functor_G := is0functor_yon_0gpd (G y)).
  Proof.
    snapply Build_NatEquiv.
    - exact (fun x => equiv_gpd_adjunction F G adj x y).
    - exact (is1natural_equiv_gpd_adjunction_l F G adj y).
  Defined.

  Definition natequiv_gpd_adjunction_r (x : A)
    : NatEquiv (opyon_0gpd (F x)) (opyon_0gpd x o G)
        (is0functor_F := is0functor_opyon_0gpd (F x))
        (is0functor_G := is0functor_compose
          (A := B) (B := A) (C := ZeroGpd)
          G (opyon_0gpd x)).
  Proof.
    snapply Build_NatEquiv.
    - exact (equiv_gpd_adjunction F G adj x).
    - exact (is1natural_equiv_gpd_adjunction_r F G adj x).
  Defined.
End GpdAdjunctionData.

Section GpdAdjunctionPostcomp.
  Context (A B J : Type)
    `{Is1Cat A, Is1Cat B, IsGraph J}
    (F : Fun11 A B) (G : Fun11 B A)
    (adj : GpdAdjunction F G).

  Local Definition gpd_adjunction_postcomp_to
    (X : Fun01 J A) (Y : Fun01 J B)
    : fun01_compose F X $-> Y -> X $-> fun01_compose G Y.
  Proof.
    intro alpha.
    snapply Build_NatTrans.
    - intro j.
      exact (equiv_fun_0gpd
        (equiv_gpd_adjunction F G adj (X j) (Y j)) (alpha j)).
    - snapply Build_Is1Natural.
      intros j j' f.
      lhs' exact (isnat_tr
        (alnat := is1natural_equiv_gpd_adjunction_l F G adj (Y j'))
        (fun x => cate_fun (equiv_gpd_adjunction F G adj x (Y j')))
        (a := X j') (a' := X j) (fmap X f) (alpha j')).
      lhs' exact (fmap (equiv_fun_0gpd
        (equiv_gpd_adjunction F G adj (X j) (Y j')))
        (isnat alpha f)).
      exact (isnat
        (alnat := is1natural_equiv_gpd_adjunction_r F G adj (X j))
        (fun y => cate_fun (equiv_gpd_adjunction F G adj (X j) y))
        (fmap Y f) (alpha j)).
  Defined.

  Local Definition gpd_adjunction_postcomp_from
    (X : Fun01 J A) (Y : Fun01 J B)
    : X $-> fun01_compose G Y -> fun01_compose F X $-> Y.
  Proof.
    intro beta.
    snapply Build_NatTrans.
    - intro j.
      exact (equiv_fun_0gpd
        (equiv_gpd_adjunction F G adj (X j) (Y j))^-1$ (beta j)).
    - snapply Build_Is1Natural.
      intros j j' f.
      set (el := natequiv_inverse
        (@natequiv_gpd_adjunction_l A B F G
          _ _ _ _ _ _ _ _ _ _ adj (Y j'))).
      set (er := natequiv_inverse
        (@natequiv_gpd_adjunction_r A B F G
          _ _ _ _ _ _ _ _ _ _ adj (X j))).
      rapply (isnat_tr (alnat := is1natural_natequiv el)
        (a := X j') (a' := X j) el (fmap X f) (beta j') $@ _).
      rapply (fmap (equiv_fun_0gpd
        (equiv_gpd_adjunction F G adj (X j) (Y j'))^-1$)
        (isnat beta f) $@ _).
      exact (isnat (alnat := is1natural_natequiv er)
        er (fmap Y f) (beta j)).
  Defined.

  Local Definition gpd_adjunction_postcomp_hom
    (X : Fun01 J A) (Y : Fun01 J B)
    : opyon_0gpd (fun01_compose F X) Y
        $<~> opyon_0gpd X (fun01_compose G Y).
  Proof.
    snapply cate_adjointify.
    - snapply Build_Fun01'.
      + exact (gpd_adjunction_postcomp_to X Y).
      + intros alpha beta p j.
        exact (fmap (equiv_fun_0gpd
          (equiv_gpd_adjunction F G adj (X j) (Y j))) (p j)).
    - snapply Build_Fun01'.
      + exact (gpd_adjunction_postcomp_from X Y).
      + intros alpha beta p j.
        exact (fmap (equiv_fun_0gpd
          (equiv_gpd_adjunction F G adj (X j) (Y j))^-1$) (p j)).
    - intros beta j.
      exact (cat_eisretr
        (equiv_gpd_adjunction F G adj (X j) (Y j)) (beta j)).
    - intros alpha j.
      exact (cat_eissect
        (equiv_gpd_adjunction F G adj (X j) (Y j)) (alpha j)).
  Defined.

  Definition gpd_adjunction_postcomp
    : GpdAdjunction
        (fun11_fun01_postcomp (A := J) F)
        (fun11_fun01_postcomp (A := J) G).
  Proof.
    snapply Build_GpdAdjunction.
    - exact gpd_adjunction_postcomp_hom.
    - intro Y.
      snapply Build_Is1Natural.
      intros X' X alpha beta j.
      exact (isnat
        (alnat := is1natural_equiv_gpd_adjunction_l F G adj (Y j))
        (fun x => cate_fun (equiv_gpd_adjunction F G adj x (Y j)))
        (alpha j) (beta j)).
    - intro X.
      snapply Build_Is1Natural.
      intros Y Y' alpha beta j.
      exact (isnat
        (alnat := is1natural_equiv_gpd_adjunction_r F G adj (X j))
        (fun y => cate_fun (equiv_gpd_adjunction F G adj (X j) y))
        (alpha j) (beta j)).
  Defined.
End GpdAdjunctionPostcomp.

Section GpdAdjunctionCompose.
  Context (A B C : Type) `{Is1Cat A} `{Is1Cat B} `{Is1Cat C}.
  Context
    (F : Fun11 A B) (G : Fun11 B A)
    (F' : Fun11 B C) (G' : Fun11 C B)
    (adj : GpdAdjunction F G) (adj' : GpdAdjunction F' G').

  Local Definition gpd_adjunction_compose_hom (x : A) (z : C)
    : opyon_0gpd (F' (F x)) z $<~> opyon_0gpd x (G (G' z))
    := equiv_gpd_adjunction F G adj x (G' z)
         $oE equiv_gpd_adjunction F' G' adj' (F x) z.

  Definition gpd_adjunction_compose
    : GpdAdjunction (fun11_compose F' F) (fun11_compose G G').
  Proof.
    snapply Build_GpdAdjunction.
    - exact gpd_adjunction_compose_hom.
    - intro z.
      snapply Build_Is1Natural.
      intros x' x f h.
      unfold op in x', x, f.
      change (x $-> x') in f.
      change (F' (F x') $-> z) in h.
      cbn.
      change (equiv_fun_0gpd
        (equiv_gpd_adjunction F G adj x (G' z))
        (equiv_fun_0gpd
          (equiv_gpd_adjunction F' G' adj' (F x) z)
          (h $o fmap F' (fmap F f)))
        $==
          (equiv_fun_0gpd
            (equiv_gpd_adjunction F G adj x' (G' z))
            (equiv_fun_0gpd
              (equiv_gpd_adjunction F' G' adj' (F x') z) h)) $o f).
      rapply (fmap (equiv_fun_0gpd
        (equiv_gpd_adjunction F G adj x (G' z)))
        (isnat
          (alnat := is1natural_equiv_gpd_adjunction_l F' G' adj' z)
          (fun y => cate_fun (equiv_gpd_adjunction F' G' adj' y z))
          (a := F x') (a' := F x) (fmap F f) h) $@ _).
      rapply (isnat
        (alnat := is1natural_equiv_gpd_adjunction_l F G adj (G' z))
        (fun y => cate_fun (equiv_gpd_adjunction F G adj y (G' z)))
        (a := x') (a' := x) f (equiv_fun_0gpd
          (equiv_gpd_adjunction F' G' adj' (F x') z) h)).
    - intro x.
      snapply Build_Is1Natural.
      intros z z' f h.
      change (z $-> z') in f.
      change (F' (F x) $-> z) in h.
      cbn.
      change (equiv_fun_0gpd
        (equiv_gpd_adjunction F G adj x (G' z'))
        (equiv_fun_0gpd
          (equiv_gpd_adjunction F' G' adj' (F x) z')
          (f $o h))
        $== fmap G (fmap G' f) $o
          (equiv_fun_0gpd
            (equiv_gpd_adjunction F G adj x (G' z))
            (equiv_fun_0gpd
              (equiv_gpd_adjunction F' G' adj' (F x) z) h))).
      rapply (fmap (equiv_fun_0gpd
        (equiv_gpd_adjunction F G adj x (G' z')))
        (isnat
          (alnat := is1natural_equiv_gpd_adjunction_r F' G' adj' (F x))
          (fun y => cate_fun (equiv_gpd_adjunction F' G' adj' (F x) y))
          f h) $@ _).
      rapply (isnat
        (alnat := is1natural_equiv_gpd_adjunction_r F G adj x)
        (fun y => cate_fun (equiv_gpd_adjunction F G adj x y))
        (fmap G' f) (equiv_fun_0gpd
          (equiv_gpd_adjunction F' G' adj' (F x) z) h)).
  Defined.
End GpdAdjunctionCompose.

Section GpdAdjunctionNatEquiv.
  Context {A B : Type} `{Is1Cat A, HasEquivs B}
    (F F' : Fun11 A B) (G : Fun11 B A)
    (e : NatEquiv F F') (adj : GpdAdjunction F G).

  Local Definition gpd_adjunction_natequiv_left_hom (x : A) (y : B)
    : opyon_0gpd (F' x) y $<~> opyon_0gpd x (G y)
    := equiv_gpd_adjunction F G adj x y
         $oE equiv_precompose_cat_equiv_0gpd (e x).

  Definition gpd_adjunction_natequiv_left
    : GpdAdjunction F' G.
  Proof.
    snapply Build_GpdAdjunction.
    - exact gpd_adjunction_natequiv_left_hom.
    - intro y.
      exact (is1natural_natequiv
        (natequiv_compose
          (natequiv_gpd_adjunction_l adj y)
          (natequiv_postwhisker
            (A := A^op) (B := B^op) (C := ZeroGpd)
            (F := F') (G := F) (yon_0gpd y) (natequiv_op e)))).
    - intro x.
      exact (is1natural_natequiv
        (natequiv_compose
          (natequiv_gpd_adjunction_r adj x)
          (natequiv_opyon_equiv_0gpd (e x)))).
  Defined.
End GpdAdjunctionNatEquiv.

Section GpdAdjunctionNatEquivRight.
  Context {A B : Type} `{HasEquivs A, Is1Cat B}
    (F : Fun11 A B) (G G' : Fun11 B A)
    (e : NatEquiv G G') (adj : GpdAdjunction F G).

  Local Definition gpd_adjunction_natequiv_right_hom (x : A) (y : B)
    : opyon_0gpd (F x) y $<~> opyon_0gpd x (G' y)
    := equiv_postcompose_cat_equiv_0gpd (e y)
         $oE equiv_gpd_adjunction F G adj x y.

  Definition gpd_adjunction_natequiv_right
    : GpdAdjunction F G'.
  Proof.
    snapply Build_GpdAdjunction.
    - exact gpd_adjunction_natequiv_right_hom.
    - intro y.
      exact (is1natural_natequiv
        (natequiv_compose
          (natequiv_yon_equiv_0gpd (e y))
          (natequiv_gpd_adjunction_l adj y))).
    - intro x.
      exact (is1natural_natequiv
        (natequiv_compose
          (natequiv_postwhisker
            (A := B) (B := A) (C := ZeroGpd)
            (F := G) (G := G') (opyon_0gpd x) e)
          (natequiv_gpd_adjunction_r adj x))).
  Defined.
End GpdAdjunctionNatEquivRight.


(** TODO: move but where? *)
Lemma fun01_profunctor {A B C D : Type} (F : A -> B) (G : C -> D)
  `{Is0Functor A B F, Is0Functor C D G}
  : Fun01 (A^op * C) (B^op * D).
Proof.
  snapply Build_Fun01.
  1: exact (functor_prod (F : A^op -> B^op) G).
  rapply is0functor_prod_functor. (* Typeclass search gets confused by the opposite categories. *)
Defined.

(** ** Natural equivalences coming from adjunctions. *)

(** There are various bits of data we would like to extract from adjunctions. *)
Section AdjunctionData.
  Context {C D : Type} {F : C -> D} {G : D -> C}
    `{Is1Cat C, Is1Cat D, !HasMorExt C, !HasMorExt D,
      !Is0Functor F, !Is0Functor G, !Is1Functor F, !Is1Functor G}
    (adj : Adjunction F G).

  Definition natequiv_adjunction_l (y : D)
    : NatEquiv (A := C^op) (yon y o F)
        (** We have to explicitly give a witness to the functoriality of [yon y o F]. *)
        (is0functor_F := is0functor_compose (A:=C^op) (B:=D^op) (C:=Type) _ _)
        (yon (G y)).
  Proof.
    napply Build_NatEquiv.
    apply (is1natural_equiv_adjunction_l adj).
  Defined.

  Definition natequiv_adjunction_r (x : C)
    : NatEquiv (opyon (F x)) (opyon x o G).
  Proof.
    napply Build_NatEquiv.
    apply (is1natural_equiv_adjunction_r adj).
  Defined.

  (** We also have the natural equivalence in both arguments at the same time. *)
  (** In order to manage the typeclass instances, we have to bundle them up into Fun01. *)
  Definition natequiv_adjunction
    : NatEquiv (A := C^op * D)
        (fun01_compose fun01_hom (fun01_profunctor F idmap))
        (fun01_compose fun01_hom (fun01_profunctor idmap G)).
  Proof.
    snapply Build_NatEquiv.
    1: intros [x y]; exact (equiv_adjunction adj x y).
    snapply Build_Is1Natural.
    intros [a b] [a' b'] [f g] K.
    refine (_ @ ap (fun x : a $-> G b' => x $o f)
      (is1natural_equiv_adjunction_r adj a b b' g K)).
    exact (is1natural_equiv_adjunction_l adj _ _ _ f (g $o K)).
  Defined.

  (** The counit of an adjunction *)
  Definition adjunction_counit : NatTrans idmap (G o F).
  Proof.
    snapply Build_NatTrans.
    { hnf. intros x.
      exact (equiv_adjunction adj x (F x) (Id _)). }
    snapply Build_Is1Natural.
    intros x x' f.
    apply GpdHom_path.
    refine (_^ @ _ @ _).
    1: exact (is1natural_equiv_adjunction_l adj _ _ _ f (Id _)).
    2: exact (is1natural_equiv_adjunction_r adj _ _ _ (fmap F f) (Id _)).
    simpl.
    apply equiv_ap'.
    apply path_hom.
    apply Square.vrefl.
  Defined.

  (** The unit of an adjunction *)
  Definition adjunction_unit : NatTrans (F o G) idmap.
  Proof.
    snapply Build_NatTrans.
    { hnf. intros y.
      exact ((equiv_adjunction adj (G y) y)^-1 (Id _)). }
    snapply Build_Is1Natural.
    intros y y' f.
    apply GpdHom_path.
    refine (_^ @ _ @ _).
    1: exact (is1natural_natequiv (natequiv_inverse
        (natequiv_adjunction_l _)) (G y') _ (fmap G f) _).
    2: exact (is1natural_natequiv (natequiv_inverse
        (natequiv_adjunction_r _)) _ _ _ (Id _)).
    simpl.
    apply equiv_ap_inv'.
    apply path_hom.
    apply Square.vrefl.
  Defined.

  Lemma triangle_helper1 x y f
    : equiv_adjunction adj x y f = fmap G f $o adjunction_counit x.
  Proof.
    refine (_ @ is1natural_equiv_adjunction_r adj _ _ _ _ _).
    by cbv; rewrite (cat_idr_strong f).
  Qed.

  Lemma triangle_helper2 x y g
    : (equiv_adjunction adj x y)^-1 g = adjunction_unit y $o fmap F g.
  Proof.
    epose (n1 := is1natural_natequiv
      (natequiv_inverse (natequiv_adjunction_l _)) _ _ _ _).
    clearbody n1; cbv in n1.
    refine (_ @ n1).
    by rewrite cat_idl_strong.
  Qed.

  Definition adjunction_triangle1
    : Transformation 
        (nattrans_comp
          (nattrans_prewhisker adjunction_unit F)
          (nattrans_postwhisker F adjunction_counit))
        (nattrans_id _).
  Proof.
    intros c.
    change (?x $-> _) with (x $-> Id (F c)).
    rewrite <- (eissect (equiv_adjunction adj _ _) (Id (F c))).
    cbv;rewrite <- (triangle_helper2 _ (F c) (adjunction_counit _)).
    exact (Id _).
  Qed.

  Definition adjunction_triangle2
    : Transformation
        (nattrans_comp
          (nattrans_postwhisker G adjunction_unit)
          (nattrans_prewhisker adjunction_counit G))
        (nattrans_id _).
  Proof.
    intros d.
    change (?x $-> _) with (x $-> Id (G d)).
    rewrite <- (eisretr (equiv_adjunction adj _ _) (Id (G d))).
    cbv;rewrite <- (triangle_helper1 (G d) _ (adjunction_unit _)).
    exact (Id _).
  Qed.

End AdjunctionData.

(** ** Building adjunctions *)

(** There are various ways to build an adjunction. *)

(** A natural equivalence between functors [D -> Type] which is also natural in the left. *)
Definition Build_Adjunction_natequiv_nat_left
  {C D : Type} (F : C -> D) (G : D -> C)
  `{Is1Cat C, Is1Cat D, !Is0Functor F, !Is0Functor G} 
  (e : forall x, NatEquiv (opyon (F x)) (opyon x o G))
  (is1nat_e : forall y, Is1Natural (A := C^op) (yon y o F)
      (** We have to explicitly give a witness to the functoriality of [yon y o F]. *)
      (is0functor_F := is0functor_compose (A:=C^op) (B:=D^op) (C:=Type) _ _)
      (yon (G y)) (fun x => e _ y))
  : Adjunction F G.
Proof.
  snapply Build_Adjunction.
  1: exact (fun x => e x).
  1: exact is1nat_e.
  intros x; exact (is1natural_natequiv (e x)).
Defined.

(** A natural equivalence between functors [C^op -> Type] which is also natural in the left. *)
Definition Build_Adjunction_natequiv_nat_right
  {C D : Type} (F : C -> D) (G : D -> C)
  `{Is1Cat C, Is1Cat D, !Is0Functor F, !Is0Functor G} 
  (e : forall y, NatEquiv (A := C^op) (yon y o F) (yon (G y))
    (is0functor_F := is0functor_compose (A:=C^op) (B:=D^op) (C:=Type) _ _))
  (is1nat_e : forall x, Is1Natural (opyon (F x)) (opyon x o G) (fun y => e y x))
  : Adjunction F G.
Proof.
  snapply Build_Adjunction.
  1: exact (fun x y => e y x).
  1: intros y; exact (is1natural_natequiv (e y)).
  exact is1nat_e.
Defined.

(** TODO: A natural equivalence between functors [C^op * D -> Type] *)

Section UnitCounitAdjunction.

  (** From the data of an adjunction: unit, counit, left triangle, right triangle *)
  Context {C D : Type} (F : C -> D) (G : D -> C)
  `{Is1Cat C, Is1Cat D, !Is0Functor F, !Is0Functor G,
    !Is1Functor F, !Is1Functor G}
  `{!HasMorExt C, !HasMorExt D}
  (ε : NatTrans (F o G) idmap)
  (η : NatTrans idmap (G o F))
  (t1 : Transformation 
    (nattrans_comp (nattrans_prewhisker ε F) (nattrans_postwhisker F η))
    (nattrans_id _))
  (t2 : Transformation
    (nattrans_comp (nattrans_postwhisker G ε) (nattrans_prewhisker η G))
    (nattrans_id _)).

  (** We can construct an equivalence between homs *)
  Local Definition γ a b : (F a $-> b) $<~> (a $-> G b).
  Proof.
    srapply equiv_adjointify.
    1: exact (fun x => fmap G x $o (η : _ $=> _) a).
    1: exact (fun x => (ε : _ $=> _) b $o fmap F x).
    + intros f.
      apply path_hom; simpl.
      refine ((fmap_comp G _ _ $@R _) $@ _).
      refine (cat_assoc _ _ _ $@ _).
      refine ((_ $@L (isnat η f)^$) $@ _).
      refine (cat_assoc_opp _ _ _ $@ _).
      refine (_ $@R _ $@ cat_idl _).
      exact (t2 b).
    + intros g.
      apply path_hom; simpl.
      refine ((_ $@L fmap_comp F _ _) $@ _).
      refine (cat_assoc_opp _ _ _ $@ _).
      refine (((isnat ε g) $@R _) $@ _).
      refine (cat_assoc _ _ _ $@ _).
      refine (_ $@L _ $@ cat_idr _).
      exact (t1 a).
  Defined.

  (** Which is natural in the left *)
  Lemma is1natural_γ_l (y : D)
    : Is1Natural (yon y o F) (yon (G y))
      (is0functor_F := is0functor_compose (A:=C^op) (B:=D^op) (C:=Type) _ _)
      (is0functor_G := is0functor_yon (G y))
      (fun x : C^op => γ x y).
  Proof.
    napply (is1natural_natequiv (natequiv_inverse
      (Build_NatEquiv (yon (G y)) (yon y o F) (fun x => (γ x y)^-1$) _))).
    napply is1natural_yoneda.
    napply is1functor_compose.
    1: napply is1functor_op; exact _.
    napply is1functor_opyon.
    exact hasmorext_op.
  Defined.

  (** And natural in the right. *)
  Lemma is1natural_γ_r x
    : Is1Natural (opyon (F x)) (fun x0 : D => opyon x (G x0)) (γ x).
  Proof.
    napply is1natural_opyoneda.
    exact _.
  Defined.

  (** Together this constructs an adjunction. *)
  Definition Build_Adjunction_unit_counit : Adjunction F G.
  Proof.
    snapply Build_Adjunction.
    - exact γ.
    - exact is1natural_γ_l.
    - exact is1natural_γ_r.
  Defined.

End UnitCounitAdjunction.

(** * Properties of adjunctions *)

(** ** Postcomposition adjunction *)
(** There are at least two easy proofs of the following on paper:
 1. Using ends: Hom(F*x,y) ≃ ∫_c Hom(Fxc,yc) ≃ ∫_c Hom(xc,Gyc) ≃ Hom(x,G*y)
 2. 2-cat theory: postcomp (-)* is a 2-functor so preserves adjunctions.
*)

Lemma adjunction_postcomp (C D J : Type)
  `{HasEquivs C, HasEquivs D, Is01Cat J} (F : Fun11 C D) (G : Fun11 D C)
  `{!HasMorExt C, !HasMorExt D, !HasMorExt (Fun01 J C), !HasMorExt (Fun01 J D)}
  : F ⊣ G -> fun11_fun01_postcomp (A:=J) F ⊣ fun11_fun01_postcomp (A:=J) G.
Proof.
  intros adj.
  srapply Build_Adjunction_unit_counit.
  - snapply Build_NatTrans.
    + intros K.
      exact (nattrans_prewhisker (adjunction_unit adj) K).
    + snapply Build_Is1Natural.
      intros K K' θ j.
      apply GpdHom_path.
      refine (_ @ is1natural_natequiv (natequiv_inverse
        (natequiv_adjunction_r adj _)) _ _ _ _).
      refine ((is1natural_natequiv (natequiv_inverse
        (natequiv_adjunction_l adj _)) _ _ _ _)^ @ _).
      cbn; rapply ap.
      refine(cat_idl_strong _ @ _^).
      apply cat_idr_strong.
  - snapply Build_NatTrans.
    + intros K.
      exact (nattrans_prewhisker (adjunction_counit adj) K).
    + snapply Build_Is1Natural.
      intros K K' θ j.
      apply GpdHom_path.
      refine (_ @ is1natural_natequiv
        (natequiv_adjunction_r adj _) _ _ _ _).
      refine ((is1natural_natequiv
        (natequiv_adjunction_l adj _) _ _ _ _)^ @ _).
      cbn; rapply ap.
      refine(cat_idl_strong _ @ _^).
      apply cat_idr_strong.
  - exact (trans_prewhisker (adjunction_triangle1 adj)).
  - exact (trans_prewhisker (adjunction_triangle2 adj)).
Defined.

(** We can compose adjunctions. Notice how the middle category must have equivalences. *)
Lemma adjunction_compose (A B C : Type)
  (F : A -> B) (G : B -> A) (F' : B -> C) (G' : C -> B)
  `{Is1Cat A, HasEquivs B, Is1Cat C}
  `{!Is0Functor F, !Is0Functor G, !Is0Functor F', !Is0Functor G'}
  : F ⊣ G -> F' ⊣ G' -> F' o F ⊣ G o G'.
Proof.
  intros adj1 adj2.
  snapply Build_Adjunction_natequiv_nat_right.
  { intros y.
    nrefine (natequiv_compose (natequiv_adjunction_l adj1 _) _).
    exact (natequiv_prewhisker (A:=A^op) (B:=B^op)
      (natequiv_adjunction_l adj2 y) F). }
  intros x.
  rapply is1natural_comp.
  + exact (is1natural_prewhisker G' (natequiv_adjunction_r adj1 x)).
  + napply is1natural_equiv_adjunction_r.
Defined.

(** Replace the left functor in an adjunction by a naturally equivalent one. *)
Lemma adjunction_natequiv_left {C D : Type} (F F' : C -> D) (G : D -> C)
  `{Is1Cat C, HasEquivs D, !HasMorExt D,
    !Is0Functor F, !Is0Functor F', !Is0Functor G} 
  : NatEquiv F F' -> F ⊣ G -> F' ⊣ G.
Proof.
  intros e adj.
  snapply Build_Adjunction_natequiv_nat_right.
  { intros y.
    refine (natequiv_compose (natequiv_adjunction_l adj _) _).
    exact (natequiv_postwhisker _ (natequiv_op e)). }
  intros x.
  rapply is1natural_comp.
Defined.

(** Replace the right functor in an adjunction by a naturally equivalent one. *)
Lemma adjunction_natequiv_right {C D : Type} (F : C -> D) (G G' : D -> C)
  `{HasEquivs C, Is1Cat D, !HasMorExt C,
    !Is0Functor F, !Is0Functor G, !Is0Functor G'} 
  : NatEquiv G G' -> F ⊣ G -> F ⊣ G'.
Proof.
  intros e adj.
  snapply Build_Adjunction_natequiv_nat_left.
  { intros x.
    refine (natequiv_compose _ (natequiv_adjunction_r adj _)).
    exact (natequiv_postwhisker _ e). }
  intros y.
  rapply is1natural_comp.
  2: exact _.
  rapply is1natural_yoneda.
Defined.

