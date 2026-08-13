Require Import Basics.Equivalences Basics.Overture Basics.PathGroupoids
  Basics.Tactics.
Require Import WildCat.Core WildCat.NatTrans WildCat.FunctorCat.
Require Import WildCat.Equiv WildCat.Opposite.
Require Import WildCat.Yoneda WildCat.EquivGpd WildCat.ZeroGroupoid.
Require Import WildCat.TwoFunctor WildCat.Cylinder WildCat.Square
  WildCat.TwoOneCat.

Set Typeclasses Depth 4.

(** * Scratch work on wild limits and colimits *)

(** This file develops limits and colimits as adjoints to diagonal functors.  It is intentionally kept separate while the coherent functor-category interface is being worked out. *)

(** ** Adjunctions enriched in 0-groupoids *)

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
      lhs' exact ((isnat epsilon g) $@R _).
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

(** ** Diagonal functors *)

Section Diagonal.
  Context (A J : Type) `{Is1Cat A, IsGraph J}.

  Definition diagonal : A -> Fun01 J A
    := fun x => Build_Fun01 (fun _ => x).

  Global Instance is0functor_diagonal : Is0Functor diagonal.
  Proof.
    snapply Build_Is0Functor.
    intros a b f.
    snapply Build_NatTrans.
    - exact (fun _ => f).
    - snapply Build_Is1Natural.
      intros x y g.
      exact (cat_idr _ $@ (cat_idl _)^$).
  Defined.

  Global Instance is1functor_diagonal : Is1Functor diagonal.
  Proof.
    snapply Build_Is1Functor.
    - exact (fun a b f g p j => p).
    - intros a j; reflexivity.
    - intros a b c f g j; reflexivity.
  Defined.

  Definition fun11_diagonal : Fun11 A (Fun01 J A)
    := Build_Fun11 _ _ diagonal.

  Class HasLimit := {
    cat_limit : Fun11 (Fun01 J A) A;
    adjunction_cat_limit : GpdAdjunction fun11_diagonal cat_limit;
  }.

  Class HasColimit := {
    cat_colimit : Fun11 (Fun01 J A) A;
    adjunction_cat_colimit : GpdAdjunction cat_colimit fun11_diagonal;
  }.
End Diagonal.

(** ** Coherent diagonal functors *)

(** This is the coherent counterpart of [diagonal].  It is only
    bundled as a [Fun02]: the enriched adjunction below needs the
    action on 1-cells and their naturality cylinders, but it does not
    need pseudofunctor coherence for the diagonal. *)
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

  Definition fun02_diagonal : Fun02 A (Fun02 J A)
    := Build_Fun02 diagonal02.

  Class HasLimit02 := {
    cat_limit02 : Fun12 (Fun02 J A) A;
    adjunction_cat_limit02
      : GpdAdjunction fun02_diagonal cat_limit02;
  }.

  Class HasColimit02 := {
    cat_colimit02 : Fun12 (Fun02 J A) A;
    adjunction_cat_colimit02
      : GpdAdjunction cat_colimit02 fun02_diagonal;
  }.
End Diagonal02.

(** Evaluation retains modifications, so it is a coherent
    1-functor without any further diagram-shape assumptions. *)
Definition fun12_eval_fun02 {A B : Type}
  `{IsGraph A, Is21Cat B} (a : A)
  : Fun12 (Fun02 A B) B.
Proof.
  snapply Build_Fun12.
  - exact (fun F => F a).
  - snapply Build_Is0Functor.
    exact (fun F G alpha => alpha a).
  - snapply Build_Is1Functor.
    + intros F G alpha beta p.
      exact (natmod_component alpha beta p a).
    + intro F.
      exact (Id _).
    + intros F G K alpha beta.
      exact (Id _).
Defined.

(** The chosen reverse associator is also the reverse of the forward
    associator. *)
Local Definition cat_assoc_rev_is_opp
  {D : Type} `{Is21Cat D}
  {a b c d : D} (f : a $-> b) (g : b $-> c) (h : c $-> d)
  : (cat_assoc f g h)^$ $== cat_assoc_opp f g h.
Proof.
  symmetry.
  rapply cat_assoc_opp_is_rev.
Defined.

(** Swapping the two graph variables preserves the cylinder data in
    the eventual action on transformations.  The definition here is
    only the object-and-arrow part of that construction. *)
Section Swap02.
  Context (A B C : Type) `{IsGraph A, IsGraph B, Is21Cat C}.

  Definition swap_fun02_at
    (F : Fun02 A (Fun02 B C)) (b : B)
    : Fun02 A C.
  Proof.
    snapply Build_Fun02.
    { exact (fun a => F a b). }
    snapply Build_Is0Functor.
    exact (fun a a' f => fmap F f b).
  Defined.

  Definition swap_fun02_fmap
    (F : Fun02 A (Fun02 B C)) {b b' : B} (g : b $-> b')
    : swap_fun02_at F b $-> swap_fun02_at F b'.
  Proof.
    snapply Build_NatTrans.
    { exact (fun a => fmap (F a) g). }
    snapply Build_Is1Natural.
    intros a a' f.
    change (Square
      (fmap (F a) g) (fmap (F a') g) (fmap F f b) (fmap F f b')).
    napply transpose.
    rapply isnat.
  Defined.

  Definition swap_fun02
    : Fun02 A (Fun02 B C) -> Fun02 B (Fun02 A C).
  Proof.
    intro F.
    snapply Build_Fun02.
    { exact (swap_fun02_at F). }
    snapply Build_Is0Functor.
    intros b b' g.
    exact (swap_fun02_fmap F g).
  Defined.

  Definition nattrans_swap_fun02_at
    {F G : Fun02 A (Fun02 B C)} (alpha : F $-> G) (b : B)
    : swap_fun02 F b $-> swap_fun02 G b.
  Proof.
    snapply Build_NatTrans.
    { exact (fun a => alpha a b). }
    snapply Build_Is1Natural.
    intros a a' f.
    exact (fmap2 (fun12_eval_fun02 b) (isnat alpha f)).
  Defined.

  Definition natmod_swap_fun02_naturality
    {F G : Fun02 A (Fun02 B C)} (alpha : F $-> G)
    {b b' : B} (g : b $-> b')
    : nattrans_swap_fun02_at alpha b'
        $o fmap (swap_fun02 F) g
      $== fmap (swap_fun02 G) g
        $o nattrans_swap_fun02_at alpha b.
  Proof.
    snapply Build_NatModification.
    { intro a.
      exact (isnat (alpha a) g). }
    intros a a' f.
    cbn beta.
    rapply cylinder_rotate_vconcat.
    exact (natmod_isnatural _ _
      (isnat (alnat := is1natural_nattrans alpha) alpha f) g).
  Defined.

  Definition nattrans_swap_fun02
    {F G : Fun02 A (Fun02 B C)} (alpha : F $-> G)
    : swap_fun02 F $-> swap_fun02 G.
  Proof.
    snapply Build_NatTrans.
    { exact (nattrans_swap_fun02_at alpha). }
    snapply Build_Is1Natural.
    intros b b' g.
    exact (natmod_swap_fun02_naturality alpha g).
  Defined.

  Definition natmod_swap_fun02_at
    {F G : Fun02 A (Fun02 B C)}
    {alpha beta : F $-> G} (p : alpha $== beta) (b : B)
    : nattrans_swap_fun02_at alpha b
      $== nattrans_swap_fun02_at beta b.
  Proof.
    snapply Build_NatModification.
    { intro a.
      exact (natmod_component
        (alpha a) (beta a) (natmod_component alpha beta p a) b). }
    intros a a' f.
    exact (natmod_isnatural alpha beta p f b).
  Defined.

  Definition natmod_swap_fun02
    {F G : Fun02 A (Fun02 B C)}
    {alpha beta : F $-> G} (p : alpha $== beta)
    : nattrans_swap_fun02 alpha $== nattrans_swap_fun02 beta.
  Proof.
    snapply Build_NatModification.
    { exact (natmod_swap_fun02_at p). }
    intros b b' g a.
    exact (natmod_isnatural
      (alpha a) (beta a) (natmod_component alpha beta p a) g).
  Defined.

  Definition natmod_swap_fun02_id_at
    (F : Fun02 A (Fun02 B C)) (b : B)
    : nattrans_swap_fun02_at (Id F) b
      $== Id (swap_fun02 F b).
  Proof.
    snapply Build_NatModification.
    { intro a.
      exact (Id _). }
    intros a a' f.
    exact (cylinder_refl _).
  Defined.

  Definition natmod_swap_fun02_id
    (F : Fun02 A (Fun02 B C))
    : nattrans_swap_fun02 (Id F) $== Id (swap_fun02 F).
  Proof.
    snapply Build_NatModification.
    { exact (natmod_swap_fun02_id_at F). }
    intros b b' g a.
    exact (cylinder_refl _).
  Defined.

  Definition natmod_swap_fun02_comp_at
    {F G K : Fun02 A (Fun02 B C)}
    (alpha : F $-> G) (beta : G $-> K) (b : B)
    : nattrans_swap_fun02_at (beta $o alpha) b
      $== nattrans_swap_fun02_at beta b
        $o nattrans_swap_fun02_at alpha b.
  Proof.
    snapply Build_NatModification.
    { intro a.
      exact (Id _). }
    intros a a' f.
    rapply cylinder_rewrite_back.
    { rapply cat_prewhisker.
      rapply cat_postwhisker.
      rapply cat_postwhisker.
      nrefine (cat_assoc_opp_is_rev _ _ _ _ _ _ _). }
    exact (cylinder_refl _).
  Defined.

  Definition natmod_swap_fun02_comp
    {F G K : Fun02 A (Fun02 B C)}
    (alpha : F $-> G) (beta : G $-> K)
    : nattrans_swap_fun02 (beta $o alpha)
      $== nattrans_swap_fun02 beta $o nattrans_swap_fun02 alpha.
  Proof.
    snapply Build_NatModification.
    { exact (natmod_swap_fun02_comp_at alpha beta). }
    intros b b' g.
    rapply Build_Cylinder_fun02.
    intro a.
    rapply cylinder_rewrite_back.
    { rapply cat_prewhisker.
      rapply cat_postwhisker.
      rapply cat_postwhisker.
      nrefine (cat_assoc_rev_is_opp _ _ _). }
    exact (cylinder_refl _).
  Defined.

  Global Instance is0functor_swap_fun02
    : Is0Functor swap_fun02.
  Proof.
    snapply Build_Is0Functor.
    exact (fun F G alpha => nattrans_swap_fun02 alpha).
  Defined.

  Global Instance is1functor_swap_fun02
    : Is1Functor swap_fun02.
  Proof.
    snapply Build_Is1Functor.
    { intros F G alpha beta p.
      exact (natmod_swap_fun02 p). }
    { exact natmod_swap_fun02_id. }
    intros F G K alpha beta.
    exact (natmod_swap_fun02_comp alpha beta).
  Defined.

  Definition fun12_swap_fun02
    : Fun12
        (Fun02 A (Fun02 B C))
        (Fun02 B (Fun02 A C))
    := Build_Fun12 swap_fun02.

  Definition fun02_swap_fun02
    : Fun02
        (Fun02 A (Fun02 B C))
        (Fun02 B (Fun02 A C))
    := fun02_fun12 fun12_swap_fun02.
End Swap02.

(** ** The coherent argument-swap adjunction *)

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

  Local Instance is1natural_equiv_swap_fun02_hom_l
    (G : Fun02 B (Fun02 A C))
    : Is1Natural (A := (Fun02 A (Fun02 B C))^op)
        (isgraph_A := isgraph_op)
        (is0functor_F := is0functor_compose
          (A := (Fun02 A (Fun02 B C))^op)
          (B := (Fun02 B (Fun02 A C))^op)
          (C := ZeroGpd)
          (swap_fun02 A B C) (yon_0gpd G))
        (is0functor_G := is0functor_yon_0gpd
          (swap_fun02 B A C G))
        (yon_0gpd G o swap_fun02 A B C)
        (yon_0gpd (swap_fun02 B A C G))
        (fun F => cate_fun (equiv_swap_fun02_hom F G)).
  Proof.
    snapply Build_Is1Natural.
    intros F F' alpha beta.
    nrefine (natmod_swap_fun02_hom_to_precompose alpha beta).
  Defined.

  Definition natequiv_swap_fun02_hom_l
    (G : Fun02 B (Fun02 A C))
    : NatEquiv (A := (Fun02 A (Fun02 B C))^op)
        (is0functor_F := is0functor_compose
          (A := (Fun02 A (Fun02 B C))^op)
          (B := (Fun02 B (Fun02 A C))^op)
          (C := ZeroGpd)
          (swap_fun02 A B C) (yon_0gpd G))
        (is0functor_G := is0functor_yon_0gpd
          (swap_fun02 B A C G))
        (yon_0gpd G o swap_fun02 A B C)
        (yon_0gpd (swap_fun02 B A C G)).
  Proof.
    snapply Build_NatEquiv.
    { exact (fun F => equiv_swap_fun02_hom F G). }
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

(** ** Pointwise coherent limit and colimit candidates *)

Section PointwiseLimit02.
  Context (A B J : Type) `{IsGraph A, Is21Cat B, IsGraph J}.
  Context `{!HasLimit02 B J}.

  Definition fun02_pointwise_limit
    : Fun02 (Fun02 J (Fun02 A B)) (Fun02 A B)
    := fun02_compose
      (fun02_fun02_postcomp (A := A) (cat_limit02 B J))
      (fun02_swap_fun02 J A B).
End PointwiseLimit02.

Section PointwiseColimit02.
  Context (A B J : Type) `{IsGraph A, Is21Cat B, IsGraph J}.
  Context `{!HasColimit02 B J}.

  Definition fun02_pointwise_colimit
    : Fun02 (Fun02 J (Fun02 A B)) (Fun02 A B)
    := fun02_compose
      (fun02_fun02_postcomp (A := A) (cat_colimit02 B J))
      (fun02_swap_fun02 J A B).
End PointwiseColimit02.

(** ** Preservation by adjoints *)

Class PreservesLimits (A B J : Type)
  `{Is1Cat A, IsGraph J, !HasLimit A J,
    HasEquivs B, !HasLimit B J}
  (F : Fun11 A B) :=
  equiv_preserveslimits (X : Fun01 J A)
    : F (cat_limit A J X)
      $<~> cat_limit B J (fun01_compose F X).

Class PreservesColimits (A B J : Type)
  `{Is1Cat A, IsGraph J, !HasColimit A J,
    HasEquivs B, !HasColimit B J}
  (F : Fun11 A B) :=
  equiv_preservescolimits (X : Fun01 J A)
    : F (cat_colimit A J X)
      $<~> cat_colimit B J (fun01_compose F X).

(** Right adjoints preserve limits. *)
Definition preserveslimits_right_adjoint
  (A B J : Type)
  `{HasEquivs A, HasEquivs B, IsGraph J,
    !HasLimit A J, !HasLimit B J}
  (L : Fun11 A B) (R : Fun11 B A) (adj : GpdAdjunction L R)
  : PreservesLimits B A J R.
Proof.
  intro K.
  srapply yon_equiv_0gpd.
  rapply (natequiv_compose
    (natequiv_gpd_adjunction_l (adjunction_cat_limit A J)
      (fun11_fun01_postcomp R K)) _).
  rapply (natequiv_compose
    (natequiv_prewhisker
      (natequiv_gpd_adjunction_l
        (gpd_adjunction_postcomp A B J L R adj) K)
      (diagonal A J)) _).
  rapply (natequiv_compose _
    (natequiv_inverse
      (natequiv_gpd_adjunction_l adj (cat_limit B J K)))).
  rapply (natequiv_compose _
    (natequiv_inverse
      (natequiv_prewhisker
        (natequiv_gpd_adjunction_l (adjunction_cat_limit B J) K) L))).
  rapply (natequiv_compose
    (natequiv_inverse (natequiv_functor_assoc_ff_f
      (A := A^op) (B := (Fun01 J A)^op)
      (C := (Fun01 J B)^op) (D := ZeroGpd)
      (yon_0gpd K) (fun11_fun01_postcomp L) (diagonal A J))) _).
  rapply (natequiv_compose _
    (natequiv_functor_assoc_ff_f
      (A := A^op) (B := B^op)
      (C := (Fun01 J B)^op) (D := ZeroGpd)
      (yon_0gpd K) (diagonal B J) L)).
  rapply (natequiv_postwhisker
    (A := A^op) (B := (Fun01 J B)^op) (C := ZeroGpd)
    (F := (diagonal B J) o L)
    (G := (fun11_fun01_postcomp L) o (diagonal A J))
    (yon_0gpd K) _).
  snapply Build_NatEquiv.
  - intro a.
    snapply cate_adjointify.
    + snapply Build_NatTrans.
      * exact (fun _ => Id _).
      * snapply Build_Is1Natural.
        intros i j f.
        napply cat_postwhisker.
        exact (fmap_id L _).
    + snapply Build_NatTrans.
      * exact (fun _ => Id _).
      * snapply Build_Is1Natural.
        intros i j f.
        napply cat_prewhisker.
        exact ((fmap_id L _)^$).
    + exact (fun _ => cat_idl _).
    + exact (fun _ => cat_idr _).
  - snapply Build_Is1Natural.
    intros a a' f.
    unfold trans_comp, cate_adjointify.
    rapply ((cate_buildequiv_fun _ $@R _) $@ _).
    rapply (_ $@ (_ $@L _)).
    2: symmetry; napply cate_buildequiv_fun.
    exact (fun _ => cat_idr _ $@ (cat_idl _)^$).
Defined.

(** Left adjoints preserve colimits. *)
Definition preservescolimits_left_adjoint
  (A B J : Type)
  `{HasEquivs A, HasEquivs B, IsGraph J,
    !HasColimit A J, !HasColimit B J}
  (L : Fun11 A B) (R : Fun11 B A) (adj : GpdAdjunction L R)
  : PreservesColimits A B J L.
Proof.
  intro K.
  srapply opyon_equiv_0gpd.
  rapply (natequiv_compose
    (natequiv_inverse
      (natequiv_gpd_adjunction_r adj (cat_colimit A J K))) _).
  rapply (natequiv_compose
    (natequiv_inverse
      (natequiv_prewhisker
        (natequiv_gpd_adjunction_r (adjunction_cat_colimit A J) K) R)) _).
  rapply (natequiv_compose _
    (natequiv_gpd_adjunction_r (adjunction_cat_colimit B J) _)).
  rapply (natequiv_compose _
    (natequiv_prewhisker
      (natequiv_gpd_adjunction_r
        (gpd_adjunction_postcomp A B J L R adj) _) _)).
  rapply (natequiv_compose _
    (natequiv_functor_assoc_ff_f
      (A := B) (B := Fun01 J B)
      (C := Fun01 J A) (D := ZeroGpd)
      (opyon_0gpd K) (fun11_fun01_postcomp R) (diagonal B J))).
  rapply (natequiv_compose
    (natequiv_inverse (natequiv_functor_assoc_ff_f
      (A := B) (B := A)
      (C := Fun01 J A) (D := ZeroGpd)
      (opyon_0gpd K) (diagonal A J) R)) _).
  rapply (natequiv_postwhisker
    (A := B) (B := Fun01 J A) (C := ZeroGpd)
    (F := (fun11_fun01_postcomp R) o (diagonal B J))
    (G := (diagonal A J) o R)
    (opyon_0gpd K) _).
  snapply Build_NatEquiv.
  - intro b.
    snapply Build_NatEquiv.
    + exact (fun _ => id_cate _).
    + snapply Build_Is1Natural.
      intros a a' f.
      rapply ((cate_buildequiv_fun _ $@R _) $@ _
        $@ (_ $@L (cate_buildequiv_fun _)^$)).
      exact (cat_idl _ $@ fmap_id R _ $@ (cat_idr _)^$).
  - snapply Build_Is1Natural.
    intros a a' f j.
    rapply ((cate_buildequiv_fun _ $@R _) $@ _
      $@ (_ $@L (cate_buildequiv_fun _)^$)).
    exact (cat_idl _ $@ (cat_idr _)^$).
Defined.

(** ** Evaluation and argument swap *)

Definition fun11_eval_fun01 {A B : Type}
  `{IsGraph A, Is1Cat B} (a : A)
  : Fun11 (Fun01 A B) B.
Proof.
  snapply Build_Fun11.
  - exact (fun F => F a).
  - snapply Build_Is0Functor.
    exact (fun F G alpha => alpha a).
  - snapply Build_Is1Functor.
    + exact (fun F G alpha beta p => p a).
    + reflexivity.
    + reflexivity.
Defined.

Definition fun01_2cell_at {A B : Type} `{IsGraph A, Is1Cat B}
  {F G : Fun01 A B} {alpha beta : F $-> G}
  (p : alpha $== beta) (a : A)
  : alpha a $== beta a
  := p a.

Section Swap.
  Context (A B C : Type) `{IsGraph A, IsGraph B, Is1Cat C}.

  Definition swap_fun01
    : Fun01 A (Fun01 B C) -> Fun01 B (Fun01 A C).
  Proof.
    intro F.
    snapply Build_Fun01.
    { intro b.
      snapply Build_Fun01.
      { exact (fun a => F a b). }
      snapply Build_Is0Functor.
      exact (fun a a' f => fmap F f b). }
    snapply Build_Is0Functor.
    intros b b' g.
    snapply Build_NatTrans.
    { exact (fun a => fmap (F a) g). }
    snapply Build_Is1Natural.
    intros a a' f.
    symmetry.
    cbn; set (fmap F f) as alpha.
    exact (isnat alpha g).
  Defined.

  Global Instance is0functor_swap_fun01
    : Is0Functor swap_fun01.
  Proof.
    snapply Build_Is0Functor.
    intros F G alpha.
    snapply Build_NatTrans.
    - intro b.
      snapply Build_NatTrans.
      + exact (fun a => alpha a b).
      + snapply Build_Is1Natural'.
        * exact (fun a a' f => isnat alpha f b).
        * exact (fun a a' f => isnat_tr alpha f b).
    - snapply Build_Is1Natural'.
      + exact (fun b b' g a => isnat (alpha a) g).
      + exact (fun b b' g a => isnat_tr (alpha a) g).
  Defined.

  Global Instance is1functor_swap_fun01
    : Is1Functor swap_fun01.
  Proof.
    snapply Build_Is1Functor.
    - exact (fun F G alpha beta p b a => p a b).
    - exact (fun F b a => Id _).
    - exact (fun F G K alpha beta b a => Id _).
  Defined.

  Definition fun11_swap_fun01
    : Fun11 (Fun01 A (Fun01 B C)) (Fun01 B (Fun01 A C))
    := Build_Fun11 _ _ swap_fun01.

  Definition nattrans_swap_fun01_diagonal
    : NatTrans
        (fun11_compose fun11_swap_fun01
          (fun11_fun01_postcomp (A := A) (fun11_diagonal C B)))
        (fun11_diagonal (Fun01 A C) B).
  Proof.
    snapply Build_NatTrans.
    - intro F.
      snapply Build_NatTrans.
      + intro b.
        snapply Build_NatTrans.
        * exact (fun a => Id _).
        * snapply Build_Is1Natural.
          intros a a' f.
          exact (cat_idl _ $@ (cat_idr _)^$).
      + snapply Build_Is1Natural.
        intros b b' g a.
        exact (cat_idr _ $@ (cat_idl _)^$).
    - snapply Build_Is1Natural.
      intros F G alpha b a.
      cbn.
      exact (cat_idl _ $@ (cat_idr _)^$).
  Defined.

  Definition natequiv_swap_fun01_diagonal `{!HasEquivs C}
    : NatEquiv
        (fun11_compose fun11_swap_fun01
          (fun11_fun01_postcomp (A := A) (fun11_diagonal C B)))
        (fun11_diagonal (Fun01 A C) B).
  Proof.
    snapply Build_NatEquiv'.
    - exact nattrans_swap_fun01_diagonal.
    - intros F b a; exact _.
  Defined.
End Swap.

Section SwapAdjunction.
  Context (A B C : Type) `{IsGraph A, IsGraph B, Is1Cat C}.

  Local Definition swap_fun01_rev
    : Fun01 B (Fun01 A C) -> Fun01 A (Fun01 B C)
    := swap_fun01 B A C.

  Definition swap_fun01_hom_to
    (F : Fun01 A (Fun01 B C)) (G : Fun01 B (Fun01 A C))
    : swap_fun01 A B C F $-> G
      -> F $-> swap_fun01_rev G.
  Proof.
    intro alpha.
    snapply Build_NatTrans.
    - intro a.
      snapply Build_NatTrans.
      + exact (fun b => alpha b a).
      + snapply Build_Is1Natural'.
        * intros b b' g.
          exact (fun01_2cell_at
            (isnat (alnat := is1natural_nattrans alpha) alpha g) a).
        * intros b b' g.
          exact (fun01_2cell_at
            (isnat_tr (alnat := is1natural_nattrans alpha) alpha g) a).
    - snapply Build_Is1Natural'.
      + intros a a' f b.
        exact (isnat (alnat := is1natural_nattrans (alpha b)) (alpha b) f).
      + intros a a' f b.
        exact (isnat_tr (alnat := is1natural_nattrans (alpha b)) (alpha b) f).
  Defined.

  Definition swap_fun01_hom_from
    (F : Fun01 A (Fun01 B C)) (G : Fun01 B (Fun01 A C))
    : F $-> swap_fun01_rev G
      -> swap_fun01 A B C F $-> G.
  Proof.
    intro alpha.
    snapply Build_NatTrans.
    - intro b.
      snapply Build_NatTrans.
      + exact (fun a => alpha a b).
      + snapply Build_Is1Natural'.
        * intros a a' f.
          exact (fun01_2cell_at
            (isnat (alnat := is1natural_nattrans alpha) alpha f) b).
        * intros a a' f.
          exact (fun01_2cell_at
            (isnat_tr (alnat := is1natural_nattrans alpha) alpha f) b).
    - snapply Build_Is1Natural'.
      + intros b b' g a.
        exact (isnat (alnat := is1natural_nattrans (alpha a)) (alpha a) g).
      + intros b b' g a.
        exact (isnat_tr (alnat := is1natural_nattrans (alpha a)) (alpha a) g).
  Defined.

  Definition equiv_swap_fun01_hom
    (F : Fun01 A (Fun01 B C)) (G : Fun01 B (Fun01 A C))
    : opyon_0gpd (swap_fun01 A B C F) G
        $<~> opyon_0gpd F (swap_fun01_rev G).
  Proof.
    snapply cate_adjointify.
    - snapply Build_Fun01'.
      + exact (swap_fun01_hom_to F G).
      + exact (fun alpha beta p a b => p b a).
    - snapply Build_Fun01'.
      + exact (swap_fun01_hom_from F G).
      + exact (fun alpha beta p b a => p a b).
    - exact (fun alpha a b => Id _).
    - exact (fun alpha b a => Id _).
  Defined.

  Definition adjunction_swap_fun01
    : GpdAdjunction (swap_fun01 A B C) (swap_fun01 B A C).
  Proof.
    snapply Build_GpdAdjunction.
    - exact equiv_swap_fun01_hom.
    - intro G.
      snapply Build_Is1Natural.
      exact (fun F F' alpha beta a b => Id _).
    - intro F.
      snapply Build_Is1Natural.
      exact (fun G G' alpha beta b a => Id _).
  Defined.
End SwapAdjunction.

(** ** Pointwise limits and colimits *)

Definition haslimit_fun01
  (A B J : Type) `{IsGraph A, HasEquivs B, IsGraph J}
  `{!HasLimit B J}
  : HasLimit (Fun01 A B) J.
Proof.
  snapply Build_HasLimit.
  - exact (fun11_compose
      (fun11_fun01_postcomp (A := A) (cat_limit B J))
      (fun11_swap_fun01 J A B)).
  - rapply (gpd_adjunction_natequiv_left
      (fun11_compose (fun11_swap_fun01 A J B)
        (fun11_fun01_postcomp (A := A) (fun11_diagonal B J)))
      (fun11_diagonal (Fun01 A B) J)
      (fun11_compose
        (fun11_fun01_postcomp (A := A) (cat_limit B J))
        (fun11_swap_fun01 J A B))
      (natequiv_swap_fun01_diagonal A J B) _).
    rapply (gpd_adjunction_compose
        (Fun01 A B)
        (Fun01 A (Fun01 J B))
        (Fun01 J (Fun01 A B))
        (fun11_fun01_postcomp (A := A) (fun11_diagonal B J))
        (fun11_fun01_postcomp (A := A) (cat_limit B J))
        (fun11_swap_fun01 A J B)
        (fun11_swap_fun01 J A B) _ _).
    + exact (gpd_adjunction_postcomp B (Fun01 J B) A
        (fun11_diagonal B J) (cat_limit B J)
        (adjunction_cat_limit B J)).
    + exact (adjunction_swap_fun01 A J B).
Defined.

Definition hascolimit_fun01
  (A B J : Type) `{IsGraph A, HasEquivs B, IsGraph J}
  `{!HasColimit B J}
  : HasColimit (Fun01 A B) J.
Proof.
  snapply Build_HasColimit.
  - exact (fun11_compose
      (fun11_fun01_postcomp (A := A) (cat_colimit B J))
      (fun11_swap_fun01 J A B)).
  - rapply (gpd_adjunction_natequiv_right
      (fun11_compose
        (fun11_fun01_postcomp (A := A) (cat_colimit B J))
        (fun11_swap_fun01 J A B))
      (fun11_compose (fun11_swap_fun01 A J B)
        (fun11_fun01_postcomp (A := A) (fun11_diagonal B J)))
      (fun11_diagonal (Fun01 A B) J)
      (natequiv_swap_fun01_diagonal A J B) _).
    rapply (gpd_adjunction_compose
        (Fun01 J (Fun01 A B))
        (Fun01 A (Fun01 J B))
        (Fun01 A B)
        (fun11_swap_fun01 J A B)
        (fun11_swap_fun01 A J B)
        (fun11_fun01_postcomp (A := A) (cat_colimit B J))
        (fun11_fun01_postcomp (A := A) (fun11_diagonal B J)) _ _).
    + exact (adjunction_swap_fun01 J A B).
    + exact (gpd_adjunction_postcomp (Fun01 J B) B A
        (cat_colimit B J) (fun11_diagonal B J)
        (adjunction_cat_colimit B J)).
Defined.

(** ** Colimits commute with colimits *)

Section ColimitsCommute.
  Context (A I J : Type) `{HasEquivs A} `{IsGraph I} `{IsGraph J}.
  Context `{!HasColimit A I} `{!HasColimit A J}.

  Local Instance hascolimit_fun01_colimits_commute
    : HasColimit (Fun01 I A) J
    := hascolimit_fun01 I A J.

  Local Instance preservescolimits_cat_colimit
    : PreservesColimits (Fun01 I A) A J (cat_colimit A I)
    := preservescolimits_left_adjoint
      (Fun01 I A) A J
      (cat_colimit A I) (fun11_diagonal A I)
      (adjunction_cat_colimit A I).

  Definition equiv_colimit_colimit (X : Fun01 J (Fun01 I A))
    : cat_colimit A I
        (fun01_compose (cat_colimit A J) (swap_fun01 J I A X))
      $<~> cat_colimit A J (fun01_compose (cat_colimit A I) X)
    := equiv_preservescolimits X.
End ColimitsCommute.

(** ** The walking span *)

Inductive WalkingSpan :=
  | span_left
  | span_center
  | span_right.

Definition walking_span_hom (i j : WalkingSpan) : Type
  := match i, j with
     | span_center, span_left
     | span_center, span_right => Unit
     | _, _ => Empty
     end.

Global Instance isgraph_walking_span : IsGraph WalkingSpan
  := Build_IsGraph WalkingSpan walking_span_hom.

(** ** The span-colimit 3-by-3 lemma *)

Section PushoutThreeByThree.
  Context (A : Type) `{HasEquivs A}.
  Context `{!HasColimit A WalkingSpan}.

  (** A functor of this type is a 3-by-3 diagram in which every row and every column is a span.  The equivalence compares taking the three column pushouts and then their row pushout with taking the three row pushouts and then their column pushout. *)
  Definition equiv_span_colimit_3_by_3
    (X : Fun01 WalkingSpan (Fun01 WalkingSpan A))
    : cat_colimit A WalkingSpan
        (fun01_compose (cat_colimit A WalkingSpan)
          (swap_fun01 WalkingSpan WalkingSpan A X))
      $<~> cat_colimit A WalkingSpan
        (fun01_compose (cat_colimit A WalkingSpan) X)
    := equiv_colimit_colimit A WalkingSpan WalkingSpan X.
End PushoutThreeByThree.
