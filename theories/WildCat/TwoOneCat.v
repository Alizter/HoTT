Require Import Basics.Overture Basics.Tactics.
Require Import WildCat.Core.
Require Import WildCat.NatTrans.
Require Import WildCat.Square.

(** * Wild (2,1)-categories *)

Class Is21Cat (A : Type) `{Is1Cat A, !Is3Graph A} :=
{
  is1cat_hom :: forall (a b : A), Is1Cat (a $-> b) ;
  is1gpd_hom :: forall (a b : A), Is1Gpd (a $-> b) ;
  is1functor_postcomp :: forall (a b c : A) (g : b $-> c), Is1Functor (cat_postcomp a g) ;
  is1functor_precomp :: forall (a b c : A) (f : a $-> b), Is1Functor (cat_precomp c f) ;
  bifunctor_coh_comp : forall {a b c : A} {f f' : a $-> b}  {g g' : b $-> c}
    (p : f $== f') (p' : g $== g'),
    (p' $@R f) $@ (g' $@L p) $== (g $@L p) $@ (p' $@R f') ;

  (** Naturality of the associator in each variable separately *)
  is1natural_cat_assoc_l :: forall (a b c d : A) (f : a $-> b) (g : b $-> c),
      Is1Natural (cat_precomp d f o cat_precomp d g) (cat_precomp d (g $o f))
                 (cat_assoc f g);
  is1natural_cat_assoc_m :: forall (a b c d : A) (f : a $-> b) (h : c $-> d),
      Is1Natural (cat_precomp d f o cat_postcomp b h) (cat_postcomp a h o cat_precomp c f)
                 (fun g => cat_assoc f g h);
  is1natural_cat_assoc_r :: forall (a b c d : A) (g : b $-> c) (h : c $-> d),
      Is1Natural (cat_postcomp a (h $o g)) (cat_postcomp a h o cat_postcomp a g)
                 (fun f => cat_assoc f g h);

  (** Naturality of the unitors *)
  is1natural_cat_idl :: forall (a b : A),
      Is1Natural (cat_postcomp a (Id b)) idmap
                 cat_idl ;

  is1natural_cat_idr :: forall (a b : A),
      Is1Natural (cat_precomp b (Id a)) idmap
                 cat_idr;

  (** The separately stored reverse associator is the inverse of the forward associator. *)
  cat_assoc_opp_is_rev : forall (a b c d : A)
      (f : a $-> b) (g : b $-> c) (h : c $-> d),
      cat_assoc_opp f g h $== (cat_assoc f g h)^$;

  (** Coherence *)
  cat_pentagon : forall (a b c d e : A)
                        (f : a $-> b) (g : b $-> c) (h : c $-> d) (k : d $-> e),
      (k $@L cat_assoc f g h) $o (cat_assoc f (h $o g) k) $o (cat_assoc g h k $@R f)
      $== (cat_assoc (g $o f) h k) $o (cat_assoc f g (k $o h)) ;

  cat_tril : forall (a b c : A) (f : a $-> b) (g : b $-> c),
      (g $@L cat_idl f) $o (cat_assoc f (Id b) g) $== (cat_idr g $@R f)
}.

(** TODO: Make these square-shaped statements the naturality fields of
    [Is21Cat], rather than recovering them from [Is1Natural]. *)
Lemma cat_assoc_natural_r {A : Type} `{Is21Cat A}
  {a b c d : A} {f f' : a $-> b} (p : f $== f')
  (g : b $-> c) (h : c $-> d)
  : Square
      (cat_assoc f g h) (cat_assoc f' g h)
      ((h $o g) $@L p) (h $@L (g $@L p)).
Proof.
  exact (isnat
    (alnat := is1natural_cat_assoc_r a b c d g h)
    (fun k => cat_assoc k g h) p).
Defined.

Lemma cat_assoc_natural_m {A : Type} `{Is21Cat A}
  {a b c d : A} (f : a $-> b)
  {g g' : b $-> c} (p : g $== g') (h : c $-> d)
  : Square
      (cat_assoc f g h) (cat_assoc f g' h)
      ((h $@L p) $@R f) (h $@L (p $@R f)).
Proof.
  exact (isnat
    (alnat := is1natural_cat_assoc_m a b c d f h)
    (fun k => cat_assoc f k h) p).
Defined.

Lemma cat_assoc_natural_l {A : Type} `{Is21Cat A}
  {a b c d : A} (f : a $-> b) (g : b $-> c)
  {h h' : c $-> d} (p : h $== h')
  : Square
      (cat_assoc f g h) (cat_assoc f g h')
      ((p $@R g) $@R f) (p $@R (g $o f)).
Proof.
  exact (isnat
    (alnat := is1natural_cat_assoc_l a b c d f g)
    (fun k => cat_assoc f g k) p).
Defined.

Lemma cat_idl_natural {A : Type} `{Is21Cat A}
  {a b : A} {f g : a $-> b} (p : f $== g)
  : Square
      (cat_idl f) (cat_idl g)
      (Id b $@L p) p.
Proof.
  exact (isnat
    (alnat := is1natural_cat_idl a b)
    cat_idl p).
Defined.

Lemma cat_idr_natural {A : Type} `{Is21Cat A}
  {a b : A} {f g : a $-> b} (p : f $== g)
  : Square
      (cat_idr f) (cat_idr g)
      (p $@R Id a) p.
Proof.
  exact (isnat
    (alnat := is1natural_cat_idr a b)
    cat_idr p).
Defined.

(** *** Whiskering functoriality *)

Definition cat_postwhisker_pp {A} `{Is21Cat A} {a b c : A}
  {f g h : a $-> b} (k : b $-> c) (p : f $== g) (q : g $== h)
  : k $@L (p $@ q) $== (k $@L p) $@ (k $@L q)
  := fmap_comp _ _ _.

Definition cat_prewhisker_pp {A} `{Is21Cat A} {a b c : A}
  {f g h : b $-> c} (k : a $-> b) (p : f $== g) (q : g $== h)
  : (p $@ q) $@R k $== (p $@R k) $@ (q $@R k)
  := fmap_comp _ _ _.

Lemma cat_idl_assoc {A : Type} `{Is21Cat A}
  {a b c : A} (k : a $-> b) (f : b $-> c)
  : cat_idl f $@R k
    $== cat_assoc k f (Id c) $@ cat_idl (f $o k).
Proof.
  (** Cancel the left unitor at the common source; its naturality reduces the comparison to postwhiskering both sides by [Id c]. *)
  apply (gpd_cancelR _ _
    (cat_idl ((Id c $o f) $o k))).
  lhs' exact (cat_idl_natural (cat_idl f $@R k))^$.
  rhs' exact (cat_idl_natural
    (cat_assoc k f (Id c) $@ cat_idl (f $o k)))^$.
  rapply cat_postwhisker.
  rhs' exact (cat_postwhisker_pp (Id c)
    (cat_assoc k f (Id c)) (cat_idl (f $o k))).
  (** Associator naturality and the triangle at [f $o k] expose the associators around the two unitors. *)
  lhs' exact (gpd_moveR_hV
    (cat_assoc_natural_m k (cat_idl f) (Id c)))^$.
  rhs' exact (gpd_moveL_hV
    (cat_tril (A := A) a c c (f $o k) (Id c))
      $@R (Id c $@L cat_assoc k f (Id c))).
  apply gpd_moveR_hV.
  (** Apply the triangle at [f], then use naturality of the associator in its final variable. *)
  lhs' exact (cat_assoc k f (Id c) $@L
    (fmap2 (cat_precomp c k)
      (gpd_moveL_hV
        (cat_tril (A := A) b c c f (Id c)))
    $@ cat_prewhisker_pp k
      (cat_assoc f (Id c) (Id c))^$
      (cat_idr (Id c) $@R f))).
  lhs' exact (cat_assoc_opp
    ((cat_assoc f (Id c) (Id c))^$ $@R k)
    ((cat_idr (Id c) $@R f) $@R k)
    (cat_assoc k f (Id c))).
  lhs' exact (cat_assoc_natural_l k f (cat_idr (Id c))
    $@R ((cat_assoc f (Id c) (Id c))^$ $@R k)).
  lhs' exact (cat_assoc
    ((cat_assoc f (Id c) (Id c))^$ $@R k)
    (cat_assoc k f (Id c $o Id c))
    (cat_idr (Id c) $@R (f $o k))).
  rhs' exact (cat_assoc
    (cat_assoc k (Id c $o f) (Id c))
    (Id c $@L cat_assoc k f (Id c))
    ((cat_idr (Id c) $@R (f $o k)) $o
      (cat_assoc (f $o k) (Id c) (Id c))^$)).
  rhs' exact (cat_assoc
    ((Id c $@L cat_assoc k f (Id c)) $o
      cat_assoc k (Id c $o f) (Id c))
    (cat_assoc (f $o k) (Id c) (Id c))^$
    (cat_idr (Id c) $@R (f $o k))).
  (** Cancel the common right unitor and use preservation of inverses by precomposition; the remaining boundary is the pentagon. *)
  rapply cat_postwhisker.
  lhs' exact (cat_assoc k f (Id c $o Id c) $@L
    gpd_1functor_V (cat_precomp c k)
      (cat_assoc f (Id c) (Id c))).
  apply gpd_moveR_hV.
  rhs' exact (cat_assoc
    (fmap (cat_precomp c k)
      (cat_assoc f (Id c) (Id c)))
    ((Id c $@L cat_assoc k f (Id c)) $o
      cat_assoc k (Id c $o f) (Id c))
    (cat_assoc (f $o k) (Id c) (Id c))^$).
  apply gpd_moveL_Vh.
  exact (cat_pentagon
    (A := A) a b c c c k f (Id c) (Id c))^$.
Defined.

Lemma cat_idr_assoc {A : Type} `{Is21Cat A}
  {a b c : A} (k : a $-> b) (h : b $-> c)
  : h $@L cat_idr k
    $== cat_assoc_opp (Id a) k h $@ cat_idr (h $o k).
Proof.
  (* Cancel the common right unitor and use its naturality to expose the associator boundary. *)
  apply (gpd_cancelR _ _
    (cat_idr (h $o (k $o Id a)))).
  lhs' exact (cat_idr_natural (h $@L cat_idr k))^$.
  rhs' exact (cat_idr_natural
    (cat_assoc_opp (Id a) k h $@ cat_idr (h $o k)))^$.
  rapply cat_postwhisker.
  rhs' exact (cat_prewhisker_pp (Id a)
    (cat_assoc_opp (Id a) k h) (cat_idr (h $o k))).
  lhs' exact (gpd_moveL_Vh
    (cat_assoc_natural_m (Id a) (cat_idr k) h)).
  rhs' exact ((cat_tril (A := A) a a c (Id a) (h $o k))^$
    $@R (cat_assoc_opp (Id a) k h $@R Id a)).
  (* Replace the stored opposite associator by the inverse of the forward associator before cancelling in the hom-groupoid. *)
  rhs' napply (fun p => cat_postwhisker (A := a $-> c)
    (a := (h $o (k $o Id a)) $o Id a)
    (b := ((h $o k) $o Id a) $o Id a)
    (c := (h $o k) $o Id a)
    (((h $o k) $@L cat_idl (Id a)) $o
      cat_assoc (Id a) (Id a) (h $o k)) p).
  2: exact (fmap2 (cat_precomp c (Id a))
      (cat_assoc_opp_is_rev a a b c (Id a) k h)).
  rhs' napply (fun p => cat_postwhisker (A := a $-> c)
    (a := (h $o (k $o Id a)) $o Id a)
    (b := ((h $o k) $o Id a) $o Id a)
    (c := (h $o k) $o Id a)
    (((h $o k) $@L cat_idl (Id a)) $o
      cat_assoc (Id a) (Id a) (h $o k)) p).
  2: exact (gpd_1functor_V (cat_precomp c (Id a))
      (cat_assoc (Id a) k h)).
  apply gpd_moveL_hV.
  lhs' exact (cat_assoc
    (fmap (cat_precomp c (Id a)) (cat_assoc (Id a) k h))
    ((h $@L (cat_idr k $@R Id a)) $o
      cat_assoc (Id a) (k $o Id a) h)
    (cat_assoc (Id a) k h)^$).
  lhs' exact ((cat_assoc (Id a) k h)^$ $@L cat_assoc
    (fmap (cat_precomp c (Id a)) (cat_assoc (Id a) k h))
    (cat_assoc (Id a) (k $o Id a) h)
    (h $@L (cat_idr k $@R Id a))).
  lhs' exact ((cat_assoc (Id a) k h)^$ $@L
    ((fmap2 (cat_postcomp a h)
        (cat_tril (A := A) a a b (Id a) k)^$
      $@ cat_postwhisker_pp h
        (cat_assoc (Id a) (Id a) k)
        (k $@L cat_idl (Id a)))
    $@R (cat_assoc (Id a) (k $o Id a) h $o
      fmap (cat_precomp c (Id a)) (cat_assoc (Id a) k h)))).
  lhs' exact (cat_assoc_opp
    (cat_assoc (Id a) (k $o Id a) h $o
      fmap (cat_precomp c (Id a)) (cat_assoc (Id a) k h))
    ((h $@L cat_assoc (Id a) (Id a) k) $@
      (h $@L (k $@L cat_idl (Id a))))
    (cat_assoc (Id a) k h)^$).
  lhs' exact (cat_assoc_opp
    (h $@L cat_assoc (Id a) (Id a) k)
    (h $@L (k $@L cat_idl (Id a)))
    (cat_assoc (Id a) k h)^$
    $@R (cat_assoc (Id a) (k $o Id a) h $o
      fmap (cat_precomp c (Id a)) (cat_assoc (Id a) k h))).
  lhs' exact (cat_assoc
    (cat_assoc (Id a) (k $o Id a) h $o
      fmap (cat_precomp c (Id a)) (cat_assoc (Id a) k h))
    (h $@L cat_assoc (Id a) (Id a) k)
    ((cat_assoc (Id a) k h)^$ $o
      (h $@L (k $@L cat_idl (Id a))))).
  lhs' exact (vinverse_square_gpd
    (cat_assoc_natural_r (cat_idl (Id a)) k h)
    $@R (h $@L cat_assoc (Id a) (Id a) k $o
      (cat_assoc (Id a) (k $o Id a) h $o
        fmap (cat_precomp c (Id a)) (cat_assoc (Id a) k h)))).
  lhs' exact (cat_assoc
    (h $@L cat_assoc (Id a) (Id a) k $o
      (cat_assoc (Id a) (k $o Id a) h $o
        fmap (cat_precomp c (Id a)) (cat_assoc (Id a) k h)))
    (cat_assoc (Id a $o Id a) k h)^$
    ((h $o k) $@L cat_idl (Id a))).
  (* What remains is precisely the pentagon with two identity edges. *)
  rapply cat_postwhisker.
  rapply gpd_moveR_Vh.
  lhs' exact (cat_assoc_opp
    (fmap (cat_precomp c (Id a)) (cat_assoc (Id a) k h))
    (cat_assoc (Id a) (k $o Id a) h)
    (h $@L cat_assoc (Id a) (Id a) k)).
  exact (cat_pentagon
    (A := A) a a a b c (Id a) (Id a) k h).
Defined.

(** The left and right unitors agree at an identity morphism. *)
Definition cat_idl_idr_id {A : Type} `{Is21Cat A} (a : A)
  : cat_idl (Id a) $== cat_idr (Id a).
Proof.
  pose (I := Id a).
  pose (l := cat_idl I).
  pose (r := cat_idr I).
  pose (l2 := cat_idl (I $o I)).
  pose (r2 := cat_idr (I $o I)).
  pose (assoc := cat_assoc I I I).
  assert (El : I $@L l $== l2).
  { apply (gpd_cancelL l (I $@L l) l2).
    exact (cat_idl_natural l). }
  assert (Ew : l $@R I $== r $@R I).
  { lhs' exact (cat_idl_assoc I I).
    lhs' exact (El^$ $@R assoc).
    exact (cat_tril (A := A) a a a I I). }
  apply (gpd_cancelR l r r2).
  exact ((cat_idr_natural l)^$
    $@ (r $@L Ew)
    $@ cat_idr_natural r).
Defined.

(** *** Exchange law *)

Definition cat_exchange {A : Type} `{Is21Cat A} {a b c : A}
  {f f' f'' : a $-> b} {g g' g'' : b $-> c}
  (p : f $== f') (q : f' $== f'') (r : g $== g') (s : g' $== g'')
  : (p $@ q) $@@ (r $@ s) $== (p $@@ r) $@ (q $@@ s).
Proof.
  unfold "$@@".
  (** We use the distributivity of [$@R] and [$@L] in a (2,1)-category (since they are functors) to see that we have the same data on both sides of the 3-morphism. *)
  nrefine ((_ $@L cat_prewhisker_pp _ _ _ ) $@ _).
  nrefine ((cat_postwhisker_pp _ _ _ $@R _) $@ _).
  (** Now we reassociate and whisker on the left and right. *)
  nrefine (cat_assoc _ _ _ $@ _).
  refine (_ $@ (cat_assoc _ _ _)^$).
  nrefine (_ $@L _).
  refine (_ $@ cat_assoc _ _ _).
  refine ((cat_assoc _ _ _)^$ $@ _).
  nrefine (_ $@R _).
  (** Finally we are left with the bifunctoriality condition for left and right whiskering which is part of the data of the (2,1)-cat. *)
  apply bifunctor_coh_comp.
Defined.

(** Horizontal composition with an identity 2-cell reduces to
    whiskering. *)
Definition cat_comp2_idr
  {A : Type} `{Is21Cat A} {a b c : A}
  {f f' : a $-> b} (p : f $== f') (g : b $-> c)
  : p $@@ Id g $== g $@L p.
Proof.
  unfold "$@@".
  lhs' exact ((g $@L p) $@L fmap_id (cat_precomp _ f) g).
  exact (cat_idr (g $@L p)).
Defined.

Definition cat_comp2_idl
  {A : Type} `{Is21Cat A} {a b c : A}
  (f : a $-> b) {g g' : b $-> c} (q : g $== g')
  : Id f $@@ q $== q $@R f.
Proof.
  unfold "$@@".
  lhs' exact (fmap_id (cat_postcomp _ g') f $@R (q $@R f)).
  exact (cat_idl (q $@R f)).
Defined.

Definition cat_comp2_homotopic_idr
  {A : Type} `{Is21Cat A} {a b c : A}
  {f f' : a $-> b} (p : f $== f') (g : b $-> c)
  {q : g $== g} (r : q $== Id g)
  : p $@@ q $== g $@L p.
Proof.
  unfold "$@@".
  lhs' exact ((g $@L p) $@L fmap2 (cat_precomp _ f) r).
  lhs' exact ((g $@L p) $@L fmap_id (cat_precomp _ f) g).
  exact (cat_idr (g $@L p)).
Defined.

Definition cat_comp2_homotopic_idl
  {A : Type} `{Is21Cat A} {a b c : A}
  (f : a $-> b) {p : f $== f} (r : p $== Id f)
  {g g' : b $-> c} (q : g $== g')
  : p $@@ q $== q $@R f.
Proof.
  unfold "$@@".
  lhs' exact (fmap2 (cat_postcomp _ g') r $@R (q $@R f)).
  lhs' exact (fmap_id (cat_postcomp _ g') f $@R (q $@R f)).
  exact (cat_idl (q $@R f)).
Defined.
