Require Import Basics.Overture Basics.Tactics.
Require Import WildCat.Core WildCat.Equiv WildCat.NatTrans WildCat.FunctorCat
  WildCat.Square WildCat.TwoOneCat.

(** * The wild (2,1)-category of 1-groupoids *)

Record OneGpd := {
  onegpd_carrier :> Type;
  isgraph_onegpd_carrier :: IsGraph onegpd_carrier;
  is2graph_onegpd_carrier :: Is2Graph onegpd_carrier;
  is01cat_onegpd_carrier :: Is01Cat onegpd_carrier;
  is1cat_onegpd_carrier :: Is1Cat onegpd_carrier;
  is0gpd_onegpd_carrier :: Is0Gpd onegpd_carrier;
  is1gpd_onegpd_carrier :: Is1Gpd onegpd_carrier;
}.

(** Morphisms are 1-functors, 2-morphisms are natural
    transformations, and 3-morphisms are pointwise 2-morphisms. *)
Instance isgraph_1gpd : IsGraph OneGpd
  := {| Hom A B := Fun11 (onegpd_carrier A) (onegpd_carrier B) |}.

(** Action of a morphism of 1-groupoids on a morphism. *)
Definition onegpd_fmap
  {A B : OneGpd} (F : A $-> B)
  {a b : A} (f : a $-> b)
  : F a $-> F b
  := fun11_fmap F f.

(** Inverse of a 2-cell in a 1-groupoid. *)
Definition onegpd_rev
  {A : OneGpd} {a b : A} (p : a $== b)
  : b $== a
  := p^$.


(** Vertical composition of 2-cells in a 1-groupoid. *)
Definition onegpd_comp
  {A : OneGpd} {a b c : A}
  (p : a $== b) (q : b $== c)
  : a $== c
  := p $@ q.

(** A 3-cell in a 1-groupoid. *)
Definition OneGpdHom
  {A : OneGpd} {a b : A} (p q : a $== b)
  : Type
  := p $== q.

Definition onegpd_hom_id
  {A : OneGpd} {a b : A} (p : a $== b)
  : OneGpdHom p p
  := Id p.

Definition onegpd_hom_comp
  {A : OneGpd} {a b : A} {p q r : a $== b}
  (h : OneGpdHom p q) (k : OneGpdHom q r)
  : OneGpdHom p r
  := h $@ k.

Definition onegpd_hom_rev
  {A : OneGpd} {a b : A} {p q : a $== b}
  (h : OneGpdHom p q)
  : OneGpdHom q p
  := h^$.

Definition onegpd_hom_prewhisker
  {A : OneGpd} {a b c : A}
  {p q : b $== c} (h : OneGpdHom p q) (k : a $== b)
  : OneGpdHom (onegpd_comp k p) (onegpd_comp k q)
  := h $@R k.

Definition onegpd_hom_postwhisker
  {A : OneGpd} {a b c : A}
  (k : b $== c) {p q : a $== b} (h : OneGpdHom p q)
  : OneGpdHom (onegpd_comp p k) (onegpd_comp q k)
  := k $@L h.

Definition onegpd_solve_inverse_left
  {A : OneGpd} {x y z : A}
  {p : x $== z} {q : z $== y} {r : x $== y}
  (h : OneGpdHom p (onegpd_comp r (onegpd_rev q)))
  : OneGpdHom q (onegpd_comp (onegpd_rev p) r)
  := gpd_solve_inverse_left h.

Definition onegpd_hom_assoc
  {A : OneGpd} {a b c d : A}
  (p : a $== b) (q : b $== c) (r : c $== d)
  : OneGpdHom
      (onegpd_comp (onegpd_comp p q) r)
      (onegpd_comp p (onegpd_comp q r)).
Proof.
  unfold OneGpdHom, onegpd_comp, gpd_comp.
  exact (cat_assoc_opp p q r).
Defined.

Definition onegpd_hom_assoc_opp
  {A : OneGpd} {a b c d : A}
  (p : a $== b) (q : b $== c) (r : c $== d)
  : OneGpdHom
      (onegpd_comp p (onegpd_comp q r))
      (onegpd_comp (onegpd_comp p q) r).
Proof.
  unfold OneGpdHom, onegpd_comp, gpd_comp.
  exact (cat_assoc p q r).
Defined.

Definition onegpd_hom_V_hh
  {A : OneGpd} {a b c : A}
  (f : b $== c) (g : a $== b)
  : OneGpdHom
      (onegpd_comp (onegpd_comp g f) (onegpd_rev f))
      g.
Proof.
  unfold OneGpdHom, onegpd_comp, onegpd_rev, gpd_comp.
  exact (gpd_V_hh f g).
Defined.

Global Instance reflexive_onegpdhom
  {A : OneGpd} {a b : A}
  : Reflexive (@OneGpdHom A a b)
  := onegpd_hom_id.

Global Instance transitive_onegpdhom
  {A : OneGpd} {a b : A}
  : Transitive (@OneGpdHom A a b)
  := @onegpd_hom_comp A a b.

Global Instance symmetric_onegpdhom
  {A : OneGpd} {a b : A}
  : Symmetric (@OneGpdHom A a b)
  := @onegpd_hom_rev A a b.

(** A morphism of 1-groupoids preserves squares. *)
Definition onegpd_fmap_square
  {A B : OneGpd} (F : A $-> B)
  {x00 x20 x02 x22 : A}
  {f : x00 $-> x20} {g : x02 $-> x22}
  {u : x00 $-> x02} {v : x20 $-> x22}
  (s : Square u v f g)
  : Square
      (onegpd_fmap F u) (onegpd_fmap F v)
      (onegpd_fmap F f) (onegpd_fmap F g)
  := fmap_square F s.

(** Action and coherence of a morphism of 1-groupoids on 2-cells. *)
Definition onegpd_fmap2
  {A B : OneGpd} (F : A $-> B)
  {a b : A} {f g : a $-> b} (p : f $== g)
  : OneGpdHom
      (onegpd_fmap F f)
      (onegpd_fmap F g).
Proof.
  exact (fmap2 F p).
Defined.

Definition onegpd_fmap_id
  {A B : OneGpd} (F : A $-> B) (a : A)
  : OneGpdHom
      (onegpd_fmap F (Id a))
      (Id (F a)).
Proof.
  exact (fmap_id F a).
Defined.

Definition onegpd_fmap_comp
  {A B : OneGpd} (F : A $-> B)
  {a b c : A} (f : a $-> b) (g : b $-> c)
  : OneGpdHom
      (onegpd_fmap F (g $o f))
      (onegpd_comp
        (onegpd_fmap F f)
        (onegpd_fmap F g)).
Proof.
  unfold OneGpdHom, onegpd_comp, gpd_comp.
  exact (fmap_comp F f g).
Defined.

Definition onegpd_fmap_rev
  {A B : OneGpd} (F : A $-> B)
  {a b : A} (p : a $== b)
  : OneGpdHom
      (onegpd_fmap F (onegpd_rev p))
      (onegpd_rev (onegpd_fmap F p))
  := gpd_1functor_V F p.

(** Naturality of a 2-cell between morphisms of 1-groupoids, exposed
    without unfolding the functor-category representation. *)
Definition onegpd_isnat
  {A B : OneGpd} {F G : A $-> B}
  (alpha : F $== G) {a b : A} (f : a $-> b)
  : OneGpdHom
      (onegpd_comp (onegpd_fmap F f) (alpha b))
      (onegpd_comp (alpha a) (onegpd_fmap G f)).
Proof.
  unfold OneGpdHom, onegpd_comp, gpd_comp.
  exact (isnat alpha f).
Defined.

Definition onegpd_isnat_tr
  {A B : OneGpd} {F G : A $-> B}
  (alpha : F $== G) {a b : A} (f : a $-> b)
  : OneGpdHom
      (onegpd_comp (alpha a) (onegpd_fmap G f))
      (onegpd_comp (onegpd_fmap F f) (alpha b)).
Proof.
  unfold OneGpdHom, onegpd_comp, gpd_comp.
  exact (isnat_tr alpha f).
Defined.

Instance is2graph_1gpd : Is2Graph OneGpd
  := fun A B => isgraph_fun11.

Instance is3graph_1gpd : Is3Graph OneGpd
  := fun A B => is2graph_fun11.

Instance is01cat_1gpd : Is01Cat OneGpd
  := {| Id A := fun11_id;
        cat_comp A B C G F := fun11_compose G F |}.

Instance is0functor_1gpd_postcomp
  (A B C : OneGpd) (G : B $-> C)
  : Is0Functor (cat_postcomp A G).
Proof.
  snapply Build_Is0Functor.
  intros F F' alpha.
  exact (nattrans_postwhisker G alpha).
Defined.

Instance is0functor_1gpd_precomp
  (A B C : OneGpd) (F : A $-> B)
  : Is0Functor (cat_precomp C F).
Proof.
  snapply Build_Is0Functor.
  intros G G' alpha.
  exact (nattrans_prewhisker alpha F).
Defined.

Definition cat_assoc_1gpd
  (A B C D : OneGpd)
  (F : A $-> B) (G : B $-> C) (H : C $-> D)
  : (H $o G) $o F $== H $o (G $o F).
Proof.
  snapply Build_NatTrans.
  1: intro a; exact (Id _).
  snapply Build_Is1Natural.
  intros a b f.
  exact (cat_idl _ $@ (cat_idr _)^$).
Defined.

Definition cat_assoc_opp_1gpd
  (A B C D : OneGpd)
  (F : A $-> B) (G : B $-> C) (H : C $-> D)
  : H $o (G $o F) $== (H $o G) $o F
  := nattrans_inverse_gpd (cat_assoc_1gpd A B C D F G H).

Definition cat_idl_1gpd
  (A B : OneGpd) (F : A $-> B)
  : Id B $o F $== F.
Proof.
  snapply Build_NatTrans.
  1: intro a; exact (Id _).
  snapply Build_Is1Natural.
  intros a b f.
  exact (cat_idl _ $@ (cat_idr _)^$).
Defined.

Definition cat_idr_1gpd
  (A B : OneGpd) (F : A $-> B)
  : F $o Id A $== F.
Proof.
  snapply Build_NatTrans.
  1: intro a; exact (Id _).
  snapply Build_Is1Natural.
  intros a b f.
  exact (cat_idl _ $@ (cat_idr _)^$).
Defined.

Instance is1cat_1gpd : Is1Cat OneGpd.
Proof.
  snapply Build_Is1Cat.
  - intros A B.
    exact is01cat_fun11.
  - intros A B.
    exact is0gpd_fun11.
  - exact is0functor_1gpd_postcomp.
  - exact is0functor_1gpd_precomp.
  - exact cat_assoc_1gpd.
  - exact cat_assoc_opp_1gpd.
  - exact cat_idl_1gpd.
  - exact cat_idr_1gpd.
Defined.

Instance is1functor_1gpd_postcomp
  (A B C : OneGpd) (G : B $-> C)
  : Is1Functor (cat_postcomp A G).
Proof.
  snapply Build_Is1Functor.
  - intros F F' alpha beta p a.
    exact (fmap2 G (p a)).
  - intros F a.
    exact (fmap_id G (F a)).
  - intros F F' F'' alpha beta a.
    exact (fmap_comp G (alpha a) (beta a)).
Defined.

Instance is1functor_1gpd_precomp
  (A B C : OneGpd) (F : A $-> B)
  : Is1Functor (cat_precomp C F).
Proof.
  snapply Build_Is1Functor.
  - intros G G' alpha beta p a.
    exact (p (F a)).
  - intros G a.
    exact (Id _).
  - intros G G' G'' alpha beta a.
    exact (Id _).
Defined.

Definition bifunctor_coh_comp_1gpd
  {A B C : OneGpd}
  {F F' : A $-> B} {G G' : B $-> C}
  (p : F $== F') (q : G $== G')
  : (q $@R F) $@ (G' $@L p)
    $== (G $@L p) $@ (q $@R F').
Proof.
  intro a.
  exact (isnat_tr q (p a)).
Defined.

Definition is1natural_cat_assoc_l_1gpd
  (A B C D : OneGpd) (F : A $-> B) (G : B $-> C)
  : Is1Natural
      (cat_precomp D F o cat_precomp D G)
      (cat_precomp D (G $o F))
      (cat_assoc F G).
Proof.
  snapply Build_Is1Natural.
  intros H H' alpha a.
  exact (cat_idl _ $@ (cat_idr _)^$).
Defined.

Definition is1natural_cat_assoc_m_1gpd
  (A B C D : OneGpd) (F : A $-> B) (H : C $-> D)
  : Is1Natural
      (cat_precomp D F o cat_postcomp B H)
      (cat_postcomp A H o cat_precomp C F)
      (fun G => cat_assoc F G H).
Proof.
  snapply Build_Is1Natural.
  intros G G' alpha a.
  exact (cat_idl _ $@ (cat_idr _)^$).
Defined.

Definition is1natural_cat_assoc_r_1gpd
  (A B C D : OneGpd) (G : B $-> C) (H : C $-> D)
  : Is1Natural
      (cat_postcomp A (H $o G))
      (cat_postcomp A H o cat_postcomp A G)
      (fun F => cat_assoc F G H).
Proof.
  snapply Build_Is1Natural.
  intros F F' alpha a.
  exact (cat_idl _ $@ (cat_idr _)^$).
Defined.

Definition is1natural_cat_idl_1gpd
  (A B : OneGpd)
  : Is1Natural
      (cat_postcomp A (Id B)) idmap
      cat_idl.
Proof.
  snapply Build_Is1Natural.
  intros F F' alpha a.
  exact (cat_idl _ $@ (cat_idr _)^$).
Defined.

Definition is1natural_cat_idr_1gpd
  (A B : OneGpd)
  : Is1Natural
      (cat_precomp B (Id A)) idmap
      cat_idr.
Proof.
  snapply Build_Is1Natural.
  intros F F' alpha a.
  exact (cat_idl _ $@ (cat_idr _)^$).
Defined.

Definition cat_assoc_opp_is_rev_1gpd
  (A B C D : OneGpd)
  (F : A $-> B) (G : B $-> C) (H : C $-> D)
  : cat_assoc_opp F G H $== (cat_assoc F G H)^$.
Proof.
  intro a.
  exact (Id _).
Defined.

Definition cat_pentagon_1gpd
  (A B C D E : OneGpd)
  (F : A $-> B) (G : B $-> C) (H : C $-> D) (K : D $-> E)
  : (K $@L cat_assoc F G H) $o
      cat_assoc F (H $o G) K $o
      (cat_assoc G H K $@R F)
    $== cat_assoc (G $o F) H K $o
      cat_assoc F G (K $o H).
Proof.
  intro a.
  change (((fmap K (Id (H (G (F a)))))
      $o (Id (K (H (G (F a)))))
      $o (Id (K (H (G (F a))))))
    $== ((Id (K (H (G (F a)))))
      $o (Id (K (H (G (F a))))))).
  exact (cat_assoc _ _ _
    $@ (_ $@L cat_idl _)
    $@ cat_idr _
    $@ fmap_id K _
    $@ (cat_idl _)^$).
Defined.

Definition cat_tril_1gpd
  (A B C : OneGpd) (F : A $-> B) (G : B $-> C)
  : (G $@L cat_idl F) $o cat_assoc F (Id B) G
    $== cat_idr G $@R F.
Proof.
  intro a.
  change ((fmap G (Id (F a))) $o (Id (G (F a)))
    $== Id (G (F a))).
  exact (cat_idr _ $@ fmap_id G _).
Defined.

Instance is21cat_1gpd : Is21Cat OneGpd.
Proof.
  snapply Build_Is21Cat.
  - intros A B.
    exact is1cat_fun11.
  - intros A B.
    exact is1gpd_fun11.
  - exact is1functor_1gpd_postcomp.
  - exact is1functor_1gpd_precomp.
  - exact @bifunctor_coh_comp_1gpd.
  - exact is1natural_cat_assoc_l_1gpd.
  - exact is1natural_cat_assoc_m_1gpd.
  - exact is1natural_cat_assoc_r_1gpd.
  - exact is1natural_cat_idl_1gpd.
  - exact is1natural_cat_idr_1gpd.
  - exact cat_assoc_opp_is_rev_1gpd.
  - exact cat_pentagon_1gpd.
  - exact cat_tril_1gpd.
Defined.

(** Equivalences of 1-groupoids are bi-invertible 1-functors. *)
Instance hasequivs_1gpd : HasEquivs OneGpd
  := cat_hasequivs OneGpd.
