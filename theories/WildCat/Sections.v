Require Import Basics.Overture Basics.Tactics.
Require Import WildCat.Core WildCat.Cylinder WildCat.Equiv WildCat.FunctorCat
  WildCat.NatTrans WildCat.OneGroupoid WildCat.Square WildCat.TwoFunctor
  WildCat.TwoOneCat WildCat.TwoYoneda.

Set Typeclasses Depth 4.

(** * Coherent sections of graph-indexed families of 1-groupoids *)

(** A coherent section problem has a 1-groupoid of choices at every vertex and
    two functors from the endpoint choices to a 1-groupoid of compatibility
    data at every edge. *)
Record CoherentSectionData (I : Type) `{IsGraph I} := {
  cs_vertex : I -> OneGpd;
  cs_edge : forall {i i' : I}, (i $-> i') -> OneGpd;
  cs_left : forall {i i' : I} (f : i $-> i'),
    cs_vertex i $-> cs_edge f;
  cs_right : forall {i i' : I} (f : i $-> i'),
    cs_vertex i' $-> cs_edge f;
}.

Arguments cs_vertex {I _} S i : rename.
Arguments cs_edge {I _} S {i i'} f : rename.
Arguments cs_left {I _} S {i i'} f : rename.
Arguments cs_right {I _} S {i i'} f : rename.

(** A coherent section chooses an object at every vertex and a comparison map
    at every edge. *)
Record CoherentSection {I : Type} `{IsGraph I}
  (S : CoherentSectionData I) := {
  cs_component : forall i, cs_vertex S i;
  cs_isnatural : forall {i i' : I} (f : i $-> i'),
    cs_right S f (cs_component i') $-> cs_left S f (cs_component i)
}.

Arguments cs_component {I _ S} x i : rename.
Arguments cs_isnatural {I _ S} x {i i'} f : rename.

(** Morphisms of coherent sections consist of pointwise morphisms together
    with the corresponding cylinders over every edge. *)
Record CoherentSectionHom {I : Type} `{IsGraph I}
  {S : CoherentSectionData I} (x y : CoherentSection S) := {
  csh_component : forall i, cs_component x i $-> cs_component y i;
  csh_isnatural : forall {i i' : I} (f : i $-> i'),
    Square
      (fun11_fmap (cs_right S f) (csh_component i'))
      (fun11_fmap (cs_left S f) (csh_component i))
      (cs_isnatural x f)
      (cs_isnatural y f)
}.

Arguments csh_component {I _ S x y} p i : rename.
Arguments csh_isnatural {I _ S x y} p {i i'} f : rename.

Instance isgraph_coherent_section
  {I : Type} `{IsGraph I} (S : CoherentSectionData I)
  : IsGraph (CoherentSection S).
Proof.
  snapply Build_IsGraph.
  exact CoherentSectionHom.
Defined.

Definition coherent_section_id
  {I : Type} `{IsGraph I} {S : CoherentSectionData I}
  (x : CoherentSection S) : x $-> x.
Proof.
  snapply Build_CoherentSectionHom.
  - intro i. exact (Id _).
  - intros i i' f.
    exact (transpose
      ((cs_isnatural x f $@L fmap_id (cs_right S f) _)
        $@ cat_idr (cs_isnatural x f)
        $@ (cat_idl (cs_isnatural x f))^$
        $@ (fmap_id (cs_left S f) _ $@R cs_isnatural x f)^$)).
Defined.

Definition coherent_section_comp
  {I : Type} `{IsGraph I} {S : CoherentSectionData I}
  {x y z : CoherentSection S}
  (q : y $-> z) (p : x $-> y) : x $-> z.
Proof.
  snapply Build_CoherentSectionHom.
  - intro i. exact (csh_component q i $o csh_component p i).
  - intros i i' f.
    refine ((csh_isnatural p f $@v csh_isnatural q f) $@hL _ $@hR _).
    + exact (fmap_comp (cs_right S f)
        (csh_component p i') (csh_component q i')).
    + exact (fmap_comp (cs_left S f)
        (csh_component p i) (csh_component q i)).
Defined.

Instance is01cat_coherent_section
  {I : Type} `{IsGraph I} (S : CoherentSectionData I)
  : Is01Cat (CoherentSection S)
  := Build_Is01Cat _ _ coherent_section_id
      (fun x y z => @coherent_section_comp I _ S x y z).

Instance is2graph_coherent_section
  {I : Type} `{IsGraph I} (S : CoherentSectionData I)
  : Is2Graph (CoherentSection S).
Proof.
  intros x y.
  snapply Build_IsGraph.
  intros p q.
  exact (forall i, csh_component p i $== csh_component q i).
Defined.

Instance is1cat_coherent_section
  {I : Type} `{IsGraph I} (S : CoherentSectionData I)
  : Is1Cat (CoherentSection S).
Proof.
  snapply Build_Is1Cat.
  - intros x y.
    snapply Build_Is01Cat.
    + intros p i. exact (Id (csh_component p i)).
    + intros p q r h k i. exact (k i $@ h i).
  - intros x y.
    snapply Build_Is0Gpd.
    intros p q h i. exact ((h i)^$).
  - intros x y z q.
    snapply Build_Is0Functor.
    intros p r h i.
    exact (csh_component q i $@L h i).
  - intros x y z p.
    snapply Build_Is0Functor.
    intros q r h i.
    exact (h i $@R csh_component p i).
  - intros x y z w p q r i.
    exact (cat_assoc (csh_component p i)
      (csh_component q i) (csh_component r i)).
  - intros x y z w p q r i.
    exact (cat_assoc_opp (csh_component p i)
      (csh_component q i) (csh_component r i)).
  - intros x y p i. exact (cat_idl (csh_component p i)).
  - intros x y p i. exact (cat_idr (csh_component p i)).
Defined.

Instance is0gpd_coherent_section
  {I : Type} `{IsGraph I} (S : CoherentSectionData I)
  : Is0Gpd (CoherentSection S).
Proof.
  snapply Build_Is0Gpd.
  intros x y p.
  snapply Build_CoherentSectionHom.
  - intro i. exact ((csh_component p i)^$).
  - intros i i' f.
    refine ((vinverse_square_gpd (csh_isnatural p f)) $@hL _ $@hR _).
    + exact (gpd_1functor_V (cs_right S f) (csh_component p i')).
    + exact (gpd_1functor_V (cs_left S f) (csh_component p i)).
Defined.

Instance is1gpd_coherent_section
  {I : Type} `{IsGraph I} (S : CoherentSectionData I)
  : Is1Gpd (CoherentSection S).
Proof.
  snapply Build_Is1Gpd.
  - intros x y p i. exact (gpd_issect (csh_component p i)).
  - intros x y p i. exact (gpd_isretr (csh_component p i)).
Defined.

Definition coherent_sections_1gpd
  {I : Type} `{IsGraph I} (S : CoherentSectionData I) : OneGpd
  := Build_OneGpd (CoherentSection S) _ _ _ _ _ _.

Section HomCoherentSections.
  Context (I C : Type) `{IsGraph I, Is21Cat C}.

  (** The coherent-section presentation of transformations [P -> Q]. *)
  Definition hom_coherent_section_data
    (P Q : Fun02 I C) : CoherentSectionData I.
  Proof.
    snapply Build_CoherentSectionData.
    - exact (fun i => hom_1gpd (P i) (Q i)).
    - exact (fun i i' f => hom_1gpd (P i) (Q i')).
    - intros i i' f.
      exact (Build_Fun11 _ _ (cat_postcomp (P i) (fmap Q f))).
    - intros i i' f.
      exact (Build_Fun11 _ _ (cat_precomp (Q i') (fmap P f))).
  Defined.

  Definition coherent_section_of_nattrans
    {P Q : Fun02 I C} (alpha : P $-> Q)
    : CoherentSection (hom_coherent_section_data P Q).
  Proof.
    snapply Build_CoherentSection.
    - exact alpha.
    - exact (fun i i' f => isnat alpha f).
  Defined.

  Definition nattrans_of_coherent_section
    {P Q : Fun02 I C}
    (x : CoherentSection (hom_coherent_section_data P Q))
    : P $-> Q.
  Proof.
    snapply Build_NatTrans.
    - exact (cs_component x).
    - snapply Build_Is1Natural.
      exact (fun i i' f => cs_isnatural x f).
  Defined.

  Definition coherent_section_hom_of_natmod
    {P Q : Fun02 I C} {alpha beta : P $-> Q}
    (p : alpha $== beta)
    : coherent_section_of_nattrans alpha
      $-> coherent_section_of_nattrans beta.
  Proof.
    snapply Build_CoherentSectionHom.
    - exact (fun i => natmod_component alpha beta p i).
    - intros i i' f.
      exact (natmod_isnatural alpha beta p f).
  Defined.

  Definition natmod_of_coherent_section_hom
    {P Q : Fun02 I C}
    {x y : CoherentSection (hom_coherent_section_data P Q)}
    (p : x $-> y)
    : nattrans_of_coherent_section x
      $== nattrans_of_coherent_section y.
  Proof.
    snapply Build_NatModification.
    - exact (csh_component p).
    - exact (fun i i' f => csh_isnatural p f).
  Defined.

  Definition fun11_coherent_section_of_nattrans
    (P Q : Fun02 I C)
    : Fun11 (hom_1gpd P Q)
        (coherent_sections_1gpd (hom_coherent_section_data P Q)).
  Proof.
    snapply Build_Fun11.
    - exact coherent_section_of_nattrans.
    - snapply Build_Is0Functor.
      exact (fun alpha beta p => coherent_section_hom_of_natmod p).
    - snapply Build_Is1Functor.
      + intros alpha beta p q h i. exact (h i).
      + intros alpha i. exact (Id _).
      + intros alpha beta gamma p q i. exact (Id _).
  Defined.

  Definition fun11_nattrans_of_coherent_section
    (P Q : Fun02 I C)
    : Fun11
        (coherent_sections_1gpd (hom_coherent_section_data P Q))
        (hom_1gpd P Q).
  Proof.
    snapply Build_Fun11.
    - exact nattrans_of_coherent_section.
    - snapply Build_Is0Functor.
      exact (fun x y p => natmod_of_coherent_section_hom p).
    - snapply Build_Is1Functor.
      + intros x y p q h i. exact (h i).
      + intros x i. exact (Id _).
      + intros x y z p q i. exact (Id _).
  Defined.

  Definition coherent_section_nattrans_retr
    (P Q : Fun02 I C)
    : NatTrans
        (fun11_compose
          (fun11_coherent_section_of_nattrans P Q)
          (fun11_nattrans_of_coherent_section P Q))
        (Id (coherent_sections_1gpd
          (hom_coherent_section_data P Q))).
  Proof.
    snapply Build_NatTrans.
    - exact (fun x => coherent_section_id x).
    - snapply Build_Is1Natural.
      intros x y p i.
      exact (cat_idl (csh_component p i)
        $@ (cat_idr (csh_component p i))^$).
  Defined.

  Definition coherent_section_nattrans_sect
    (P Q : Fun02 I C)
    : NatTrans
        (fun11_compose
          (fun11_nattrans_of_coherent_section P Q)
          (fun11_coherent_section_of_nattrans P Q))
        (Id (hom_1gpd P Q)).
  Proof.
    snapply Build_NatTrans.
    - intro alpha.
      snapply Build_NatModification.
      + intro i. exact (Id _).
      + intros i i' f. apply cylinder_refl.
    - snapply Build_Is1Natural.
      intros alpha beta p i.
      exact (cat_idl (natmod_component alpha beta p i)
        $@ (cat_idr (natmod_component alpha beta p i))^$).
  Defined.

  (** Natural transformations are equivalent, as a 1-groupoid, to their
      coherent-section presentation. *)
  Definition catie_coherent_section_of_nattrans
    (P Q : Fun02 I C)
    : @Cat_IsBiInv OneGpd isgraph_1gpd is2graph_1gpd
        is01cat_1gpd is1cat_1gpd
        (hom_1gpd P Q)
        (coherent_sections_1gpd (hom_coherent_section_data P Q))
        (fun11_coherent_section_of_nattrans P Q).
  Proof.
    snapply Build_Cat_IsBiInv.
    - exact (fun11_nattrans_of_coherent_section P Q).
    - exact (coherent_section_nattrans_retr P Q).
    - exact (fun11_nattrans_of_coherent_section P Q).
    - exact (coherent_section_nattrans_sect P Q).
  Defined.
End HomCoherentSections.
