Require Import Basics Types WildCat.
Require Import Geometry.Site.
Require Import Limits.Pullback.
Require Import HIT.Coeq.
Require Import Cubical.
Require Import Truncations.

Section PSh.

  Definition PSh (C : Type) `{Is1Cat C} := Fun11 C^op hSet.

  Context {CC : Type} `{Is1Cat CC}.

  (** The category Fun11 C^op Type has pullbacks computed pointwise *)

  Definition PreSheafPullback {A B C : PSh CC}
    (f : A $-> B) (g : C $-> B) : PSh CC.
  Proof.
    snrapply Build_Fun11.
    { intro X.
      snrapply BuildhSet.
      1: exact (Pullback (nattrans_trans f X) (nattrans_trans  g X)).
      exact _. }
    { snrapply Build_Is0Functor.
      intros X Y n.
      nrapply functor_pullback.
      1: exact (isnat f n).
      exact (isnat g n). }
    snrapply Build_Is1Functor.
    { intros X Y h i p.
      intros [x [y q]].
      snrapply equiv_path_pullback.
      snrefine (_;_;_); simpl.
      1: exact (fmap2 A p _).
      1: exact (fmap2 C p _).
      (** Notice that extra coherence is needed here. But since we are in a hset we can ignore it. *)
      snrapply equiv_sq_path.
      snrapply path_ishprop.
      exact _. }
    { intros X [x [y q]].
      snrapply equiv_path_pullback.
      snrefine (_;_;_); simpl.
      1: exact (fmap_id A _ _).
      1: exact (fmap_id C _ _).
      snrapply equiv_sq_path.
      snrapply path_ishprop.
      exact _. }
    intros X Y Z h i [x [y q]].
    snrapply equiv_path_pullback.
    snrefine (_;_;_); simpl.
    1: exact (fmap_comp A _ _ _).
    1: exact (fmap_comp C _ _ _).
    snrapply equiv_sq_path.
    snrapply path_ishprop.
    exact _.
  Defined.

  (** The coequalizer of presheaves *)
  Definition PreSheafCoeq {A B : PSh CC} (f g : A $-> B) : PSh CC.
  Proof.
    snrapply Build_Fun11.
    { intro X.
      snrapply BuildhSet.
      (** The coequalizer in hset is the truncated coequalizer *)
      1: exact (Tr 0 (Coeq (nattrans_trans f X) (nattrans_trans g X))).
      exact _. }
    { snrapply Build_Is0Functor.
      intros X Y n.
      snrapply Trunc_functor.
      nrapply functor_coeq.
      1: symmetry; exact (isnat f n).
      symmetry; exact (isnat g n). }
    snrapply Build_Is1Functor.
    { intros X Y h i p.
      snrapply O_functor_homotopy.
      snrapply functor_coeq_homotopy.
      1: exact (fmap2 A p).
      1: exact (fmap2 B p).
      1,2: intro; rapply path_ishprop. }
    { intros X.
      srapply Trunc_ind.
      snrapply Coeq_ind.
      2: intro; rapply path_ishprop.
      intro a.
      apply (ap (tr o coeq)).
      rapply (fmap_id B). }
    intros X Y Z h i.
    srapply Trunc_ind.
    snrapply Coeq_ind.
    2: intro; rapply path_ishprop.
    intro a.
    apply (ap (tr o coeq)).
    rapply (fmap_comp B).
  Defined.

  Definition PreSheafCoeq_rec {A B : PSh CC} (P : PSh CC) (f g : A $-> B)
    (h : B $-> P) (p : h $o f $== h $o g)
    : PreSheafCoeq f g $-> P.
  Proof.
    snrapply Build_NatTrans.
    { intros X.
      snrapply Trunc_rec; [exact _ |].
      snrapply Coeq_rec.
      1: exact (nattrans_trans h X).
      exact (p X). }
    snrapply Build_Is1Natural.
    intros X Y k.
    srapply Trunc_ind.
    srapply Coeq_ind.
    1: intro x; exact (isnat h k x).
    intro b.
    apply path_ishprop.
  Defined.

  (** We now require some stronger conditions on CC. This makes CC into a standard categry. *)
  Context `{!HasMorExt CC} {K : forall x y, IsHSet (x $-> y)}.

  (** Yoneda embedding for hsets *)
  Definition hset_yon : CC -> PSh CC.
  Proof.
    intro X.
    snrapply Build_Fun11.
    { intro Y.
      snrapply BuildhSet.
      { revert Y.
        exact (yon X). }
      apply K. }
    { snrapply Build_Is0Functor.
      intros a b.
      exact (fmap (yon X)). }
    snrapply Build_Is1Functor.
    { intros a b f g p x.
      apply path_hom.
      simpl.
      apply cat_postwhisker, p. }
    { intros a f.
      apply path_hom.
      simpl.
      apply cat_idr. }
    intros a b c f g h.
    apply path_hom.
    apply cat_assoc.
  Defined.

  Global Instance is0functor_hset_yon : Is0Functor hset_yon.
  Proof.
  Admitted.

  Global Instance is1functor_hset_yon : Is1Functor hset_yon.
  Proof.
  Admitted.

  Definition PreSheafCoproduct {I : Type} `{IsHSet I}
    (X : I -> PSh CC) : PSh CC.
  Proof.
    snrapply Build_Fun11.
    { intro Y.
      snrapply BuildhSet.
      1: exact {i : I & X i Y}.
      exact _. }
    { snrapply Build_Is0Functor.
      intros Y Z f.
      snrapply (functor_sigma idmap).
      intro i.
      exact (fmap (X i) f). }
    snrapply Build_Is1Functor.
    { intros Y Z f g p [i x].
      snrapply path_sigma.
      1: reflexivity.
      exact (fmap2 (X i) p x). }
    { intros Y [i x].
      snrapply path_sigma.
      1: reflexivity.
      exact (fmap_id (X i) _ x). }
    intros W Y Z f g [i x].
    snrapply path_sigma.
    1: reflexivity.
    exact (fmap_comp (X i) _ _ x).
  Defined.

  Definition PreSheafCoproduct_rec {I : Type} `{IsHSet I}
    (X : I -> PSh CC) (P : PSh CC) (f : forall i, X i $-> P)
    : PreSheafCoproduct X $-> P.
  Proof.
    snrapply Build_NatTrans.
    { intros Y [i x].
      exact (nattrans_trans (f i) _ x). }
    snrapply Build_Is1Natural.
    intros Y Z g [i x].
    exact (isnat (f i) g x).
  Defined.

  (** We could actually define this to be a functor but that doesn't seem important right now. *)
  Definition functor_presheafcoproduct {I J : hSet}
    (X : I -> PSh CC) (Y : J -> PSh CC)
    (h : I -> J) (f : forall i, X i $-> Y (h i))
    : PreSheafCoproduct X $-> PreSheafCoproduct Y.
  Proof.
    snrapply Build_NatTrans.
    { intro Z; cbn.
      nrapply (functor_sigma h).
      intro i.
      exact (nattrans_trans (f i) Z). }
    snrapply Build_Is1Natural.
    intros U V r.
    intros [i x].
    snrapply path_sigma.
    1: reflexivity.
    exact (isnat (nattrans_trans (f i)) r x).
  Defined.

End PSh.

