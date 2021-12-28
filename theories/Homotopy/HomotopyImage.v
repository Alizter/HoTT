Require Import Basics Types WildCat.
Require Import HFiber.

Section SliceHom.

  Context {X : Type}.

  (** TODO: Generalize to generic wildcat? *)
  Definition SliceHom {A B : Type} (f : A $-> X) (g : B $-> X) : Type :=
    {m : A $-> B & f $== g o m}.

  Definition SliceHomPb {A U U' : Type} {i : A $-> U} {f : A $-> X} {m : U $-> X}
    (I : f $== m $o i) (m' : U' -> X)
    : SliceHom m m' -> SliceHom f m'
    := fun '(h; H) => (h $o i; I $@ (H $@R i)).

  Definition total_triangle (P Q : X -> Type)
    : (forall (x : X), P x -> Q x) -> SliceHom (@pr1 _ P) (@pr1 _ Q)
    := fun f => (functor_sigma idmap f; fun _ => idpath).

  Global Instance isequiv_total_triangle `{Funext} (P Q : X -> Type)
    : IsEquiv (total_triangle P Q).
  Proof.
    srapply isequiv_adjointify.
    - intros [f q] x p.
      refine (transport Q (q (x;p))^ _).
      apply pr2.
    - intros [f q].
      srapply path_sigma.
      + simpl.
        funext x.
        srapply path_sigma.
        1: rapply q.
        rapply transport_pV.
      + hnf. cbn.
        funext x.
        rewrite transport_forall_constant.
        rewrite transport_paths_FlFr.
        rewrite ap_const.
        rewrite (ap_compose _ pr1).
        rewrite ap_apply_l.
        rewrite eisretr.
        rewrite ap_pr1_path_sigma.
        apply concat_1p.
    - reflexivity.
  Defined.

  Lemma equiv_functor_SliceHom `{Funext}
    {A A' B B' : Type} {f : A $-> X} {g : B $-> X}
    {f' : A' $-> X} {g' : B' $-> X} (e : A <~> A') (e' : B <~> B') 
    (p : f $== f' o e) (q : g $== g' o e')
    : SliceHom f g <~> SliceHom f' g'.
  Proof.
    srapply equiv_functor_sigma'.
    { rapply equiv_functor_arrow'.
      1: symmetry.
      all: assumption. }
    intros k. simpl.
    srapply equiv_functor_forall'.
    1: by symmetry.
    intros a.
    specialize (p (e^-1 a)).
    specialize (q (k (e^-1 a))).
    simpl in *.
    unfold functor_forall.
    rapply equiv_concat_lr.
    1: refine (ap f' (eisretr e a)^ @ _); symmetry.
    all: assumption.
  Defined.

  Definition slicehom_to_functor_hfiber {A B : Type} (f : A -> X) (g : B -> X)
    : SliceHom f g -> forall (x : X), hfiber f x -> hfiber g x
    := fun '(h; H) x '(a; p) => (h a; (H a)^ @ p).

  Global Instance isequiv_slicehom_to_functor_hfiber `{Funext}
    {A B : Type} (f : A -> X) (g : B -> X)
    : IsEquiv (slicehom_to_functor_hfiber f g).
  Proof.
    srapply isequiv_commsq.
    9: srapply isequiv_inverse.
    9: srapply isequiv_total_triangle.
    5: srapply isequiv_idmap.
    1: srapply equiv_functor_SliceHom.
    1-4: symmetry.
    1,2: apply equiv_fibration_replacement.
    1,2: intros [k [x p]]; exact p.
    2: exact _.
    hnf.
    intros [k p].
    simpl.
    funext x [y q].
    unfold functor_sigma.
    unfold slicehom_to_functor_hfiber.
    unfold functor_forall.
    simpl.
    rewrite transport_sigma'.
    rewrite transport_paths_FFlr.
    rewrite ap_const.
    simpl.
    destruct q.
    srapply path_sigma.
    1: reflexivity.
    simpl.
    rewrite ?concat_1p.
    rewrite ?concat_p1.
    rewrite inv_pp.
    rewrite inv_V.
    reflexivity.
  Defined.

End SliceHom.

Section HImage.

  Context `{Funext} {X : Type}.

  (** Universal property of homotopy image *)
  Definition HImageUP {A U U' : Type} {i : A -> U} {f : A -> X} {m : U -> X}
    `{IsEmbedding m} (I : f == m o i) : Type
    := forall (m' : U' -> X), IsEquiv (SliceHomPb I m').

  Global Instance ishprop_himage_hom {A U : Type}
    (f : A -> X) (m : U -> X) `{IsEmbedding m}
    : IsHProp (SliceHom f m).
  Proof.
    srapply istrunc_isequiv_istrunc.
    4: srapply isequiv_inverse.
    4: rapply isequiv_slicehom_to_functor_hfiber.
    exact _.
  Defined.

End HImage.







