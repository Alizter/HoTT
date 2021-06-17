Require Import Basics.
From HoTT.WildCat Require Import
  Core NatTrans Equiv Prod Opposite Yoneda.
Require Import WildCat.Type. (** Coq Bug ! *)

Generalizable Variables C D F G.

(** ** Notions of adjunctions in wild categories. *)

(** We try to capture a wild notion of (oo,1)-adjunctions since these are the ones that commonly appear in practice. Special cases include the standard 1-categorical adjunction.

There are notions of 2-adjunction/biadjunction/higher adjunction but it is not clear if this generality is useful.

We will define an adjunction to be an equivalence (in Type) between corresponding hom-types. This is a more immediately useful definition than others we can consider.

We should also be able to define "F having a left adjoint" as the initial object of a slice category C / F. However this seems like too much work for now, and it is not immediately obvious how it ties back to the adjunction isomorphism.
*)

Definition Adjunction {C D : Type} (F : C -> D) (G : D -> C)
  `{Is1Cat C, Is1Cat D, !Is0Functor F, !Is0Functor G}
  : Type.
Proof.
  refine (
  NatEquiv
    (
    (uncurry Hom
      : D^op * D -> Type)
    o (prod_functor F idmap
      : C^op * D -> D^op * D)
    : C^op * D -> Type
    )
    ( (uncurry Hom : C^op * C -> Type)
    o (prod_functor idmap G : C^op * D -> C^op * C)
    : C^op * D -> Type)).
  1: exact _.
  1,2: rapply is0functor_compose.
  2,4: rapply is0functor_hom.
  1,2: rapply is0functor_prod_functor.
  rapply is0functor_op.
Defined.

(** We can derive equivalences natural in each variable seperately. *)

Lemma natequiv_adj_left {C D : Type} (F : C -> D) (G : D -> C) 
  `{Is1Cat C, Is1Cat D, !Is0Functor F, !Is0Functor G,
    !Is1Functor G, !HasMorExt C, !HasMorExt D}
    (adj : Adjunction F G) (x : D)
  : 
  let Fop := F : C^op -> D^op in
  let h := @is0functor_op C _ _ D _ _ F _ : Is0Functor Fop in
  NatEquiv
      (yon x o Fop)
      (yon (G x)).
Proof.
  snrapply Build_NatEquiv.
  { intros y.
    exact (adj (y , x)). }
  intros y y' f z.
  simpl.
  refine (ap _ _ @ _).
  { rapply path_hom.
    symmetry.
    etransitivity.
    2: rapply cat_idl.
    apply cat_assoc. }
  refine (is1natural_natequiv _ _ adj (y,x) (y',x) (f,Id _) z @ _).
  simpl; rapply path_hom.
  refine (cat_assoc _ _ _ $@ (_ $@R _) $@ cat_idl _).
  rapply fmap_id.
Defined.

Lemma natequiv_adj_right {C D : Type} (F : C -> D) (G : D -> C) 
  `{Is1Cat C, Is1Cat D, !Is0Functor F, !Is0Functor G,
    !Is1Functor F, !HasMorExt C, !HasMorExt D}
    (adj : Adjunction F G) (x : C)
  : NatEquiv (opyon (F x)) (opyon x o G).
Proof.
  snrapply Build_NatEquiv.
  { intros y.
    exact (adj (x , y)). }
  intros y y' f z.
  simpl.
  refine (ap _ _ @ _).
  { rapply path_hom.
    symmetry.
    etransitivity.
    2: rapply cat_idr.
    refine (_ $@L _).
    rapply fmap_id. }
  refine (is1natural_natequiv _ _ adj (x,y) (x,y') (Id _,f) z @ _).
  simpl; rapply path_hom.
  apply cat_idr.
Defined.
