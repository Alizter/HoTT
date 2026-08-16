Require Import Basics.Overture Basics.Tactics.
Require Import WildCat.Core WildCat.EquivGpd WildCat.FunctorCat
  WildCat.NatTrans WildCat.Opposite WildCat.Yoneda
  WildCat.ZeroGroupoid.

Set Typeclasses Depth 3.

(** * Limits in wild categories *)

(** This file starts from specified universal cones.  The basic definitions
    only concern graph-shaped diagrams in a wild 1-category; higher coherence
    assumptions belong on later results that retain higher cells. *)

(** ** The diagonal functor *)

Section Diagonal.
  Context (A J : Type) `{Is1Cat A, IsGraph J}.

  Definition diagonal : A -> Fun01 J A
    := fun a => Build_Fun01 (fun _ => a).

  Global Instance is0functor_diagonal : Is0Functor diagonal.
  Proof.
    snapply Build_Is0Functor.
    intros a b f.
    snapply Build_NatTrans.
    - exact (fun _ => f).
    - snapply Build_Is1Natural.
      intros i j g.
      exact (cat_idr _ $@ (cat_idl _)^$).
  Defined.

  Global Instance is1functor_diagonal : Is1Functor diagonal.
  Proof.
    snapply Build_Is1Functor.
    - exact (fun a b f g p _ => p).
    - intros a i; reflexivity.
    - intros a b c f g i; reflexivity.
  Defined.

  Definition fun11_diagonal : Fun11 A (Fun01 J A)
    := Build_Fun11 _ _ diagonal.
End Diagonal.

(** ** Cones *)

(** The 0-groupoid of cones from [a] to [X].  It is contravariant in
    [a], by precomposition with constant natural transformations. *)
Definition cone_0gpd
  {A J : Type} `{Is1Cat A, IsGraph J}
  (X : Fun01 J A) : A^op -> ZeroGpd
  := yon_0gpd X o diagonal A J.

Global Instance is0functor_cone_0gpd
  {A J : Type} `{Is1Cat A, IsGraph J}
  (X : Fun01 J A)
  : Is0Functor (cone_0gpd X)
  := is0functor_compose
      (A := A^op) (B := (Fun01 J A)^op) (C := ZeroGpd)
      (diagonal A J) (yon_0gpd X).

Global Instance is1functor_cone_0gpd
  {A J : Type} `{Is1Cat A, IsGraph J}
  (X : Fun01 J A)
  : Is1Functor (cone_0gpd X)
  := is1functor_compose
      (A := A^op) (B := (Fun01 J A)^op) (C := ZeroGpd)
      (diagonal A J) (yon_0gpd X).

(** A specified cone induces a functor from maps into its apex to cones.
    The source and target 0-groupoids can live in different universes, so this
    is deliberately a heterogeneous [Fun01], rather than a morphism in one
    fixed universe of bundled [ZeroGpd]s. *)
Definition limit01_cone_map
  {A J : Type} `{Is1Cat A, IsGraph J}
  (X : Fun01 J A) (l : A)
  (cone : diagonal A J l $-> X) (a : A)
  : Fun01 (yon_0gpd l a) (cone_0gpd X a).
Proof.
  snapply Build_Fun01'.
  - intro k.
    change (a $-> l) in k.
    exact (cone $o fmap (diagonal A J) k).
  - intros k k' p j.
    change (a $-> l) in k, k'.
    change (k $== k') in p.
    exact (cone j $@L p).
Defined.

(** ** 0-coherent graph limits *)

(** This is the representability notion for [Fun01] diagrams and
    0-groupoids of cones.  A [Fun01] has no compositor or unitor data, and its
    transformations have no identity/composition coherence, so this is not a
    lax limit in the standard 2-categorical sense when the source has
    composition.  It is the appropriate graph-shaped cone notion; for
    discrete shapes it specializes to the expected 1-categorical limit.
    It is intentionally not called [Limit], since a pseudofunctor bilimit
    needs a more coherent cone mapping object. *)
Class Limit01
  (J : Type) {A : Type} `{IsGraph J, Is1Cat A}
  (X : Fun01 J A) := Build_Limit01' {
  cat_limit01 : A;
  cat_limit01_cone : diagonal A J cat_limit01 $-> X;
  cat_issurjinj_limit01_cone_map
    :: forall a : A,
      IsSurjInj
        (limit01_cone_map X cat_limit01 cat_limit01_cone a);
}.

(** Unicity for this structure is to be stated as an equivalence of
    universal cones, whose apex component is a categorical equivalence in
    [A].  It must not be converted to equality using [Funext] or univalence. *)

Arguments cat_limit01 J {A _ _ _ _ _} X {limit} : rename.
