Require Import Basics.Overture Basics.Tactics.
Require Import WildCat.Core WildCat.Equiv WildCat.FunctorCat WildCat.NatTrans
  WildCat.TwoOneCat WildCat.Yoneda WildCat.ZeroGroupoid.
Require Import WildCat.TwoFunctor.
Require Import WildCat.PushoutScratch.

Set Typeclasses Depth 3.

(** * Scratch work on wild Kan extensions *)

(** We begin with a local left Kan extension relative to an already
    constructed restriction functor.  This separates the universal
    property from the particular coherent-functor category used to
    model diagrams. *)
Section LocalLeftKanExtension.

  Context {C D : Type} `{Is1Cat C} `{Is1Cat D}.
  Context (restriction : Fun11 D C).

  Definition left_kan_extension_map
    (F : C) (L : D) (eta : F $-> restriction L) (G : D)
    : opyon_0gpd L G $-> opyon_0gpd F (restriction G).
  Proof.
    snapply Build_Fun01'.
    - intro alpha.
      exact (fmap restriction alpha $o eta).
    - intros alpha beta p.
      exact (fmap2 restriction p $@R eta).
  Defined.

  (** The universal property is imposed on the canonical map above,
      not on an unrelated family of equivalences. *)
  Definition IsLeftKanExtension
    (F : C) (L : D) (eta : F $-> restriction L) : Type
    := forall G : D,
      CatIsEquiv (left_kan_extension_map F L eta G).

  Definition LeftKanExtension (F : C) : Type
    := {L : D &
        {eta : F $-> restriction L &
          IsLeftKanExtension F L eta}}.

  Definition equiv_left_kan_extension
    {F : C} {L : D} {eta : F $-> restriction L}
    (Heta : IsLeftKanExtension F L eta) (G : D)
    : opyon_0gpd L G $<~> opyon_0gpd F (restriction G).
  Proof.
    napply Build_CatEquiv.
    exact (Heta G).
  Defined.

  Definition HasLeftKanExtensions : Type
    := forall F : C, LeftKanExtension F.

End LocalLeftKanExtension.

(** ** Corepresentations *)

(** A local left Kan extension is a corepresentation of its
    0-groupoid of cocones.  It is useful to separate out this part of
    the definition: for pushouts, we already know the relevant
    corepresentability statement before identifying those cocones
    with morphisms in a coherent diagram category. *)
Section Corepresentation.

  Context {D : Type} `{Is1Cat D} (K : Fun11 D ZeroGpd).

  Definition corepresentation_map
    (L : D) (eta : K L) (G : D)
    : opyon_0gpd L G $-> K G
    := opyoneda_0gpd L K eta G.

  Definition IsCorepresentation (L : D) (eta : K L) : Type
    := forall G : D,
      CatIsEquiv (corepresentation_map L eta G).

  Definition Corepresentation : Type
    := {L : D & {eta : K L & IsCorepresentation L eta}}.

End Corepresentation.

Section LeftKanExtensionAsCorepresentation.

  Context {C D : Type} `{Is1Cat C} `{Is1Cat D}.
  Context (restriction : Fun11 D C) (F : C).

  Definition left_kan_cocones : Fun11 D ZeroGpd
    := fun11_compose (opyon1_0gpd F) restriction.

  Definition left_kan_extension_map_is_corepresentation
    (L : D) (eta : F $-> restriction L) (G : D)
    : left_kan_extension_map restriction F L eta G
      $== corepresentation_map left_kan_cocones L eta G.
  Proof.
    intro alpha.
    exact (Id _).
  Defined.

  Definition iscorepresentation_of_isleftkanextension
    {L : D} {eta : F $-> restriction L}
    (Heta : IsLeftKanExtension restriction F L eta)
    : IsCorepresentation left_kan_cocones L eta.
  Proof.
    intro G.
    napply (catie_homotopic
      (left_kan_extension_map restriction F L eta G)).
    { exact (Heta G). }
    exact (left_kan_extension_map_is_corepresentation L eta G).
  Defined.

  Definition isleftkanextension_of_iscorepresentation
    {L : D} {eta : F $-> restriction L}
    (Heta : IsCorepresentation left_kan_cocones L eta)
    : IsLeftKanExtension restriction F L eta.
  Proof.
    intro G.
    napply (catie_homotopic
      (corepresentation_map left_kan_cocones L eta G)).
    { exact (Heta G). }
    exact (left_kan_extension_map_is_corepresentation L eta G)^$.
  Defined.

End LeftKanExtensionAsCorepresentation.

(** ** Pushouts corepresent span cocones *)

Section PushoutCorepresentation.

  Context {A B C : Type} (f : A -> B) (g : A -> C).

  (** This is the Kan-style universal property of a proposed pushout
      cocone.  The functor being corepresented sends a type [P] to the
      0-groupoid of pairs of maps [B -> P] and [C -> P] commuting over
      [A]. *)
  Definition IsPushout
    {Q : Type} (q : PushoutRecData (P := Q) f g) : Type
    := IsCorepresentation (pushoutrecdata_0gpd_fun f g) Q q.

  Definition ispushout_pushout
    : IsPushout (pushoutrecdata_pushout f g).
  Proof.
    intro P.
    napply (catie_homotopic
      (pushout_rec_inv_natequiv f g P)).
    { exact _. }
    intro k.
    exact (Id _).
  Defined.

End PushoutCorepresentation.

(** ** Pasting local left Kan extensions *)

Section LeftKanExtensionCompose.

  Context {C D E : Type}
    `{Is1Cat C} `{Is1Cat D} `{Is1Cat E}.
  Context (pstar : Fun11 D C) (qstar : Fun11 E D).
  Context (F : C) (L : D) (M : E)
    (eta : F $-> pstar L) (mu : L $-> qstar M).

  Definition left_kan_extension_comp_unit
    : F $-> fun11_compose pstar qstar M
    := fmap pstar mu $o eta.

  (** Applying the two universal maps successively. *)
  Definition left_kan_extension_comp_map (G : E)
    : opyon_0gpd M G
      $-> opyon_0gpd F (fun11_compose pstar qstar G)
    := left_kan_extension_map pstar F L eta (qstar G)
      $o left_kan_extension_map qstar L M mu G.

  (** The successive map is the canonical map for the pasted unit,
      up to the compositor of [pstar] and associativity.  This is the
      calculation that makes the Kan-extension pasting argument work. *)
  Definition left_kan_extension_comp_map_is_canonical (G : E)
    : left_kan_extension_comp_map G
      $== left_kan_extension_map
        (fun11_compose pstar qstar)
        F M left_kan_extension_comp_unit G.
  Proof.
    intro alpha.
    exact ((fmap_comp pstar mu (fmap qstar alpha) $@R eta)
      $@ cat_assoc eta (fmap pstar mu)
        (fmap pstar (fmap qstar alpha))).
  Defined.

  Definition isleftkanextension_compose
    (Heta : IsLeftKanExtension pstar F L eta)
    (Hmu : IsLeftKanExtension qstar L M mu)
    : IsLeftKanExtension
      (fun11_compose pstar qstar)
      F M left_kan_extension_comp_unit.
  Proof.
    intro G.
    napply (catie_homotopic (left_kan_extension_comp_map G)).
    - napply compose_catie'.
      + exact (Heta (qstar G)).
      + exact (Hmu G).
    - exact (left_kan_extension_comp_map_is_canonical G).
  Defined.

End LeftKanExtensionCompose.

(** ** Restriction of coherent graph-indexed diagrams *)

Definition fun02_compose
  {I J A : Type} `{IsGraph I} `{IsGraph J} `{IsGraph A}
  (F : Fun02 J A) (u : Fun02 I J)
  : Fun02 I A.
Proof.
  napply Build_Fun02.
  exact (is0functor_compose u F).
Defined.

(** Reindexing a natural transformation only uses the action of the
    shape map on edges.  In particular, it does not require the
    intermediate shape to carry categorical structure. *)
Definition nattrans_prewhisker_fun02
  {I J A : Type} `{IsGraph I} `{IsGraph J} `{Is21Cat A}
  {F G : Fun02 J A} (alpha : F $-> G) (u : Fun02 I J)
  : fun02_compose F u $-> fun02_compose G u.
Proof.
  snapply Build_NatTrans.
  - exact (fun i => alpha (u i)).
  - snapply Build_Is1Natural'.
    + intros i i' f.
      exact (isnat alpha (fmap u f)).
    + intros i i' f.
      exact (isnat_tr alpha (fmap u f)).
Defined.

Definition natmod_prewhisker
  {I J A : Type} `{IsGraph I} `{IsGraph J} `{Is21Cat A}
  {F G : Fun02 J A} {alpha beta : F $-> G}
  (p : alpha $-> beta) (u : Fun02 I J)
  : nattrans_prewhisker_fun02 alpha u
    $-> nattrans_prewhisker_fun02 beta u.
Proof.
  snapply Build_NatModification.
  - exact (fun i => natmod_component alpha beta p (u i)).
  - intros i i' f.
    exact (natmod_isnatural alpha beta p (fmap u f)).
Defined.

Definition fun02_precompose
  {I J A : Type} `{IsGraph I} `{IsGraph J} `{IsGraph A}
  (u : Fun02 I J)
  : Fun02 J A -> Fun02 I A
  := fun F => fun02_compose F u.

Instance is0functor_fun02_precompose
  {I J A : Type} `{IsGraph I} `{IsGraph J} `{Is21Cat A}
  (u : Fun02 I J)
  : Is0Functor (fun02_precompose u).
Proof.
  snapply Build_Is0Functor.
  intros F G alpha.
  exact (nattrans_prewhisker_fun02 alpha u).
Defined.

Instance is1functor_fun02_precompose
  {I J A : Type} `{IsGraph I} `{IsGraph J} `{Is21Cat A}
  (u : Fun02 I J)
  : Is1Functor (fun02_precompose u).
Proof.
  snapply Build_Is1Functor.
  - intros F G alpha beta p.
    exact (natmod_prewhisker p u).
  - intro F.
    apply natmod_id.
  - intros F G K alpha beta.
    apply natmod_id.
Defined.

Definition fun11_fun02_precompose
  {I J A : Type} `{IsGraph I} `{IsGraph J} `{Is21Cat A}
  (u : Fun02 I J)
  : Fun11 (Fun02 J A) (Fun02 I A)
  := Build_Fun11 _ _ (fun02_precompose u).

(** A local left Kan extension along [u] is now obtained by
    specializing the abstract definition to
    [fun11_fun02_precompose u].  This graph-indexed experiment does
    not yet identify a terminal shape whose restriction is exactly
    the constant-diagram functor; resolving that is part of deciding
    whether the final formulation should use categorical shapes and
    genuine pseudofunctors. *)
