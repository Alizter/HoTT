Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import HIT.Suspension.

Require Import Modalities.Accessible.
Require Import Modalities.Localization.

Import LocM.

Section Foo.

  Definition susp_functor {A B} (f : A -> B) : Susp A -> Susp B
    := Susp_rec North South (merid o f).

  Definition LocGenSusp (f : LocalGenerators) : LocalGenerators :=
  {|
      lgen_indices := lgen_indices f;
      lgen_domain := Susp o (lgen_domain f);
      lgen_codomain := Susp o (lgen_codomain f);
      lgenerator := fun i : lgen_indices f => susp_functor (f i)
  |}.

  Class IsPointedLocGen (f : LocalGenerators) := {
    ispointed_lgen_domain : forall i, IsPointed (lgen_domain f i);
    ispointed_lgen_codomain : forall i, IsPointed (lgen_codomain f i);
    ispmap_lgenerator : forall i,
      (lgenerator f i) (ispointed_lgen_domain i) = (ispointed_lgen_codomain i)
  }.

  Local Open Scope pointed_scope.

  Global Instance ispointed_localize {X} (f : LocalGenerators) `(IsPointed X)
    : IsPointed (Localize f X).
  Proof.
    by apply loc.
  Defined.

  Definition pLocalize (f : LocalGenerators) (X : pType) : pType
    := Build_pType (Localize f X) _.

  Definition cor_3_5 (f : LocalGenerators) (X : pType)
    : loops (pLocalize (LocGenSusp f) X) <~> Localize f (loops X).
  Proof.
    symmetry.
    IsLocal
  
    serapply equiv_adjointify.
    { admit. }
    { apply Localize_ind.
      { intro p.
        refine (ap _ _).
        refine (ap _ _).
        apply p. }
      destruct f as [I A B f].
      intros i n.
      induction n.
      { exact tt. }
      simpl in IHn.
      simpl.
      split.
      { intros g g'.
        srefine (_;_).
        { intro.
          apply g'.
      
      .



