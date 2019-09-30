Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import HIT.Suspension.

Require Import Modalities.ReflectiveSubuniverse.
Require Import Modalities.Accessible.
Require Import Modalities.Localization.

Require Import HIT.Truncations.
Require Import HIT.Connectedness.

Require Import Small.

(* Import LocM. *)

(* In this file we follow the CORS paper. *)



(* We need to declare a module CORS in order to discuss ReflectiveSubuniverses. This can safely be ignored. What is going on under the hood is that we have modules floating around making our theory sufficiently polymorphic. This is all explained in Modalities.ReflectiveSubuniverses. *)
(* TODO: Rename *)
Module CORS (Ls : ReflectiveSubuniverses).

(* The following lets us use all the theory associated with a reflective subuniverse. *)
Import Ls.
Module Import Ls_theory := ReflectiveSubuniverses_Theory Ls.

Section foo.

  (* We assume function extensionality. The modalities library jumps through many hoops to avoid funext, but we will use it since CORS uses it. If this work is added to the main HoTT library, there ought to be an effort to cleanup the funext. *)
  Context `{Funext}.

  (* Let L be a reflective subuniverse. *)
  Context {L : ReflectiveSubuniverse}.

  (* An L-equivalence is a map which becomes an equivalence after applying the L-functor to it. In the library we call this O_inverts L f, which says f is an L-equivalence. *)
  (* We can check these here *)
  Section Check_L_equiv.
    Context {A B} {f : A -> B}.
    Check O_inverts L f.
    (* O_inverts L f : Type *)
    Eval cbn in (O_inverts L f).
    (* = O_inverts L f : Type *)
    Eval cbv in (O_inverts L f).
    (* = IsEquiv (fst (Ls.extendable_to_O L 1%nat) (fun x : A => to L B (f x))).1 : Type *)
  End Check_L_equiv.

  (* We can precompose maps in a commutative square to get another. *)
  Definition comm_square_precompose {A B C D} {f : A -> B} {g : B -> D}
    {h : A -> C} {i : C -> D} (sq : g o f == i o h) {E : Type}
    : (fun j : _ -> E => j o f) o (fun j : _ -> E => j o g)
    == (fun j : _ -> E => j o h) o (fun j : _ -> E => j o i).
  Proof.
    intro j.
    funext x.
    apply ap, sq.
  Defined.

  (* Lemma 2.9 *)
  Lemma lemma_2_9 {X Y : Type} (g : X -> Y)
    : O_inverts L g <~> (forall Z `{In L Z}, IsEquiv (fun h : Y -> Z => h o g)).
  Proof.
    (* We have an equivalence of hprops so we only need back and forth maps. *)
    serapply equiv_iff_hprop.
    (* ==> *)
    { intro lequiv_g.
      intros Z islocal_Z.
      unfold O_functor in lequiv_g.
      set (natsq := to_O_natural L g).
      
      
      serapply isequiv_compose'. 
    
    
    admit. }
    (* <== *)
    { admit. }
    
    

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



