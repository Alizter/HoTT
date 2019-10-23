Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import PointedCategory.Functor.
Require Import PointedCategory.Profunctor.
Require Import PointedCategory.pMapFunctor.

Local Open Scope pointed_scope.

Class IsNatural {F G : pType -> pType}
   `{IsFunctor F} `{IsFunctor G}
  (P : forall (X : pType), F X ->* G X) := {
  natsquare {A B : pType} (f : A ->* B)
    : P B o* F_functor _ f ==* F_functor _ f o* P A;
}.

Section NaturalTransformationProperties.

  Context
    {F G H : pType -> pType}
   `{IsFunctor F} `{IsFunctor G} `{IsFunctor H}.

  Global Instance isnatural_compose
    (P : forall (X : pType), F X ->* G X) {nP : IsNatural P}
    (Q : forall (X : pType), G X ->* H X) {nQ : IsNatural Q}
    : IsNatural (fun X => Q X o* P X).
  Proof.
    serapply Build_IsNatural.
    intros A B f.
    destruct nP as [nP'], nQ as [nQ'].
    assert (nP := nP' A B f); clear nP'.
    assert (nQ := nQ' A B f); clear nQ'.
    refine (pmap_compose_assoc _ _ _ @* _).
    refine (pmap_postwhisker _ nP @* _).
    refine ((pmap_compose_assoc _ _ _)^* @* _).
    refine (pmap_prewhisker _ nQ @* _).
    apply pmap_compose_assoc.
  Defined.

End NaturalTransformationProperties.

Class NaturalTransformation (F G : Functor) := {
  nt_component : forall (X : pType), F X ->* G X;
  nt_isnatural :> IsNatural nt_component;
}.

Coercion nt_component : NaturalTransformation >-> Funclass.

Global Instance nt_compose {F G H : Functor}
  (P : NaturalTransformation F G)
  (Q : NaturalTransformation G H)
  : NaturalTransformation F H
  := Build_NaturalTransformation _ _ _ (isnatural_compose P Q).

Class NaturalEquivalence (F G : Functor) := {
  ne_component (X : pType) : F X <~>* G X;
  ne_isnatural :> IsNatural ne_component;
}.

Coercion ne_component : NaturalEquivalence >-> Funclass.


(** * Yoneda lemma *)
(** The Yoneda lemma comes in 3 parts. Firstly we show that natural equivalences between the hom functor hom(a,-) and a given functor F is equivalent to the functor F evaluated at a.

The second and third parts are showing that this equivalence is natural in a and F. *)

(* TODO: rename *)
Lemma yoneda (F : Functor) (a : pType)
  : NaturalTransformation (functor_pmap a) F <~> F a.
Proof.
Admitted.
(* 
Lemma yoneda_nat_a (F : Functor) {a b : pType} (f : a ->* b) : Type. 
Proof.
  serapply @natsquare.

F_functor (F:=functor_pmap a) f (functor_pmap a)

(* This equivalence is natural in F *)
Lemma yoneda_nat_F {F G : Functor} (phi_F : NaturalTransformation F G)
  (a : pType) : 
 *)
Theorem pYoneda {A B : pType}
  : NaturalEquivalence (functor_pmap B) (functor_pmap A) <~> (A <~>* B).
Proof. Admitted. (*
  Arguments F_functor _ {_ _ _}.
(*   Arguments functor _ _ : clear implicits. *)
  serapply equiv_adjointify.
  { intros [h [h_nat]].
    set (yB := functor_pmap B) in *.
    set (yA := functor_pmap A) in *.
    set (to := h B pmap_idmap).
    set (fr := (h A)^-1* pmap_idmap).
    Arguments pointed_fun {_ _}.
    Arguments pointed_equiv_fun {_ _}.
    
    serapply pequiv_adjointify'.
    1: exact to.
    1: exact fr.
    { intro x.
      set (p := h_nat A B to).
      set (q := h_nat B A fr).
      admit. }
    { intro x.
      set (p := h_nat A B to).
      set (q := h_nat B A fr).
      set (_yA_ := F_functor (A:=B) (B:=A) yA) in *.
      
(*       destruct p as [p p_point]. *)
      destruct (h_nat B B pmap_idmap) as [p' pp]. _
      p' pmap_idmap
      unfold yA in h_nat.
      unfold functor_pmap in h_nat.
      simpl in h_nat.
      
      cbv.
      
      apply eissect.
    
    
     simpl.
      set (p := h_nat A B to).
      set (q := h_nat B A fr).
      unfold fr.
      unfold to in p, q.
      cbv.
      pointed_reduce.
      admit. }
    { simpl.
      set (h_nat B A fr).
      
    
    2: refine ((h A)^-1* _). pmap_idmap).



*)





