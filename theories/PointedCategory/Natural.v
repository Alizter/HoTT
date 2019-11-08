Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import PointedCategory.Functor.
Require Import PointedCategory.Profunctor.
Require Import PointedCategory.pMapFunctor.

Local Open Scope pointed_scope.

Definition IsNatural {F G : pType -> pType}
  `{IsFunctor F} `{IsFunctor G}
  (P : forall (X : pType), F X ->* G X)
  := forall A B (f : A ->* B),
    P B o* F_functor _ f ==* F_functor _ f o* P A.

Existing Class IsNatural.

Definition isnatural_compose
  {F G H : pType -> pType}
 `{IsFunctor F} `{IsFunctor G} `{IsFunctor H}
  (P : forall (X : pType), F X ->* G X) {nP : IsNatural P}
  (Q : forall (X : pType), G X ->* H X) {nQ : IsNatural Q}
  : IsNatural (fun X => Q X o* P X).
Proof.
  intros A B f.
  assert (nP' := nP A B f).
  assert (nQ' := nQ A B f).
  refine (pmap_compose_assoc _ _ _ @* _).
  refine (pmap_postwhisker _ nP' @* _).
  refine ((pmap_compose_assoc _ _ _)^* @* _).
  refine (pmap_prewhisker _ nQ' @* _).
  apply pmap_compose_assoc.
Defined.

Definition isnatural_inverse
  {F G : pType -> pType}
 `{IsFunctor F} `{IsFunctor G}
  (e : forall (X : pType), F X <~>* G X) {n : IsNatural e}
  : IsNatural (fun X => (e X)^-1*).
Proof.
  intros X Y f.
  cbv beta.
  transitivity ((e Y)^-1* o* F_functor G f o* ((e X) o* (e X)^-1*)).
  { symmetry.
    refine (_ @* pmap_precompose_idmap _).
    apply pmap_postwhisker, peisretr. }
  transitivity (((e Y)^-1* o* (e Y)) o* F_functor F f o* (e X)^-1*).
  { refine ((pmap_compose_assoc _ _ _)^* @* _).
    apply pmap_prewhisker.
    refine (pmap_compose_assoc _ _ _ @* _ @* (pmap_compose_assoc _ _ _)^*).
    apply pmap_postwhisker.
    symmetry.
    apply n. }
  apply pmap_prewhisker.
  refine (_ @* pmap_postcompose_idmap _).
  apply pmap_prewhisker.
  apply peissect.
Defined.

Class NaturalTransformation (F G : Functor) := {
  nt_component : forall (X : pType), F X ->* G X;
  nt_isnatural :> IsNatural nt_component;
}.

Coercion nt_component : NaturalTransformation >-> Funclass.

Definition nt_compose {F G H : Functor}
  (P : NaturalTransformation F G)
  (Q : NaturalTransformation G H)
  : NaturalTransformation F H
  := Build_NaturalTransformation _ _ _ (isnatural_compose P Q).

Class NaturalEquivalence (F G : Functor) := {
  ne_component (X : pType) : F X <~>* G X;
  ne_isnatural :> IsNatural ne_component;
}.

Coercion ne_component : NaturalEquivalence >-> Funclass.

Definition natequiv_inv {F G : Functor}
  : NaturalEquivalence F G -> NaturalEquivalence G F.
Proof.
  intros [e n].
  serapply Build_NaturalEquivalence.
  1: intro; apply pequiv_inverse, e.
  by apply isnatural_inverse.
Defined.

Lemma pYoneda (A B : pType) `{Funext}
  (p : NaturalEquivalence (functor_pmap A) (functor_pmap B))
  : A <~>* B.
Proof.
  destruct p as [e n].
  serapply pequiv_adjointify'.
  1: exact ((e B)^-1 pmap_idmap).
  1: exact (e A pmap_idmap).
  1,2: intro x.
  1: refine (_ @ pointed_htpy (path_pmap^-1 (eisretr (e B) pmap_idmap)) x).
  1: pose proof (pointed_htpy (n A B ((e B)^-1 pmap_idmap)) pmap_idmap) as p.
  2: refine (_ @ pointed_htpy (path_pmap^-1 (eissect (e A) pmap_idmap)) x).
  2: pose proof (pointed_htpy (isnatural_inverse e B A (e A pmap_idmap)) pmap_idmap) as p.
  1,2: cbn in p; symmetry in p.
  1,2: rewrite 3 path_pmap_precompose_idmap in p.
  1,2: apply path_pmap^-1 in p.
  1,2: apply pointed_htpy in p.
  1,2: apply (p x).
Defined.

