Require Import Basics.
Require Import Types.
Require Import Pointed.Core.
Require Import Pointed.pMap.
Require Import Pointed.pHomotopy.
Require Import Pointed.pEquiv.
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

(** This makes it easier to write locally. *)
Local Notation ne := NaturalEquivalence.

Definition natequiv_inv {F G : Functor}
  : NaturalEquivalence F G -> NaturalEquivalence G F.
Proof.
  intros [e n].
  serapply Build_NaturalEquivalence.
  1: intro; apply pequiv_inverse, e.
  by apply isnatural_inverse.
Defined.

Definition natequiv_compose {F G H : Functor}
  : ne F G -> ne G H -> ne F H.
Proof.
  intros [e n] [f m].
  serapply Build_NaturalEquivalence.
  1: exact (fun X => f X o*E e X).
  serapply isnatural_compose.
Defined.

Global Instance reflexive_natequiv : Reflexive NaturalEquivalence.
Proof.
  intro F.
  serapply Build_NaturalEquivalence.
  1: intro; reflexivity.
  intros A B f.
  simpl.
  exact (pmap_postcompose_idmap _
    @* (pmap_precompose_idmap _)^*).
Defined.

Global Instance symmetric_natequiv : Symmetric NaturalEquivalence.
Proof.
  intros F G p.
  by apply natequiv_inv.
Defined.

Global Instance transitive_natequiv : Transitive NaturalEquivalence.
Proof.
  intros F G H p q.
  apply (natequiv_compose p q).
Defined.

Lemma pYoneda {A B : pType} `{Funext}
  (p : NaturalEquivalence (functor_pmap B) (functor_pmap A))
  : A <~>* B.
Proof.
  destruct p as [e n].
  serapply pequiv_adjointify'.
  1: exact (e B pmap_idmap).
  1: exact ((e A)^-1 pmap_idmap).
  1,2: intro x.
  1: refine (_ @ pointed_htpy (path_pmap^-1 (eissect (e B) pmap_idmap)) x).
  1: pose proof (pointed_htpy
    (isnatural_inverse e A B (e B pmap_idmap)) pmap_idmap) as p.
  2: refine (_ @ pointed_htpy (path_pmap^-1 (eisretr (e A) pmap_idmap)) x).
  2: pose proof (pointed_htpy (n B A ((e A)^-1 pmap_idmap)) pmap_idmap)as p.
  1,2: cbn in p; symmetry in p.
  1,2: rewrite 3 path_pmap_precompose_idmap in p.
  1,2: apply path_pmap^-1 in p.
  1,2: apply pointed_htpy in p.
  1,2: apply (p x).
Defined.

Definition natequiv_precompose `{Funext} {A B : pType} (p : A <~>* B)
  : NaturalEquivalence (functor_pmap B) (functor_pmap A).
Proof.
  serapply Build_NaturalEquivalence.
  { intro X.
    by serapply pequiv_isprofunctor. }
  intros X Y f.
  serapply Build_pHomotopy.
  { intro g.
    apply path_pmap.
    serapply Build_pHomotopy.
    1: reflexivity.
    refine (concat_1p _ @ concat_1p _ @ _).
    refine (_ @ ap _ _).
    2: exact ((concat_1p _)^ @ (ap_idmap _)^ @ (concat_p1 _)^).
    refine (_ @ concat_pp_p _ _ _).
    cbn; apply whiskerR.
    refine (ap_pp _ _ _ @ _).
    refine (ap (fun x => x @ _) _ @ _).
    1: symmetry; apply ap_compose.
    apply whiskerL, ap.
    refine (concat_p1 _ @ _).
    apply ap_idmap. }
  simpl.
Admitted.


(** TODO: 

  When p is a pointed natural equivalence
  
  contravariant hom (pYoneda p) X ==* p X

  pYoneda ought to be an equivalence with inverse given by precomposition but this is unlikely to be provable.
  

*)

Definition natequiv_functor_compose_assoc `{U : Funext} F G H
  : NaturalEquivalence (F oF (G oF H)) ((F oF G) oF H).
Proof.
  serapply Build_NaturalEquivalence.
  1: intro; reflexivity.
  simpl.
  intros X Y f.
  simpl.
  exact (pmap_postcompose_idmap _
    @* (pmap_precompose_idmap _)^*).
Defined.

Definition natequiv_prewhisker `{U : Funext} {F G} H
  : NaturalEquivalence F G -> NaturalEquivalence (F oF H) (G oF H).
Proof.
  intro p.
  serapply Build_NaturalEquivalence.
  { intro X.
    apply p. }
  simpl.
  intros X Y f.
  apply ne_isnatural.
Defined.

Definition natequiv_postwhisker `{U : Funext} {F G} H
  : NaturalEquivalence F G -> NaturalEquivalence (H oF F) (H oF G).
Proof.
  intro p.
  serapply Build_NaturalEquivalence.
  { intro X; cbn.
    serapply pequiv_isfunctor.
    apply p. }
  intros X Y f; cbn.
  refine (F_compose^* @* _ @* F_compose).
  apply F_2functor.
  apply ne_isnatural.
Defined.



