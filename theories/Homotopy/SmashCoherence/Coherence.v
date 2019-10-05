Require Import Basics.
Require Import Types.
Require Import Pointed.

Local Open Scope pointed_scope.

(* By functor we really mean 1-coherent functor *)
Class IsFunctor (F : pType -> pType) := {
  F_functor {A B : pType} (f : A ->* B) : F A ->* F B;
  F_idmap {A : pType} : F_functor (@pmap_idmap A) ==* pmap_idmap;
  F_compose {A B C : pType} {f' : B ->* C} {f : A ->* B}
    : F_functor (f' o* f) ==* F_functor f' o* F_functor f;
}.

(* TODO: Change name. *)
(* A "2Functor" is a functor which preserves pHomotopies *)
Class Is2Functor (F : pType -> pType) `{IsFunctor F} := {
  F_2functor : forall (A B : pType) (f g : A ->* B),
    f ==* g -> F_functor f ==* F_functor g
}.

(* Given funext any functor is a "2functor". *)
Global Instance is2functor_functor `{Funext} {F : pType -> pType}
  `{IsFunctor F} : Is2Functor F.
Proof.
  serapply Build_Is2Functor.
  intros A B f g p.
  by destruct (path_pmap p).
Defined.

(* The equivalence generated from being a functor *)
Definition pequiv_isfunctor (F : pType -> pType) `{Is2Functor F}
  {A B : pType} : A <~>* B -> F A <~>* F B.
Proof.
  intro e.
  serapply pequiv_adjointify.
  1: apply F_functor, e.
  1: apply F_functor, e^-1*.
  1,2: refine (F_compose^* @* _).
  1,2: refine (_ @* F_idmap).
  1,2: apply F_2functor.
  1: apply peisretr.
  apply peissect.
Defined.

Class IsPointedFunctor (F : pType -> pType) := {
  F_zero : F punit = punit
}.

(* TODO: Rename *)
Lemma functor_zero `{Funext} F `{IsPointedFunctor F} `{IsFunctor F} {A B : pType}
  : F_functor (pmap_const : A ->* B) = pmap_const.
Proof.
  rewrite <- (path_pmap (pmap_postcompose_const (pmap_const (A := punit)))).
  rewrite (path_pmap F_compose).
  rewrite (path_pmap (punit_ind_const' (F_functor pmap_const ) F_zero)).
  apply (path_pmap (pmap_precompose_const (F_functor pmap_const))).
Defined.

Section NaturalTransformation.

  Context
   `{Funext}
    {F G : pType -> pType}
   `{IsFunctor F}
   `{IsFunctor G}
   `{IsPointedFunctor F}
   `{IsPointedFunctor G}.

  (* TODO: Name *)
  Definition natural_zero (P : forall (X : pType), F X ->* G X) {A B : pType}
    : P B o* F_functor (F := F) (pmap_const)
    ==* F_functor (F := G) (pmap_const) o* P A.
  Proof.
    destruct (functor_zero F (A:=A) (B:=B))^.
    destruct (functor_zero G (A:=A) (B:=B))^.
    refine (phomotopy_compose (pmap_postcompose_const _) _).
    apply phomotopy_inverse.
    apply pmap_precompose_const.
  Defined.

  Class IsNatural (P : forall (X : pType), F X ->* G X) := {
    natsquare {A B : pType} (f : A ->* B)
      : P B o* F_functor f ==* F_functor f o* P A;
  }.

  Class IsPointedNatural (P : forall (X : pType), F X ->* G X) := {
    pointed_isnat : IsNatural P;
    pointed_nattr {A B : pType} : natsquare (@pmap_const A B) = natural_zero P
  }.

End NaturalTransformation.

Class IsBifunctor (F : pType -> pType -> pType) := {
  F_bifunctor {A B A' B' : pType} (f : A ->* B) (f : A' ->* B')
    : F A A' ->* F B B';
  F_bidmap {A A' : pType} : F_bifunctor (@pmap_idmap A) (@pmap_idmap A')
    ==* pmap_idmap;
  F_bicompose {A A' B B' C C' : pType} {g : B ->* C} {f : A ->* B}
    {g' : B' ->* C'} {f' : A' ->* B'}
    : F_bifunctor (g o* f) (g' o* f')
      ==* (F_bifunctor g g') o* (F_bifunctor f f');
}.

Global Instance isfunctor_bifunctor_left (F : pType -> pType -> pType)
  `{IsBifunctor F} (A : pType) : IsFunctor (F A).
Proof.
  serapply Build_IsFunctor.
  { intros X Y.
    apply F_bifunctor, pmap_idmap. }
  { intro X.
    apply F_bidmap. }
  intros X Y Z f' f; cbn.
  apply (F_bicompose (g:=pmap_idmap) (f:=pmap_idmap)).
Defined.

Global Instance isfunctor_bifunctor_right (F : pType -> pType -> pType)
  `{IsBifunctor F} (A : pType) : IsFunctor (fun x => F x A).
Proof.
  serapply Build_IsFunctor.
  { intros X Y f; cbn.
    refine (F_bifunctor f pmap_idmap). }
  { intro X.
    apply F_bidmap. }
  intros X Y Z f' f; cbn.
  apply (F_bicompose (g':=pmap_idmap) (f':=pmap_idmap)).
Defined.

(* TODO: Change name. *)
(* A "2Bifunctor" is a bifunctor which preserves pHomotopies in each argument *)
Class Is2Bifunctor (F : pType -> pType -> pType) `{IsBifunctor F} := {
  F_2bifunctor : forall (A A' B B' : pType) (f g : A ->* B) (f' g' : A' ->* B'),
    f ==* g -> f' ==* g' -> F_bifunctor f f' ==* F_bifunctor g g';
}.

(* Given funext any bifunctor is a "2Bifunctor". *)
Global Instance is2bifunctor_bifunctor `{Funext} {F : pType -> pType -> pType}
  `{IsBifunctor F} : Is2Bifunctor F.
Proof.
  serapply Build_Is2Bifunctor.
  intros A A' B B' f g f' g' p p'.
  by destruct (path_pmap p), (path_pmap p').
Defined.

(* The equivalence generated from being a bifunctor *)
Definition pequiv_isbifunctor (F : pType -> pType -> pType) `{Is2Bifunctor F}
  {A A' B B' : pType} : A <~>* B -> A' <~>* B' -> F A A' <~>* F B B'.
Proof.
  intros e e'.
  serapply pequiv_adjointify.
  1: exact (F_bifunctor e e').
  1: exact (F_bifunctor e^-1* e'^-1*).
  1,2: refine (F_bicompose^* @* _).
  1,2: refine (_ @* F_bidmap).
  1,2: apply F_2bifunctor.
  1,2: apply peisretr.
  1,2: apply peissect.
Defined.

(* A profunctor is like a bifunctor but contravariant in its first argument. *)
Class IsProfunctor (F : pType -> pType -> pType) := {
  F_profunctor {A B A' B' : pType} (f : A ->* B) (f : A' ->* B')
    : F B A' ->* F A B';
  F_proidmap {A A' : pType} : F_profunctor (@pmap_idmap A) (@pmap_idmap A')
    ==* pmap_idmap;
  F_procompose {A A' B B' C C' : pType} {g : B ->* C} {f : A ->* B}
    {g' : B' ->* C'} {f' : A' ->* B'}
    : F_profunctor (g o* f) (g' o* f')
      ==* (F_profunctor f g') o* (F_profunctor g f');
}.

(* Notably filling the left side of a profunctor gives a functor. *)
Global Instance isfunctor_profunctor_left (F : pType -> pType -> pType)
  `(IsProfunctor F) (A : pType) : IsFunctor (F A).
Proof.
  serapply Build_IsFunctor.
  { intros X Y.
    apply F_profunctor, pmap_idmap. }
  { intro X.
    apply F_proidmap. }
  intros X Y Z f' f; cbn.
  apply (F_procompose (g:=pmap_idmap) (f:=pmap_idmap)).
Defined.

(* TODO: Change name. *)
(* A "2profunctor" is a profunctor which preserves pHomotopies in each argument *)
Class Is2Profunctor (F : pType -> pType -> pType) `{IsProfunctor F} := {
  F_2profunctor : forall (A A' B B' : pType) (f g : A ->* B) (f' g' : A' ->* B'),
    f ==* g -> f' ==* g' -> F_profunctor f f' ==* F_profunctor g g';
}.

(* Given funext any profunctor is a "2profunctor". *)
Global Instance is2profunctor_profunctor `{Funext} {F : pType -> pType -> pType}
  `{IsProfunctor F} : Is2Profunctor F.
Proof.
  serapply Build_Is2Profunctor.
  intros A A' B B' f g f' g' p p'.
  by destruct (path_pmap p), (path_pmap p').
Defined.

(* The equivalence generated from being a profunctor *)
Definition pequiv_isprofunctor (F : pType -> pType -> pType) `{Is2Profunctor F}
  {A A' B B' : pType} : A <~>* B -> A' <~>* B' -> F B A' <~>* F A B'.
Proof.
  intros e e'.
  serapply pequiv_adjointify.
  1: exact (F_profunctor e e').
  1: exact (F_profunctor e^-1* e'^-1*).
  1,2: refine (F_procompose^* @* _).
  1,2: refine (_ @* F_proidmap).
  1,2: apply F_2profunctor.
  2,3: apply peisretr.
  1,2: apply peissect.
Defined.

Section SymmetricMonoidal.

  Context (F : pType -> pType -> pType).

  Notation "A ⊗ B" := (F A B) (at level 20).
  Notation "f '[⊗]' g" := (F_bifunctor f g) (at level 20).
  Notation id := pmap_idmap.

  (* Here is all the data of a symmetric monoidal product *)
  Class SymmetricMonoidalProduct := 
  {
    (* Bifunctor *)
    coh_bifunctor : IsBifunctor F;

    (* Associator *)
    associator A B C : (A ⊗ B) ⊗ C <~>* A ⊗ (B ⊗ C);

    (* Associator naturality square *)
    associator_nat_square A A' B B' C C' (f : A ->* A')
      (g : B ->* B') (h : C ->* C')
      : f [⊗] (g [⊗] h) o* associator A B C
      ==* associator A' B' C' o* (f [⊗] g) [⊗] h;

    (* Pentagon *)
    pentagon A B C D : associator A B (C ⊗ D) o* associator (A ⊗ B) C D
      ==* id [⊗] associator B C D o*
      associator A (B ⊗ C) D o* associator A B C [⊗] id;

    (* Braiding *)
    braiding A B : A ⊗ B <~>* B ⊗ A;

    (* Braiding naturality square *)
    braiding_nat_square A A' B B' (f : A ->* A') (g : B ->* B')
      : g [⊗] f o* braiding A B ==* braiding A' B' o* f [⊗] g;

    (* Hexagon *)
    hexagon A B C : associator B C A o* braiding A (B ⊗ C) o* associator A B C
      ==* id [⊗] braiding A C o* associator B A C o* braiding A B [⊗] id;

    (* Unit *)
    unit : pType;

    (* Left unitor *)
    unitor A : unit ⊗ A <~>* A;

    (* Left unitor naturality square *)
    unitor_nat_square A A' (f : A ->* A') : f o* unitor A
      ==* unitor A' o* id [⊗] f;

    (* Left unitor triangle *)
    unitor_triangle A B : unitor (A ⊗ B) o* associator unit A B
      ==* unitor A [⊗] id;
  }.

End SymmetricMonoidal.

