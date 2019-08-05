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
    : F_bifunctor (g o* f) (g' o* f') ==* (F_bifunctor g g') o* (F_bifunctor f f');
}.

Global Instance isfunctor_bifunctor_left (F : pType -> pType -> pType)
  `(IsBifunctor F) (A : pType) : IsFunctor (F A).
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
  `(IsBifunctor F) (A : pType) : IsFunctor (fun x => F x A).
Proof.
serapply Build_IsFunctor.
  { intros X Y f; cbn.
    refine (F_bifunctor f pmap_idmap). }
  { intro X.
    apply F_bidmap. }
  intros X Y Z f' f; cbn.
  apply (F_bicompose (g':=pmap_idmap) (f':=pmap_idmap)).
Defined.

Section BiFunctor.

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

End BiFunctor.
