Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import PointedCategory.Functor.
Require Import PointedCategory.Bifunctor.

Local Open Scope pointed_scope.

Section Monoidal.

  Context (F : Bifunctor).

  Local Notation "A ⊗ B" := (F A B) (at level 20).
  Local Notation "f '[⊗]' g" := (F_bifunctor f g) (at level 20).
  Notation id := pmap_idmap.

  (* Here is all the data of a monoidal product *)
  Class MonoidalProduct := 
  {
    (* Associator *)
    mp_associator A B C : (A ⊗ B) ⊗ C <~>* A ⊗ (B ⊗ C);

    (* Associator naturality square *)
    mp_associator_nat_square A A' B B' C C' (f : A ->* A')
      (g : B ->* B') (h : C ->* C')
      : f [⊗] (g [⊗] h) o* mp_associator A B C
      ==* mp_associator A' B' C' o* (f [⊗] g) [⊗] h;

    (* Pentagon *)
    mp_pentagon A B C D : mp_associator A B (C ⊗ D) o* mp_associator (A ⊗ B) C D
      ==* id [⊗] mp_associator B C D o*
      mp_associator A (B ⊗ C) D o* mp_associator A B C [⊗] id;

    (* Unit *)
    mp_unit : pType;

    (* Left unitor *)
    mp_unitor A : mp_unit ⊗ A <~>* A;

    (* Left unitor naturality square *)
    unitor_nat_square A A' (f : A ->* A') : f o* mp_unitor A
      ==* mp_unitor A' o* id [⊗] f;

    (* Left unitor triangle *)
    unitor_triangle A B : mp_unitor (A ⊗ B) o* mp_associator mp_unit A B
      ==* mp_unitor A [⊗] id;
  }.

End Monoidal.