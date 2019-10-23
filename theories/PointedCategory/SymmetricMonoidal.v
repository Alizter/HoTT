Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import PointedCategory.Functor.
Require Import PointedCategory.Bifunctor.

Local Open Scope pointed_scope.

Section SymmetricMonoidal.

  Context (F : Bifunctor).

  Local Notation "A ⊗ B" := (F A B) (at level 20).
  Local Notation "f '[⊗]' g" := (F_bifunctor f g) (at level 20).
  Local Notation id := pmap_idmap.

  (* Here is all the data of a symmetric monoidal product *)
  Class SymmetricMonoidalProduct := 
  {
    (* Associator *)
    smp_associator A B C : (A ⊗ B) ⊗ C <~>* A ⊗ (B ⊗ C);

    (* Associator naturality square *)
    smp_associator_nat_square A A' B B' C C' (f : A ->* A')
      (g : B ->* B') (h : C ->* C')
      : f [⊗] (g [⊗] h) o* smp_associator A B C
      ==* smp_associator A' B' C' o* (f [⊗] g) [⊗] h;

    (* Pentagon *)
    smp_pentagon A B C D
      : smp_associator A B (C ⊗ D) o* smp_associator (A ⊗ B) C D
      ==* id [⊗] smp_associator B C D o*
      smp_associator A (B ⊗ C) D o* smp_associator A B C [⊗] id;

    (* Braiding *)
    smp_braiding A B : A ⊗ B <~>* B ⊗ A;

    (* Braiding naturality square *)
    smp_braiding_nat_square A A' B B' (f : A ->* A') (g : B ->* B')
      : g [⊗] f o* smp_braiding A B ==* smp_braiding A' B' o* f [⊗] g;

    (* Hexagon *)
    smp_hexagon A B C : smp_associator B C A o* smp_braiding A (B ⊗ C) o* smp_associator A B C
      ==* id [⊗] smp_braiding A C o* smp_associator B A C o* smp_braiding A B [⊗] id;

    (* Unit *)
    smp_unit : pType;

    (* Left unitor *)
    smp_unitor A : smp_unit ⊗ A <~>* A;

    (* Left unitor naturality square *)
    smp_unitor_nat_square A A' (f : A ->* A') : f o* smp_unitor A
      ==* smp_unitor A' o* id [⊗] f;

    (* Left unitor triangle *)
    smp_unitor_triangle A B : smp_unitor (A ⊗ B) o* smp_associator smp_unit A B
      ==* smp_unitor A [⊗] id;
  }.

End SymmetricMonoidal.

