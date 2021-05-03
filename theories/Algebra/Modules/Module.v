Require Import Basics Types.
Require Import Algebra.Groups.
Require Import Algebra.AbGroups.
Require Import Algebra.Rings.

Local Open Scope mc_scope.
Local Open Scope mc_add_scope.

Class ScalarOp (A B : Type) : Type := scalar : A -> B -> B.
Typeclasses Transparent ScalarOp.

Infix "⋅" := scalar (at level 20).


(** An R-module is an abelian group together with an action of a ring R. *)
Record Module (R : CRing) := Build_Module' {
  (** We coerce modules to their underlying Abelian groups *)
  module_abgroup :> AbGroup ;
  (** Scalar operation *)
  module_scalar : ScalarOp R module_abgroup ;
  (** Scalar operation distributes over addition in the group. *)
  module_distr_l
    : LeftHeteroDistribute (A := R) (B := module_abgroup) (C := module_abgroup)
        scalar (+) (+) ;
  (** Scalar operation distributes through addition in the scalar. *)
  module_distr_r
    : RightHeteroDistribute (A := R) (B := module_abgroup) (C := module_abgroup)
        scalar (+) (+) ;
  (** Scalar operation is associative *)
  module_assoc : HeteroAssociative scalar scalar scalar (.*.) ;
  (** Scalar operation unit action *)
  module_unit : LeftIdentity scalar cring_one ;
}.

Arguments module_scalar {R m}.

Module ModuleNotations.
  (* Infix "⋅" := module_scalar (at level 20). *)
  Notation "R -module" := (Module R) (format "R -module", at level 1).
End ModuleNotations.

Import ModuleNotations.

(** Same constructor but with typeclasses unfolded. *)
Definition Build_Module (R : CRing) (A : AbGroup) (s : ScalarOp R A)
  (h1 : forall (a : R) (b c : A), a ⋅ (b + c) = a ⋅ b + a ⋅ c)
  (h2 : forall (a b : R) (c : A), (a + b) ⋅ c = a ⋅ c + b ⋅ c)
  (h3 : forall (x y : R) (z : A), x ⋅ (y ⋅ z) = (x * y) ⋅ z)
  (h4 : forall y : A, cring_one ⋅ y = y)
  : R-module
  := Build_Module' R A s h1 h2 h3 h4.

