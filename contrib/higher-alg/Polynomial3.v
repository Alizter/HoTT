Require Import Basics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Section PolyDef.

(** A polynomial over I consists of the following data: **)
Record Poly {I : Type} := {
  (** A family of operations **)
  Op : I -> Type;
  (** For each operation, a family of paramaters **)
  Param {i : I} : Op i -> Type;
  (** A function choosing the sorts of the parameters **)
  SortOf {i : I} (f : Op i) : Param f -> I;
}.

(** Let I be a type of sorts **)
Context {I : Type}.

Context {P : @Poly I}.

(** Operations of a polynomial **)
Definition Ops := exists (i : I), Op P i.

(** A polynomial P : Poly I generates a type of trees: **)
Inductive Tr (i : I) : Type :=
  | lf : Tr i
  | nd (f : Op P i) (phi : forall (p : Param P f), Tr (SortOf P f p)) : Tr i.


(** For a tree w : Tr i, we will need its type of leaves **)
Fixpoint Leaf {i : I} (w : Tr i) : I -> Type.
  intro j; induction w.
  + refine (i = j).
  + refine (exists (p : Param P f), Leaf _ (phi p) j).
Defined.

(** And the type of nodes **)
Fixpoint Node {i : I} (w : Tr i) : Ops -> Type.
  intros jg; induction w.
  + refine Empty.
  + refine (((i;f) = jg) + exists (p : Param P f), Node _ (phi p) jg).
Defined.

(**TODO: This definition needs to be corrected **)
(** A frame from a tree w to an operator f checks if the leaves of the tree are
    equivalent to the parameters of the operator **)
Definition Frame {i : I} {P : Poly} (w : Tr i) (f : Op P i) :=
  exists (j : I), @Leaf i w j <~> Param P f.

Definition InFrame : Ops -> Type.
  intro; destruct X as [i f].
  refine (exists (w : Tr i), Frame w f).
Defined.

(** Polynomial relation **)
Definition PolyRel : Type.
  refine (forall (f : Ops), InFrame f -> Type).
Defined.

End PolyDef.

Section Flatten.

Context {I : Type}.

(** TODO: Check this is correct **)
(** Slice of polynomial by a relation **)
Definition Slice (P : @Poly I) (R : @PolyRel _ P) : @Poly (@Ops _ P).
  srapply Build_Poly.
  + intro f; refine (exists (inf : InFrame f), R f inf).
  + intros jg X; destruct X as [x _]; destruct x as [w inf]; destruct inf as [c _]. 
    refine (Node w jg).
  + intros jg X Y. refine jg.
Defined.

Notation "P // R" := (@Slice P R) : flatten_scope.

Open Scope flatten_scope.

Context {P : @Poly I}.
Context {R : @PolyRel _ P}.

Definition flatten {i : I} {f : Op P i} : @Tr _ (P // R) (i ; f) -> @Tr _ P i.





