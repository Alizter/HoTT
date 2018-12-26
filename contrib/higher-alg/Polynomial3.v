Require Import Basics.
Require Import Types.Sigma.

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
  SortOf {i : I} {f : Op i} : Param f -> I;
}.

(** Let I be a type of sorts **)
Context {I : Type}.

Context {P : @Poly I}.

(** Operations of a polynomial **)
Definition Ops := exists (i : I), Op P i.

(** Gets parameters of a given sort **)
Definition SortedParam {i : I} (f : Op P i) (k : I) := 
  exists (p : Param P f), SortOf P p = k.

(** Used to define functions associated with nodes **)
Definition bracket (X : I -> Type) (i : I) : Type :=
  exists (f : Op P i), forall j, Param P f -> X j.

(** framed version **)
Definition bracketf {X Y : I -> Type} (psi : forall (i : I), X i -> Y i)
(i : I) : (bracket X i) -> (bracket Y i).
  intro X0; destruct X0 as [f phi];
  refine (f ; _); intros; refine (psi j (phi j X0)).
Defined.

(** A polynomial P : Poly I generates a type of trees: **)
Inductive Tr (i : I) : Type :=
  | lf : Tr i
  | nd : bracket Tr i -> Tr i.

(** For a tree w : Tr i, we will need its type of leaves **)
Fixpoint Leaf {i : I} (w : Tr i) : I -> Type.
  intro j; induction w.
  + refine (i = j).
  + destruct b as [f phi].
    refine (exists (p : Param P f), Leaf _ (phi j p) j).
Defined.

(** And the type of nodes **)
Fixpoint Node {i : I} (w : Tr i) : Ops -> Type.
  intros jg; induction w.
  + refine Empty.
  + destruct b as [f phi]; destruct jg as [j g].
    refine (((i;f) = (j;g)) +
      exists (p : Param P f), Node _ (phi j p) (j;g)).
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

(** TODO: Check this is correct **)
(** Slice of polynomial by a relation **)
Definition Slice (R : PolyRel) : @Poly Ops.
  srapply Build_Poly.
  + intro f; refine (exists (inf : InFrame f), R f inf).
  + intros jg X; destruct X as [x _]; destruct x as [w inf]; destruct inf as [c _]. 
    refine (Node w jg).
  + intros jg X Y. refine jg.
Defined.


(** Any operation is a tree **)
Definition corolla {i : I} (f : Op P i) : Tr i.
  refine (nd (f; fun j p => lf j)).
Defined.

Definition corolla_frm {i : I} (f : Op P i) : 
(exists (j : I), Leaf (corolla f) j) <~> Param P f.
  serapply equiv_adjointify.
  + refine (fun X => X.2.1).
  + refine (fun X => (i ; X ; idpath)).
  + refine (fun _ => idpath).
  + compute. intros. destruct x as [j y]. destruct y as [y z].
    * compute. intros. destruct x as [j y]. destruct y as [y z].
      
End PolyDef.

Notation "P // R" := (@Slice _ P R) : flatten_scope.

Section Flatten.

Context {I : Type}.
Context {P : @Poly I}.
Context {R : @PolyRel _ P}.


Open Scope flatten_scope.

Definition flatten {i : I} {f : Op P i} : @Tr _ (P // R) (i ; f) -> @Tr _ P i.
  intro w; induction w.
  + refine (corolla f).
  +
Admitted.

Definition flatten_frm 






