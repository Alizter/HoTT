Require Import Basics Types.
Require Import WildCat Pointed.
Require Import Algebra.Groups.
Require Import Homotopy.Bouquet.
Require Import Limits.Limit.
Require Import Diagrams.Sequence Diagrams.Diagram.
Require Import Spaces.Finite.

(** * Hawaiian Earring *)

(** TODO: description of Hawaiian Earring space from topology. *)

(** Note that we are only constructing and working with the homotopy type of the Hawaiian Earring space and not the topological space itself. *)

(** TODO: move to Bouquet *)
Global Instance is0functor_bouquet : Is0Functor Bouquet := _.
Global Instance is1functor_bouquet : Is1Functor Bouquet := _.

(** Given a Bouquet of n circles, there is an inclusion map into a Bouquet of n.+1 circles. *)
Definition bouquet_fin_incl (n : nat)
  : Bouquet (Fin n) $-> Bouquet (Fin n.+1)
  := fmap Bouquet fin_incl.

(** The colimit of these maps should be a bouquet on nat. That should follow formally from Bouquet consisting of composed left adjoints, therefore preserving colimits. Hence it will follow from the colimit of Fin being nat. *)

(** The Hawaiian earring will follow from the retracts of these inclusion maps in fin, not behaving so well with the Bouquet functor. *)

Definition fin_proj (n : nat) (x : Fin n.+2) : Fin n.+1 :=
  match x with
  | inl z => z
  | inr _ => fin_zero
  end.

Lemma path_fin_proj_succ (n : nat)
  : fin_proj n o fin_incl == idmap.
Proof.
  by intros [x|].
Defined.

Definition bouquet_fin_proj (n : nat)
  : Bouquet (Fin n.+2) $-> Bouquet (Fin n.+1)
  := fmap Bouquet (fin_proj n).

(** Functoriality makes showing this is a retract easy. *)
Definition bouquet_fin_proj_succ (n : nat)
  : bouquet_fin_proj n $o bouquet_fin_incl n.+1 $== Id _.
Proof.
  refine ((fmap_comp Bouquet _ _)^$ $@ fmap2 _ _
    $@ fmap_id Bouquet _).
  apply path_fin_proj_succ.
Defined.

(** Now taking the limit of this sequence will yield the Hawaiian earring. *)

(** The sequence for the Hawaiian earring *)
Require Import Diagrams.Graph.

Definition sequenceop_graph : Graph :=
  Build_Graph nat (fun n m : nat => m.+1%nat = n).

Definition SequenceOp := Diagram sequenceop_graph.
Definition Build_SequenceOp
  (X : nat -> Type) (f : forall n : nat, X (S n) -> X n)
  : SequenceOp.
Proof.
  srapply (Build_Diagram sequenceop_graph X).
  intros n m [].
  rapply f.
Defined.

Definition seqop_hawaii : SequenceOp :=
  Build_SequenceOp
    (fun n => Bouquet (Fin n.+1))
    bouquet_fin_proj.


Definition HawaiianEarring : Type := Limit seqop_hawaii.

(** TODO: we need better limits/colimits *)




