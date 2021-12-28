Require Import Basics Types WildCat.
Require Import Truncations HFiber.
Require Import Diagrams.Graph Diagrams.Sequence Diagrams.Diagram Diagrams.Cocone.
Require Import Homotopy.Join.
Require Import Homotopy.HomotopyImage.
Require Import Colimits.Colimit.

Local Open Scope nat_scope.

(** * Join construction *)

(** In this file we give an alternative construction of the propositional truncation using colimits. This can serve as a metatheoretic justification that propositional truncations exist. *)

(** The joint of n.+1 copies of a type. *)
Fixpoint Join_power (A : Type) (n : nat) : Type :=
  match n with
  | 0 => A
  | m.+1 => Join A (Join_power A m)
  end.

(** The sequence of increasing joins. *)
Definition Join_seq (A : Type) : Sequence.
Proof.
  srapply Build_Sequence.
  1: exact (Join_power A).
  intros n.
  exact joinr.
Defined.

(** Propositional truncation can be defined as the colimit of this sequence. *)
Definition PropTrunc A : Type := Colimit (Join_seq A).

(** The constructor is given by the colimit constructor. *)
Definition ptr_in {A} : A -> PropTrunc A := colim (D:=Join_seq A) 0.

(** The sequential colimit of this sequence is the propositional truncation. *)

(** TODO: move: this is a general property of sequences *)
(** Mapping spaces from colimits of sequences can be characterized. *)
Lemma equiv_colim_seq_rec `{Funext} (A : Sequence) (P : Type) `{IsHProp P}
  : (Colimit A -> P) <~> (forall n, A n -> P).
Proof.
  symmetry.
  refine (equiv_colimit_rec P oE _).
  refine (issig_Cocone _ _ oE _).
  symmetry.
  srapply Build_Equiv.
  1: exact pr1.
  exact _.
Defined.

(** Universal property of propositional truncation. *)
Lemma equiv_PropTrunc_rec `{Funext} (A P : Type) `{IsHProp P}
  : (PropTrunc A -> P) <~> (A -> P).
Proof.
  refine (_ oE equiv_colim_seq_rec _ P).
  srapply equiv_iff_hprop.
  { intros h.
    exact (h 0). }
  intros f.
  induction n.
  - exact f.
  - cbn.
    srapply Join_rec.
    1,2: assumption.
    intros a b.
    rapply path_ishprop.
Defined.

(** TODO: is this needed? *)
Global Instance isequiv_PropTrunc_rec_precomp `{Funext}
  (A P : Type) `{IsHProp P}
  : IsEquiv (fun f : PropTrunc A -> P => f o ptr_in).
Proof.
  rapply (equiv_isequiv (equiv_PropTrunc_rec A P)).
Defined.

(** TODO: move: this is a general property of sequences *)
(** If a sequential colimit has maps homotopic to a constant map then the colimit is contractible. *)
Global Instance contr_colim_seq_into_prop {funext : Funext} (A : Sequence)
  (a : forall n, A n) (H : forall n, const (a n.+1) == A _f idpath)
  : Contr (Colimit A).
Proof.
  transparent assert (B : Sequence).
  { srapply Build_Sequence.
    1: exact A.
    intros n.
    exact (const (a n.+1)). }
  rapply contr_equiv'.
  1: rapply equiv_functor_colimit.
  1: rapply (equiv_sequence B A).
  1: reflexivity.
  { intros n e.
    exists equiv_idmap.
    intros x.
    symmetry.
    exact (H _ (e x)). }
  srapply Build_Contr.
  1: exact (colim (D:=B) 1 (a 1)).
  srapply Colimit_ind.
  { intros i x.
    induction i.
    1: exact (colimp (D:=B) _ _ idpath x).
    refine (IHi (a i) @ _).
    refine ((colimp (D:=B) _ _ idpath (a i))^ @ _).
    refine ((colimp (D:=B) _ _ idpath (a i.+1))^ @ _).
    exact (colimp (D:=B) _ _ idpath x). }
  intros n m [] x.
  rewrite transport_paths_FlFr.
  rewrite ap_const.
  rewrite ap_idmap.
  destruct n; simpl; hott_simpl.
  (** TODO: I got lazy towards the end, the proof can probably be cleaned up. *)
Qed.

(** The propositional truncation is a hprop. *)
Global Instance ishprop_proptrunc `{Funext} (A : Type)
  : IsHProp (PropTrunc A).
Proof.
  rapply hprop_inhabited_contr.
  rapply (equiv_PropTrunc_rec _ _)^-1.
  intros x.
  srapply contr_colim_seq_into_prop.
  - intros n.
    destruct n.
    1: exact x.
    exact (joinl x).
  - intros n.
    rapply jglue.
Defined.
