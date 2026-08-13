Require Import Basics.Overture Basics.Tactics Basics.Equivalences
  Basics.PathGroupoids.
Require Import Types.Paths Types.Sigma.
Require Import Spaces.Nat.Core.
Require Import Diagrams.Sequence Diagrams.Cocone.
Require Import Colimits.Colimit Colimits.Sequential.
Require Import WildCat.Core.
Require Import Pointed.Core Pointed.Loops Pointed.pEquiv.

Local Open Scope pointed_scope.
Local Close Scope trunc_scope.
Local Open Scope nat_scope.

(** * Sequential colimits of pointed types *)

(** A pointed sequence consists of pointed types and pointed structure maps. *)
Definition PSequence
  := {A : nat -> pType & forall n, A n ->* A n.+1}.

Definition pseq_type (A : PSequence) (n : nat) : pType
  := A.1 n.

Coercion pseq_type : PSequence >-> Funclass.

Definition pseq_map (A : PSequence) (n : nat)
  : A n ->* A n.+1
  := A.2 n.

(** The underlying sequence of types. *)
Definition sequence_psequence (A : PSequence) : Sequence
  := Build_Sequence (fun n => A n) (fun n => pseq_map A n).

(** A pointed cocone is an ordinary cocone together with pointedness at its zeroth leg.  Pointedness of all later legs follows recursively, so no additional coherence data is required. *)
Definition pSeqCocone (A : PSequence) (X : pType)
  := {C : Cocone (sequence_psequence A) X &
      C 0 (point (A 0)) = point X}.

Definition pseq_cocone_cocone {A : PSequence} {X : pType}
  (C : pSeqCocone A X)
  : Cocone (sequence_psequence A) X
  := C.1.

Coercion pseq_cocone_cocone : pSeqCocone >-> Cocone.

Definition pseq_cocone_point {A : PSequence} {X : pType}
  (C : pSeqCocone A X)
  : C 0 (point (A 0)) = point X
  := C.2.

(** Every leg of a pointed sequential cocone is pointed. *)
Fixpoint pseq_cocone_leg_point {A : PSequence} {X : pType}
  (C : pSeqCocone A X) (n : nat)
  : C n (point (A n)) = point X.
Proof.
  destruct n as [|n].
  - exact (pseq_cocone_point C).
  - refine (ap (C n.+1) (point_eq (pseq_map A n))^
      @ legs_comm C n n.+1 idpath (point (A n))
      @ _).
    napply pseq_cocone_leg_point.
Defined.

Definition pseq_cocone_leg {A : PSequence} {X : pType}
  (C : pSeqCocone A X) (n : nat)
  : A n ->* X.
Proof.
  snapply Build_pMap.
  - exact (C n).
  - napply pseq_cocone_leg_point.
Defined.

Local Definition pseq_cocone_comm_point
  {X : Type} {x y z w : X}
  (p : x = y) (q : x = z) (r : z = w)
  : q = (p @ ((p^ @ q) @ r)) @ r^.
Proof.
  destruct p, q, r.
  reflexivity.
Defined.

(** The cocone equations are pointed homotopies. *)
Definition pseq_cocone_comm {A : PSequence} {X : pType}
  (C : pSeqCocone A X) (n : nat)
  : pseq_cocone_leg C n.+1 o* pseq_map A n
    ==* pseq_cocone_leg C n.
Proof.
  snapply Build_pHomotopy.
  - exact (legs_comm C n n.+1 idpath).
  - cbn.
    unfold pseq_cocone_leg_point; cbn.
    rewrite ap_V.
    apply pseq_cocone_comm_point.
Defined.

(** Pointed maps and pointed commuting homotopies determine a pointed cocone. *)
Definition pseq_cocone_of_pmaps {A : PSequence} {X : pType}
  (f : forall n, A n ->* X)
  (h : forall n, f n.+1 o* pseq_map A n ==* f n)
  : pSeqCocone A X.
Proof.
  snapply exist.
  - snapply Build_Cocone.
    + exact (fun n => f n).
    + intros n m p.
      destruct p.
      exact (h n).
  - exact (point_eq (f 0)).
Defined.

(** The sequential colimit is pointed by the image of the zeroth basepoint. *)
Definition pSeqColimit (A : PSequence) : pType
  := [Colimit (sequence_psequence A),
      @colim sequence_graph (sequence_psequence A) 0
        (point (A 0))].

(** The canonical pointed cocone into the sequential colimit. *)
Definition pseq_cocone_colimit (A : PSequence)
  : pSeqCocone A (pSeqColimit A).
Proof.
  snapply exist.
  - exact (cocone_colimit (sequence_psequence A)).
  - reflexivity.
Defined.

Definition pseq_inj (A : PSequence) (n : nat)
  : A n ->* pSeqColimit A
  := pseq_cocone_leg (pseq_cocone_colimit A) n.

Definition pseq_glue (A : PSequence) (n : nat)
  : pseq_inj A n.+1 o* pseq_map A n
    ==* pseq_inj A n
  := pseq_cocone_comm (pseq_cocone_colimit A) n.

(** The pointed recursor for a sequential colimit. *)
Definition pseq_colimit_rec {A : PSequence} {X : pType}
  (C : pSeqCocone A X)
  : pSeqColimit A ->* X.
Proof.
  snapply Build_pMap.
  - exact (Colimit_rec X C).
  - exact (pseq_cocone_point C).
Defined.

(** The pointed recursor is an equivalence: this is the concrete universal property needed below. *)
Definition equiv_pseq_colimit_rec `{Funext}
  (A : PSequence) (X : pType)
  : pSeqCocone A X <~> (pSeqColimit A ->* X).
Proof.
  refine (issig_pmap _ _ oE _).
  exact (equiv_functor_sigma_pb
    (equiv_colimit_rec (D := sequence_psequence A) X)).
Defined.

(** ** Shifting and looping pointed sequences *)

Definition pseq_succ (A : PSequence) : PSequence
  := (fun n => A n.+1; fun n => pseq_map A n.+1).

(** Dropping the zeroth term does not change a pointed sequential colimit. *)
Definition pequiv_pseq_colimit_succ (A : PSequence)
  : pSeqColimit (pseq_succ A) <~>* pSeqColimit A.
Proof.
  snapply Build_pEquiv'.
  - exact (equiv_colim_succ_seq_to_colim_seq
      (sequence_psequence A)).
  - exact (point_eq (pseq_inj A 1)).
Defined.

Definition pseq_loops (A : PSequence) : PSequence
  := (fun n => loops (A n);
      fun n => fmap loops (pseq_map A n)).

(** Applying loops to the canonical legs gives a cocone over the levelwise loop sequence. *)
Definition pseq_cocone_loops (A : PSequence)
  : pSeqCocone (pseq_loops A) (loops (pSeqColimit A)).
Proof.
  snapply pseq_cocone_of_pmaps.
  - exact (fun n => fmap loops (pseq_inj A n)).
  - intro n.
    refine ((fmap_comp loops
      (pseq_map A n) (pseq_inj A n.+1))^* @* _).
    exact (fmap2 loops (pseq_glue A n)).
Defined.

(** The canonical comparison from the colimit of the loop spaces to the loop space of the colimit. *)
Definition pseq_colimit_loops (A : PSequence)
  : pSeqColimit (pseq_loops A) ->* loops (pSeqColimit A)
  := pseq_colimit_rec (pseq_cocone_loops A).
