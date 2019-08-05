Require Import Basics.
Require Import Types.
Require Import HSet.
Require Import Pointed.
Require Import TruncType.
Require Import UnivalenceAxiom.

Local Open Scope path_scope.
Local Open Scope pointed_scope.

(* 7.1.11 is TruncType.istrunc_trunctype *)

Local Notation "( X , x )" := (Build_pType X x).

Definition P (n : nat) (X : TruncType n)
  := iterated_loops n.+1 (Build_pType (TruncType n) X).

Global Instance isset_P n : forall X, IsHSet (P n X).
Proof.
  intro X.
(*   refine ((equiv_istrunc_istrunc_loops -2 (P n X))^-1%equiv _).
  intro.
  set (P n X).
  apply istrunc_loops.
  serapply hset_axiomK.
  unfold axiomK. *)
Admitted.
(* Defined. *)

Definition Loop n := sigT (pointed_type o (P n)).

Definition istrunc_Loop (n : nat) : IsTrunc n.+1 (Loop n).
Proof.
  induction n.
  1: exact _.
  unfold Loop; cbn.
  refine (@trunc_sigma _ _ n.+2 _ _).
  intro X.
  refine (@trunc_leq _ n.+2 _ _ (isset_P n.+1 X)).
  exact tt.
Defined.

Definition ptrivial (A : pType) (b : A) := point A = b.
Definition exists_nontrivial (A : pType) := {b : _ & ~(ptrivial A b)}.

Definition iterated_loops_Loop_nontrivial n
  : exists_nontrivial (iterated_loops n.+2 (Type, Loop n)).
Proof.
  
Admitted.

(* Definition bar n : exists_nontrivial (iterated_loops n.+2
  (n.+1 -Type, @BuildTruncType n.+1 (Loop n) (istrunc_Loop n))).
Proof.
  set ((n.+1 -Type, @BuildTruncType n.+1 (Loop n) (istrunc_Loop n))).
  assert (p = (psigma ((Type, Loop n); (IsTrunc n.+1; istrunc_Loop n)))).
  { admit. }
  rewrite X.
  refine (transport exists_nontrivial _ _).
  { refine (loops_psigma_trunc n.+2 (Type, Loop n) (IsTrunc n.+1; istrunc_Loop n) _).
  
  rewrite (loops_psigma_trunc n.+2 (Type, Loop n) (IsTrunc n.+1; istrunc_Loop n) _).
  
  
  
  assert ({| trunctype_type := Loop n; istrunc_trunctype_type := istrunc_Loop n |} = (Loop n; istrunc_Loop n)).
Admitted. *)


