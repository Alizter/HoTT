(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics.


(** Stdlib file *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** The type [nat] of Peano natural numbers (built from [O] and [S])
    is defined in [Datatypes.v] *)

(** This module defines the following operations on natural numbers :
    - predecessor [pred]
    - addition [plus]
    - multiplication [mult]
    - less or equal order [le]
    - less [lt]
    - greater or equal [ge]
    - greater [gt]

   It states various lemmas and theorems about natural numbers,
   including Peano's axioms of arithmetic (in Coq, these are provable).
   Case analysis on [nat] and induction on [nat * nat] are provided too
 *)

Require Coq.Init.Nat.

Open Scope nat_scope.
Local Notation "0" := O.

Definition eq_S := @ap _ _ S.

Hint Resolve (ap S): v62.
Hint Resolve (ap (A:=nat)): core.

(** The predecessor function *)

Definition pred (n:nat) : nat := match n with
                                 | O => n
                                 | S u => u
                                 end.
(* Hint Resolve (f_equal pred): v62. *)

Theorem pred_Sn : forall n:nat, n = pred (S n).
Proof.
  simpl; reflexivity.
Qed.

(** Injectivity of successor *)

Definition eq_add_S n m (H: S n = S m): n = m := ap pred H.
Hint Immediate eq_add_S: core.

Theorem not_eq_S : forall n m:nat, n <> m -> S n <> S m.
Proof.
  red; auto.
Qed.
Hint Resolve not_eq_S: core.

Definition IsSucc (n:nat) : Type :=
  match n with
  | O => False
  | S p => True
  end.

(** Zero is not the successor of a number *)

(* XXX Andrej: Try to put back in, does not work with current Coq. *)
(* Theorem O_S : forall n:nat, 0 <> S n. *)
(* Proof. *)
(*   discriminate. *)
(* Qed. *)
(* Hint Resolve O_S: core. *)

(* XXX Andrej: Try to put back in, does not work with current Coq. *)
(* Theorem n_Sn : forall n:nat, n <> S n. *)
(* Proof. *)
(*   induction n; auto. *)
(* Qed. *)
(* Hint Resolve n_Sn: core. *)

(** addition *)

Fixpoint plus (n m:nat) : nat :=
  match n with
  | O => m
  | S p => S (p + m)
  end

where "n + m" := (plus n m) : nat_scope.

Hint Resolve (ap011 plus): v62.
Hint Resolve (ap011 (A:=nat) (B:=nat)): core.

Lemma plus_n_O : forall n:nat, n = n + 0.
Proof.
  induction n; simpl; auto.
Qed.
Hint Resolve plus_n_O: core.

Lemma plus_O_n : forall n:nat, 0 + n = n.
Proof.
  auto.
Qed.

Lemma plus_n_Sm : forall n m:nat, S (n + m) = n + S m.
Proof.
  intros n m; induction n; simpl; auto.
Qed.
Hint Resolve plus_n_Sm: core.

Lemma plus_Sn_m : forall n m:nat, S n + m = S (n + m).
Proof.
  auto.
Qed.

(** Standard associated names *)

Notation plus_0_r_reverse := plus_n_O (only parsing).
Notation plus_succ_r_reverse := plus_n_Sm (only parsing).

(** Multiplication *)

Fixpoint mult (n m:nat) : nat :=
  match n with
  | O => 0
  | S p => m + p * m
  end

where "n * m" := (mult n m) : nat_scope.

Hint Resolve (ap011 mult): core.

Lemma mult_n_O : forall n:nat, 0 = n * 0.
Proof.
  induction n; simpl; auto.
Qed.
Hint Resolve mult_n_O: core.

Lemma mult_n_Sm : forall n m:nat, n * m + n = n * S m.
Proof.
  intros; induction n as [| p H]; simpl; auto.
  destruct H; rewrite <- plus_n_Sm; apply eq_S.
  pattern m at 1 3; elim m; simpl; auto.
Qed.
Hint Resolve mult_n_Sm: core.

(** Standard associated names *)

Notation mult_0_r_reverse := mult_n_O (only parsing).
Notation mult_succ_r_reverse := mult_n_Sm (only parsing).

(** Truncated subtraction: [m-n] is [0] if [n>=m] *)

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O, _ => n
  | S k, O => n
  | S k, S l => k - l
  end

where "n - m" := (minus n m) : nat_scope.

(** Principle of double induction *)

Theorem nat_double_ind :
 forall R:nat -> nat -> Type,
   (forall n:nat, R 0 n) ->
   (forall n:nat, R (S n) 0) ->
   (forall n m:nat, R n m -> R (S n) (S m)) -> forall n m:nat, R n m.
Proof.
  induction n; auto.
  destruct m; auto.
Qed.

(** Maximum and minimum : definitions and specifications *)

Fixpoint max n m : nat :=
  match n, m with
    | O, _ => m
    | S n', O => n
    | S n', S m' => S (max n' m')
  end.

Fixpoint min n m : nat :=
  match n, m with
    | O, _ => 0
    | S n', O => 0
    | S n', S m' => S (min n' m')
  end.

(* Theorem max_l : forall n m : nat, m <= n -> max n m = n. *)
(* Proof. *)
(* induction n; destruct m; simpl; auto. inversion 1. *)
(* intros. apply f_equal. apply IHn. apply le_S_n. trivial. *)
(* Qed. *)

(* Theorem max_r : forall n m : nat, n <= m -> max n m = m. *)
(* Proof. *)
(* induction n; destruct m; simpl; auto. inversion 1. *)
(* intros. apply f_equal. apply IHn. apply le_S_n. trivial. *)
(* Qed. *)

(* Theorem min_l : forall n m : nat, n <= m -> min n m = n. *)
(* Proof. *)
(* induction n; destruct m; simpl; auto. inversion 1. *)
(* intros. apply f_equal. apply IHn. apply le_S_n. trivial. *)
(* Qed. *)

(* Theorem min_r : forall n m : nat, m <= n -> min n m = m. *)
(* Proof. *)
(* induction n; destruct m; simpl; auto. inversion 1. *)
(* intros. apply f_equal. apply IHn. apply le_S_n. trivial. *)
(* Qed. *)

(** [n]th iteration of the function [f] *)

Fixpoint nat_iter (n:nat) {A} (f:A->A) (x:A) : A :=
  match n with
    | O => x
    | S n' => f (nat_iter n' f x)
  end.

Lemma nat_iter_succ_r n {A} (f:A->A) (x:A) :
  nat_iter (S n) f x = nat_iter n f (f x).
Proof.
  induction n; intros; simpl; rewrite <- ?IHn; trivial.
Qed.

Theorem nat_iter_plus :
  forall (n m:nat) {A} (f:A -> A) (x:A),
    nat_iter (n + m) f x = nat_iter n f (nat_iter m f x).
Proof.
  induction n; intros; simpl; rewrite ?IHn; trivial.
Qed.

(** Preservation of invariants : if [f : A->A] preserves the invariant [Inv],
    then the iterates of [f] also preserve it. *)

Theorem nat_iter_invariant :
  forall (n:nat) {A} (f:A -> A) (P : A -> Type),
    (forall x, P x -> P (f x)) ->
    forall x, P x -> P (nat_iter n f x).
Proof.
  induction n; simpl; trivial.
  intros A f P Hf x Hx. apply Hf, IHn; trivial.
Qed.

(** END Stdlib file *)


Require Import HoTT.Types.Bool.
Require Import HoTT.TruncType HoTT.DProp.

(** We reopen these scopes so they take precedence over nat_scope; otherwise, now that we have [Coq.Init.Peano], we'd get [* : nat -> nat -> nat] rather than [* : Type -> Type -> Type]. *)
Global Open Scope type_scope.
Global Open Scope core_scope.

(** But in this file, we want to be able to use the usual symbols for natural number arithmetic. *)
Local Open Scope nat_scope.

Scheme nat_ind := Induction for nat Sort Type.
Scheme nat_rec := Minimality for nat Sort Type.


(** ** Arithmetic *)

Lemma nat_plus_n_O : forall n:nat, n = n + 0.
Proof.
  induction n.
  - reflexivity.
  - simpl; apply ap; assumption.
Defined.

Lemma nat_plus_n_Sm : forall n m:nat, (n + m).+1 = n + m.+1.
Proof.
  intros n m; induction n; simpl.
  - reflexivity.
  - apply ap; assumption.
Defined.

Definition nat_plus_comm (n m : nat) : n + m = m + n.
Proof.
  revert m; induction n as [|n IH]; intros m; simpl.
  - refine (nat_plus_n_O m).
  - transitivity (m + n).+1.
    + apply ap, IH.
    + apply nat_plus_n_Sm.
Qed.

(** ** Exponentiation *)

Fixpoint nat_exp (n m : nat) : nat
  := match m with
       | 0 => 1
       | S m => nat_exp n m * n
     end.

(** ** Factorials *)

Fixpoint factorial (n : nat) : nat
  := match n with
       | 0 => 1
       | S n => S n * factorial n
     end.

(* here ends the old Types/Nat.v and starts Spaces.v *)

(** Much of the layout of this file is adapted from ssreflect *)

(** ** Equality *)
(** *** Boolean equality and its properties *)

Fixpoint code_nat (m n : nat) {struct m} : DHProp :=
  match m, n with
    | 0, 0 => True
    | m'.+1, n'.+1 => code_nat m' n'
    | _, _ => False
  end.

Infix "=n" := code_nat : nat_scope.

Fixpoint idcode_nat {n} : (n =n n) :=
  match n as n return (n =n n) with
    | 0 => tt
    | S n' => @idcode_nat n'
  end.

Fixpoint path_nat {n m} : (n =n m) -> (n = m) :=
  match m as m, n as n return (n =n m) -> (n = m) with
    | 0, 0 => fun _ => idpath
    | m'.+1, n'.+1 => fun H : (n' =n m') => ap S (path_nat H)
    | _, _ => fun H => match H with end
  end.

Global Instance isequiv_path_nat {n m} : IsEquiv (@path_nat n m).
Proof.
  refine (isequiv_adjointify
            (@path_nat n m)
            (fun H => transport (fun m' => (n =n m')) H idcode_nat)
            _ _).
  { intros []; simpl.
    induction n; simpl; trivial.
    by destruct (IHn^)%path. }
  { intro. apply path_ishprop. }
Defined.

Definition equiv_path_nat {n m} : (n =n m) <~> (n = m)
  := Build_Equiv _ _ (@path_nat n m) _.

Global Instance decidable_paths_nat : DecidablePaths nat
  := fun n m => decidable_equiv _ (@path_nat n m) _.

Corollary hset_nat : IsHSet nat.
Proof.
  exact _.
Defined.

(** ** Natural number ordering *)

Definition leq m n := ((m - n) =n 0).
Definition lt m n := leq (m.+1) n.

Notation "m <= n" := (leq m n) : nat_scope.
Notation "m < n" := (lt m n) : nat_scope.
Notation "m >= n" := (n <= m) (only parsing) : nat_scope.
Notation "m > n" := (n < m) (only parsing) : nat_scope.

(** ** Theorems about natural number ordering *)

Fixpoint leq0n {n} : 0 <= n :=
  match n as n return 0 <= n with
    | 0 => tt
    | n'.+1 => @leq0n n'
  end.

Fixpoint subnn {n} : n - n =n 0 :=
  match n as n return n - n =n 0 with
    | 0 => tt
    | n'.+1 => @subnn n'
  end.

Global Instance leq_refl : Reflexive leq
  := @subnn.

Fixpoint leqnSn {n} : n <= S n :=
  match n as n return n <= S n with
  | 0 => tt
  | n'.+1 => @leqnSn n'
  end.

Fixpoint leq_transd {x y z} : (x <= y -> y <= z -> x <= z)%dprop :=
  match x as x, y as y, z as z return (x <= y -> y <= z -> x <= z)%dprop with
    | 0, 0, 0 => dprop_istrue
    | x'.+1, 0, 0 => dprop_istrue
    | 0, y'.+1, 0 => dprop_istrue
    | 0, 0, z'.+1 => dprop_istrue
    | x'.+1, y'.+1, 0 => dprop_istrue
    | x'.+1, 0, z'.+1 => dprop_istrue
    | 0, y'.+1, z'.+1 => @leq_transd 0 y' z'
    | x'.+1, y'.+1, z'.+1 => @leq_transd x' y' z'
  end.

Global Instance leq_trans : Transitive (fun n m => leq n m)
  := @leq_transd.

Fixpoint leq_antisymd {x y} : (x <= y -> y <= x -> x =n y)%dprop :=
  match x as x, y as y return (x <= y -> y <= x -> x =n y)%dprop with
    | 0, 0 => dprop_istrue
    | x'.+1, y'.+1 => @leq_antisymd x' y'
    | _, _ => dprop_istrue
  end.

Lemma leq_antisym : forall {x y}, x <= y -> y <= x -> x = y.
Proof.
  intros x y p q.
  apply path_nat.
  apply leq_antisymd; assumption.
Defined.

Definition not_nltn n : ~ (n < n).
Proof.
  induction n as [|n IH]; simpl.
  - auto.
  - apply IH.
Defined.

Definition leq1Sn {n} : 1 <= n.+1 := tt.

Fixpoint leqdichot {m} {n} : ((m <= n) + (m > n))%type.
Proof.
  induction m, n.
  - left; reflexivity.
  - left; apply leq0n.
  - right; unfold lt; apply leq1Sn.
  - assert ((m <= n) + (n < m)) as X by apply leqdichot.
    induction X as [leqmn|ltnm].
    + left; assumption.
    + right; assumption.
Defined.

Lemma leq_n n : leq n n.
Proof.
  apply subnn.
Defined.

Lemma leq_S : forall n m, leq n m -> leq n (S m).
Proof.
  intros n m p.
  rapply leq_trans.
  1: exact p.
  exact leqnSn.
Defined.

Definition geq (n m : nat) := m <= n.
Hint Unfold geq : core.

(* Local Infix ">=" := ge : nat_scope. *)

Definition gt (n m:nat) := m < n.
Hint Unfold gt: core.

(* Local Infix ">" := gt : nat_scope. *)

Local Notation "x <= y <= z" := (x <= y /\ y <= z) : nat_scope.
Local Notation "x <= y < z" := (x <= y /\ y < z) : nat_scope.
Local Notation "x < y < z" := (x < y /\ y < z) : nat_scope.
Local Notation "x < y <= z" := (x < y /\ y <= z) : nat_scope.

Theorem leq_pred : forall n m, n <= m -> pred n <= pred m.
Proof.
  intros n m p.
  destruct n.
  1: exact tt.
  destruct m.
  1: destruct p.
  exact p.
Defined.

Theorem leq_S_n : forall n m, S n <= S m -> n <= m.
Proof.
intros n m. exact (leq_pred (S n) (S m)).
Qed.
