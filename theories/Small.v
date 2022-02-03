Require Import Basics Types HFiber.
Require Import PropResizing.

(** Adapted from the formalization of Dan Christensen's "Non-accessible localizations".

The formalization NonAccessible: https://github.com/jdchristensen/NonAccessible *)


(* Facts about "small" types and non-accessible localizations. *)

(* Universe variables:  we most often use a subset of [i j k u].  We think of [Type@{i}] as containing the "small" types and [Type@{j}] the "large" types.  In some early results, there are no constraints between [i] and [j], and in others we require that [i <= j], as expected.  While the case [i = j] isn't particularly interesting, we put some effort into ensuring that it is permitted as well, as there is no semantic reason to exclude it.  The universe variable [k] should be thought of as max(i+1,j), and it is generally required to satisfy [i < k] and [j <= k].  If we assume that [i < j], then we can take [k = j], but we include [k] so that we also allow the case [i = j].  The universe variable [u] is only present because we occasionally use Univalence in [Type@{k}], so the equality types need a larger universe to live in.  Because of this, most results require [k < u].

Summary of the most common situation:  [i < k < u, j <= k], where [i] is for the small types, [j] is for the large types, [k = max(i+1,j)] and [u] is an ambient universe for Univalence.

We include universe annotations when they clarify the meaning (e.g. in [IsSmall] and when using [PropResizing]), and also when it is required in order to keep control of the universe variables. *)

(* We say that [X : Type@{j}] is small (relative to Type@{i}) if it is equivalent to a type in [Type@{i}].  We use a record to avoid an extra universe variable.  This version has no constraints on i and j.  It lands in max(i+1,j), as expected. *)
Class IsSmall@{i j | } (X : Type@{j}) := {
  smalltype : Type@{i} ;
  equiv_smalltype : smalltype <~> X
}.
Arguments smalltype {X} _.
Arguments equiv_smalltype {X} _.
Coercion smalltype : IsSmall >-> Sortclass.

Definition lift_issmall@{i j k | j <= k}
           (X : Type@{j})
           (sX : IsSmall@{i j} X)
  : IsSmall@{i k} X
  := Build_IsSmall X (smalltype sX) (equiv_smalltype sX).

Definition lower_issmall@{i j k | j <= k}
           (X : Type@{j})
           (sX : IsSmall@{i k} X)
  : IsSmall@{i j} X
  := Build_IsSmall X (smalltype sX) (equiv_smalltype sX).

Global Instance ishprop_issmall@{i j k | i < k, j <= k} `{Univalence}
  (X : Type@{j}) : IsHProp (IsSmall@{i j} X).
Proof.
  apply hprop_inhabited_contr.
  intros [Z e].
  (* [IsSmall X] is equivalent to [IsSmall Z], which is contractible since it is a based path space. *)
  rapply (istrunc_equiv_istrunc@{k k} { Y : Type@{i} & Y <~> Z } _).
  - refine (_ oE _).
    1: issig.
    apply equiv_functor_sigma_id.
    intro Y.
    exact (equiv_functor_equiv@{i i i j k k} equiv_idmap e).
Defined.

(* A type in [Type@{i}] is clearly small. *)
Global Instance issmall_in@{i j | i <= j} (X : Type@{i}) : IsSmall@{i j} X
  := Build_IsSmall X X equiv_idmap.

(* The small types are closed under equivalence. *)
(* No constraints on i, j1 and j2. *)
Definition issmall_equiv_issmall@{i j1 j2 | } {A : Type@{j1}} {B : Type@{j2}}
  (e : A <~> B) (sA : IsSmall@{i j1} A)
  : IsSmall@{i j2} B.
Proof.
  exists (smalltype sA).
  exact (e oE (equiv_smalltype sA)).
Defined.

(* The small types are closed under dependent sums. *)
Global Instance sigma_closed_issmall@{i j | } {A : Type@{j}}
  (B : A -> Type@{j}) (sA : IsSmall@{i j} A)
  (sB : forall a, IsSmall@{i j} (B a))
  : IsSmall@{i j} { a : A & B a }.
Proof.
  exists { a : (smalltype sA) & (smalltype (sB (equiv_smalltype sA a))) }.
  snrapply equiv_functor_sigma'; intros; apply equiv_smalltype.
Defined.

(* If a map has small codomain and fibers, then the domain is small. *)
Definition issmall_codomain_fibers_small@{i j | } {X Y : Type@{j}}
           (f : X -> Y)
           (sY : IsSmall@{i j} Y)
           (sF : forall y : Y, IsSmall@{i j} (hfiber f y))
  : IsSmall@{i j} X.
Proof.
  nrapply issmall_equiv_issmall.
  - exact (equiv_fibration_replacement f)^-1%equiv.
  - apply sigma_closed_issmall; assumption.
Defined.

(* Propositional Resizing says that every (-1)-truncated type is small. *)
(* No constraints on i and j. *)
Definition issmall_hprop@{i j | } `{PropResizing}
  (X : Type@{j}) (T : IsTrunc (-1) X)
  : IsSmall@{i j} X.
Proof.
  exists (resize_hprop@{j i} X).
  apply (equiv_resize_hprop X)^-1%equiv.
Defined.

(* Every contractible, i.e. (-2)-truncated type, is small. *)
Definition issmall_contr@{i j| } (X : Type@{j}) (T : IsTrunc (-2) X): IsSmall@{i j} X.
Proof.
  exact (issmall_equiv_issmall (equiv_contr_unit)^-1 _).
Defined.

(* This isn't yet in the paper. It lets us simplify the statement of Proposition 2.8. *)
Definition issmall_inhabited_issmall@{i j k u | i < k, j <= k, k < u}
  `{PropResizing} `{Univalence}
  (X : Type@{j}) (isX : X -> IsSmall@{i j} X)
  : IsSmall@{i j} X.
Proof.
  (* Since IsSmall@{i j} lives in a universe larger than [i] and we're not assuming [i <= j], we have to pass through universe [k], which we think of as max(i+1,j). *)
  apply lower_issmall.
  (* Now the goal is IsSmall@{i k} X. *)
  apply (issmall_codomain_fibers_small isX).
  - rapply issmall_hprop.
  - intro sX.
    apply sigma_closed_issmall.
    1: apply (lift_issmall _ sX).
    intro x.
    rapply issmall_contr.
Defined.

(* Locally small types. *)

(* We say that a type [X] is 0-locally small if it is small, and (n+1)-locally small if its identity types are n-small. *)
Fixpoint IsLocallySmall@{i j k | i < k, j <= k} (n : nat) (X : Type@{j}) : Type@{k}
  := match n with
    | 0%nat => IsSmall@{i j} X
    | S m => forall x y : X, IsLocallySmall m (x = y)
    end.
Existing Class IsLocallySmall.
#[export] Typeclasses Transparent IsLocallySmall.

Global Instance islocallysmall0 {A} : IsSmall A -> IsLocallySmall 0 A.
Proof.
  by unfold IsLocallySmall.
Defined.

Global Instance ishprop_islocally_small@{i j k u | i < k, j <= k, k <= u, j < u}
  `{Univalence} (n : nat) (X : Type@{j})
  : IsHProp@{k} (IsLocallySmall@{i j k} n X).
Proof.
  (* We use [simple_induction] to control the universe variable. *)
  revert X; simple_induction n n IHn; exact _.
Defined.

Definition islocally_small_in@{i j k | i <= j, j <= k, i < k} (n : nat) (X : Type@{i})
  : IsLocallySmall@{i j k} n X.
Proof.
  revert X.
  induction n; intro X.
  - apply issmall_in.
  - intros x y.
    exact (IHn (x = y)).
Defined.

(* The locally small types are closed under equivalence. *)
Definition islocally_small_equiv_islocally_small
  @{i j1 j2 k u | i < k, j1 <= k, j2 <= k, k <= u, j1 < u, j2 < u}
  (n : nat) {A : Type@{j1}} {B : Type@{j2}}
  (e : A <~> B) (lsA : IsLocallySmall@{i j1 k} n A)
  : IsLocallySmall@{i j2 k} n B.
Proof.
  revert A B e lsA.
  simple_induction n n IHn.
  - exact @issmall_equiv_issmall@{i j1 j2}.
  - intros A B e lsA b b'.
    nrapply IHn.
    * exact (equiv_ap' (e^-1%equiv) b b')^-1%equiv.
    * apply lsA.
Defined.

Global Instance sigma_closed_islocally_small
  @{i j k u | i < k, j <= k, k <= u, j < u}
  (n : nat) {A : Type@{j}} (B : A -> Type@{j})
  (lsA : IsLocallySmall@{i j k} n A)
  (lsB : forall a, IsLocallySmall@{i j k} n (B a))
  : IsLocallySmall@{i j k} n { a : A & B a }.
Proof.
  revert A B lsA lsB.
  simple_induction n n IHn.
  - exact @sigma_closed_issmall.
  - intros A B lsA lsB x y.
    apply (islocally_small_equiv_islocally_small n (equiv_path_sigma _ x y)).
    apply IHn.
    * apply lsA.
    * intro p.
      apply lsB.
Defined.

(* If a map has locally small codomain and fibers, then the domain is locally small. *)
Definition islocally_small_codomain_fibers_locally_small
  @{i j k u | i < k, j <= k, k <= u, j < u}
  (n : nat) {X Y : Type@{j}} (f : X -> Y)
  (sY : IsLocallySmall@{i j k} n Y)
  (sF : forall y : Y, IsLocallySmall@{i j k} n (hfiber f y))
  : IsLocallySmall@{i j k} n X.
Proof.
  nrapply islocally_small_equiv_islocally_small@{i j j k u}.
  - exact (equiv_fibration_replacement f)^-1%equiv.
  - apply sigma_closed_islocally_small; assumption.
Defined.

(* A small type is n-locally small for all n. *)
Global Instance islocally_small_small
  @{i j k u | i < k, j <= k, k <= u, j < u} (n : nat)
  (X : Type@{j}) (sX : IsSmall@{i j} X)
  : IsLocallySmall@{i j k} n X.
Proof.
  apply (islocally_small_equiv_islocally_small@{i i j k u} n (equiv_smalltype sX)).
  apply islocally_small_in.
Defined.

(** TODO: move *)
(* Sends a trunc_index [m] to the natural number [m+2]. *)
Fixpoint trunc_index_to_nat (m : trunc_index) : nat
:= match m with
     | minus_two => 0
     | m'.+1 => (trunc_index_to_nat m').+1
   end.

(* Under Propositional Resizing, every (n+1)-truncated type is (n+2)-locally small. This is Lemma 2.3 in the paper. *)
Definition islocally_small_trunc@{i j k u | i < k, j <= k, k <= u, j < u}
  `{PropResizing} (n : trunc_index) (X : Type@{j}) (T : IsTrunc n.+1 X)
  : IsLocallySmall@{i j k} (trunc_index_to_nat n) X.
Proof.
  revert n X T.
  rapply trunc_index_rect@{u}; cbn.
  - nrapply issmall_hprop.
  - intros n IHn X T x y.
    rapply IHn.
Defined.
