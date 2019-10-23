Require Import Basics.
Require Import Types.
Require Import Pointed.Core.

Local Open Scope pointed_scope.

(* pointed homotopy is a reflexive relation *)
Global Instance phomotopy_reflexive {A B} : Reflexive (@pHomotopy A B).
Proof.
  intro.
  serapply Build_pHomotopy.
  + apply apD10; reflexivity.
  + apply concat_1p.
Defined.

Definition phomotopy_paths {A B} {f g : A ->* B}
  : f = g -> f ==* g.
Proof.
  by intros [].
Defined.

(** ** Whiskering of pointed homotopies by pointed functions *)

Definition pmap_postwhisker {A B C : pType} {f g : A ->* B}
  (h : B ->* C) (p : f ==* g) : h o* f ==* h o* g.
Proof.
  serapply Build_pHomotopy.
  1: intro; cbn; apply ap, p.
  refine (concat_p_pp _ _ _ @ _).
  apply whiskerR; cbn.
  refine ((ap_pp _ _ _)^ @ _).
  apply ap.
  by destruct p.
Defined.

Definition pmap_prewhisker {A B C : pType} (f : A ->* B)
  {g h : B ->* C} (p : g ==* h) : g o* f ==* h o* f.
Proof.
  serapply Build_pHomotopy.
  1: intro; cbn; apply p.
  by pointed_reduce.
Defined.


(** ** Composition of pointed homotopies *)

Definition phomotopy_compose {A B : pType} {f g h : A ->* B}
  (p : f ==* g) (q : g ==* h) : f ==* h.
Proof.
  pointed_reduce.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros x; exact (p x @ q x).
  - apply concat_p1.
Defined.

Infix "@*" := phomotopy_compose : pointed_scope.

(* pointed homotopy is a transitive relation *)
Global Instance phomotopy_transitive {A B} : Transitive (@pHomotopy A B)
  := @phomotopy_compose A B.

Definition phomotopy_inverse {A B : pType} {f g : A ->* B}
: (f ==* g) -> (g ==* f).
Proof.
  intros p; pointed_reduce.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros x; exact ((p x)^).
  - apply concat_Vp.
Defined.

(* pointed homotopy is a symmetric relation *)
Global Instance phomotopy_symmetric {A B} : Symmetric (@pHomotopy A B)
  := @phomotopy_inverse A B.


Notation "p ^*" := (phomotopy_inverse p) : pointed_scope.

Definition issig_phomotopy {A B : pType} (f g : A ->* B)
: { p : f == g & p (point A) @ point_eq g = point_eq f } <~> (f ==* g).
Proof.
  issig.
Defined.

Lemma pmap_const_factor {A B : pType} {f : punit ->* B} {g : A ->* punit}
  : f o* g ==* pmap_const.
Proof.
  serapply Build_pHomotopy.
  { pointed_reduce.
    intro x.
    cbv.
    apply ap.
    apply path_unit. }
  pointed_reduce.
  by match goal with |- ap f (path_unit ?p _) = _
    => destruct p end.
Defined.


