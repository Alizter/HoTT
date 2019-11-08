Require Import Basics Types PathAny.
Require Import Pointed.Core.
Require Import Pointed.pHomotopy.

Local Open Scope pointed_scope.
Local Open Scope path_scope.

(* By function extensionality pointed homotopies are equivalent to paths *)
Definition equiv_path_pmap `{Funext} {A B : pType} (f g : A ->* B)
  : (f ==* g) <~> (f = g).
Proof.
  refine (_ oE (issig_phomotopy f g)^-1).
  eqp_issig_contr (issig_pmap A B).
  { intros [f feq]; cbn.
    exists (fun a => 1%path).
    apply concat_1p. }
  intros [f feq]; cbn.
  contr_sigsig f (fun a:A => idpath (f a)); cbn.
  refine (contr_equiv' {feq' : f (point A) = point B & feq = feq'} _).
  refine (equiv_functor_sigma' (equiv_idmap _) _); intros p.
  refine (equiv_path_inverse _ _ oE _).
  apply equiv_concat_r. symmetry; apply concat_1p.
Defined.

Definition path_pmap `{Funext} {A B : pType} {f g : A ->* B}
  : (f ==* g) -> (f = g) := equiv_path_pmap f g.

Global Instance isequiv_path_pmap `{Funext} {A B : pType} {f g : A ->* B}
  : IsEquiv (@path_pmap _ A B f g).
Proof.
  unfold path_pmap.
  apply equiv_isequiv.
Defined.

(* We note that the inverse of [path_pmap] computes definitionally on reflexivity, and hence [path_pmap] itself computes typally so.  *)
Definition equiv_inverse_path_pmap_1 `{Funext} {A B} {f : A ->* B}
  : (equiv_path_pmap f f)^-1 1%path = reflexivity f
  := 1.

Definition path_pmap_1 `{Funext} {A B} {f : A ->* B}
  : path_pmap (reflexivity f) = 1%path.
Proof.
  apply moveR_equiv_M.
  reflexivity.
Defined.

(** ** Associativity of pointed map composition *)

Definition pmap_compose_assoc {A B C D : pType} (h : C ->* D)
  (g : B ->* C) (f : A ->* B) : (h o* g) o* f ==* h o* (g o* f).
Proof.
  serapply Build_pHomotopy.
  1: reflexivity.
  by pointed_reduce.
Defined.

Definition pmap_precompose_idmap {A B : pType} (f : A ->* B)
  : f o* pmap_idmap ==* f.
Proof.
  serapply Build_pHomotopy.
  all: reflexivity.
Defined.

Definition path_pmap_precompose_idmap {A B : pType} (f : A ->* B)
  : f o* pmap_idmap = f.
Proof.
  by pointed_reduce.
Defined.

Definition pmap_postcompose_idmap {A B : pType} (f : A ->* B)
  : pmap_idmap o* f ==* f.
Proof.
  serapply Build_pHomotopy.
  1: reflexivity.
  refine (concat_1p _ @ _ @ (concat_p1 _)^).
  symmetry.
  apply ap_idmap.
Defined.

Definition path_pmap_postcompose_idmap {A B : pType} (f : A ->* B)
  : pmap_idmap o* f = f.
Proof.
  by pointed_reduce.
Defined.

(* precomposing the zero map is the zero map *)
Lemma pmap_precompose_const {A B C : pType} (f : B ->* C)
  : f o* @pmap_const A B ==* pmap_const.
Proof.
  serapply Build_pHomotopy.
  1: intro; apply point_eq.
  exact (concat_p1 _ @ (concat_1p _)^).
Defined.

(* postcomposing the zero map is the zero map *)
Lemma pmap_postcompose_const {A B C : pType} (f : A ->* B)
  : pmap_const o* f ==* @pmap_const A C.
Proof.
  serapply Build_pHomotopy.
  1: reflexivity.
  refine (ap (fun x => concat x 1) (ap_const _ _)^).
Defined.

Lemma pmap_punit_const {A : pType} {f : A ->* punit} : f ==* pmap_const.
Proof.
  serapply Build_pHomotopy.
  1: intro; apply path_unit.
  refine (concat_p1 _ @ _).
  apply eta_path_unit.
Defined.

Lemma pmap_const_factor {A B : pType} {f : punit ->* B} {g : A ->* punit}
  : f o* g ==* pmap_const.
Proof.
  refine (_ @* pmap_precompose_const f).
  apply pmap_postwhisker.
  apply pmap_punit_const.
Defined.

Definition hap `{Funext} {A B C D : pType}
  {f g : A ->* B} (h : (A ->* B) -> (C ->* D))
  : f ==* g -> h f ==* h g.
Proof.
  intro p.
  serapply Build_pHomotopy.
  1: by apply ap10, ap, ap, path_pmap.
  destruct (path_pmap p).
  apply concat_1p.
Defined.

Definition path_pmap_ap `{Funext} {A B C D : pType}
  {f g : A ->* B} (p : f ==* g)
  (h : (A ->* B) -> (C ->* D))
  : ap h (path_pmap p) = path_pmap (hap h p).
Proof.
  unfold hap.
  destruct (path_pmap p).
  symmetry.
  apply path_pmap_1.
Defined.

Definition path_pmap_pp `{Funext}
  {A B : pType} {f g h : A ->* B}
  (p : f ==* g) (q : g ==* h)
  : path_pmap p @ path_pmap q = path_pmap (p @* q).
Proof.
  set (p' := path_pmap p).
  set (q' := path_pmap q).
  rewrite <- (eissect path_pmap p).
  rewrite <- (eissect path_pmap q).
  change (path_pmap p) with p'.
  change (path_pmap q) with q'.
  clearbody p' q'; clear p q.
  destruct p', q'.
  apply moveL_equiv_M.
  rewrite !equiv_inverse_path_pmap_1.
  by pointed_reduce.
Defined.

