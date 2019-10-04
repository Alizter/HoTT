Require Import Basics.
Require Import Types.
Require Import Pointed.Core.
Require Import Pointed.pHomotopy.

Local Open Scope pointed_scope.
Local Open Scope path_scope.

(* By function extensionality pointed homotopies are equivalent to paths *)
Definition equiv_path_pmap `{Funext} {A B : pType} (f g : A ->* B)
  : (f ==* g) <~> (f = g).
Proof.
  refine ((equiv_ap' (issig_pmap A B)^-1 f g)^-1 oE _); cbn.
  refine (_ oE (issig_phomotopy f g)^-1).
  refine (equiv_path_sigma _ _ _ oE _); cbn.
  refine (equiv_functor_sigma' (equiv_path_arrow f g) _); intros p. cbn.
  refine (_ oE equiv_moveL_Vp _ _ _).
  refine (_ oE equiv_path_inverse _ _).
  apply equiv_concat_l.
  refine (transport_paths_Fl (path_forall f g p) (point_eq f) @ _).
  apply whiskerR, inverse2.
  refine (ap_apply_l (path_forall f g p) (point A) @ _).
  apply ap10_path_forall.
Defined.

Definition path_pmap `{Funext} {A B : pType} {f g : A ->* B}
  : (f ==* g) -> (f = g) := equiv_path_pmap f g.

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

Definition pmap_postcompose_idmap {A B : pType} (f : A ->* B)
: pmap_idmap o* f ==* f.
Proof.
  serapply Build_pHomotopy.
  1: reflexivity.
  refine (concat_1p _ @ _ @ (concat_p1 _)^).
  symmetry.
  apply ap_idmap.
Defined.



(* postcomposing the zero map is the zero map *)
Lemma pmap_postcompose_const {A B C : pType} (f : B ->* C)
  : f o* @pmap_const A B ==* pmap_const.
Proof.
  serapply Build_pHomotopy.
  1: intro; apply point_eq.
  exact (concat_p1 _ @ (concat_1p _)^).
Defined.

(* precomposing the zero map is the zero map *)
Lemma pmap_precompose_const {A B C : pType} (f : A ->* B)
  : pmap_const o* f ==* @pmap_const A C.
Proof.
  serapply Build_pHomotopy.
  1: reflexivity.
  refine (ap (fun x => concat x 1) (ap_const _ _)^).
Defined.

Definition path_pmap_refl `{Funext} {A B} {x : A ->* B}
  : path_pmap (phomotopy_reflexive x) = 1%path.
Proof.
  unfold phomotopy_reflexive.
  apply moveR_equiv_M.
  cbn.
  apply ap.
  pointed_reduce.
  rewrite transport_paths_FlFr.
  rewrite ap_idmap.
  hott_simpl.
  unfold ap10_path_forall.
  unfold apD10_path_forall.
  rewrite eisadj.
  rewrite transport_paths_FlFr.
  rewrite ap_idmap.
Admitted.

(*
Definition path_pmap_ap `{Funext} {A B C D : pType} {f g : A ->* B} (p : f ==* g)
  (h : (A ->* B) -> (C ->* D))
  : ap h (path_pmap p) = path_pmap (phomotopy_ap h p).
Proof.
  unfold phomotopy_ap.
  destruct (path_pmap p).
  simpl.
  symmetry.
  apply path_pmap_refl.
Defined. *)

Definition path_pmap_pp `{Funext} {A B : pType} {f g h : A ->* B}
  (p : f ==* g) (q : g ==* h) : path_pmap p @ path_pmap q = path_pmap (p @* q).
Proof.
Admitted.



(* Any map from the unit type must be a constant map *)
Lemma punit_ind_const {X : pType} (f : punit ->* X)
  : f ==* pmap_const.
Proof.
  serapply Build_pHomotopy.
  + rapply Unit_ind.
    erapply point_eq.
  + apply concat_p1.
Defined.

(* TODO: Do we really need this, should this generally apply to any contr? *)
(* Here is a variant that allows for types to simply be equal to unit *)
Lemma punit_ind_const' {X Y : pType} (f : Y ->* X) (p : Y = punit)
  : f ==* pmap_const.
Proof.
  destruct p^.
  apply punit_ind_const.
Defined.


