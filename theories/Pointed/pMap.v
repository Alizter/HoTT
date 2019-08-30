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
  pointed_reduce.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros ?; reflexivity.
  - reflexivity.
Defined.

Definition pmap_precompose_idmap {A B : pType} (f : A ->* B)
: f o* pmap_idmap ==* f.
Proof.
  by pointed_reduce.
Defined.

Definition pmap_postcompose_idmap {A B : pType} (f : A ->* B)
: pmap_idmap o* f ==* f.
Proof.
  by pointed_reduce.
Defined.

(* A kind of ap for pHomotopies *)
Definition phomotopy_ap `{Funext} {A B C D : pType} {f g : A ->* B}
  (h : (A ->* B) -> C ->* D) : f ==* g -> h f ==* h g.
Proof.
  intro p.
  serapply Build_pHomotopy.
  { apply ap10.
    apply ap, ap.
    apply path_pmap.
    assumption. }
  destruct (path_pmap p).
  apply concat_1p.
Defined.

(* The canonical constant/zero map *)
Definition pmap_const {A B : pType} : A ->* B
  := Build_pMap _ _ (const (point B)) 1.

(* postcomposing the zero map is the zero map *)
Lemma pmap_postcompose_const {A B C : pType} (f : B ->* C)
  : f o* @pmap_const A B ==* pmap_const.
Proof.
  by pointed_reduce.
Defined.

(* precomposing the zero map is the zero map *)
Lemma pmap_precompose_const {A B C : pType} (f : A ->* B)
  : pmap_const o* f ==* @pmap_const A C.
Proof.
  by pointed_reduce.
Defined.

Definition path_pmap_refl `{Funext} {A B} {x : A ->* B}
  : path_pmap (phomotopy_reflexive x) = 1%path.
Proof.
  unfold phomotopy_reflexive.
  apply moveR_equiv_M.
  cbn.
  apply ap.
  rewrite ? inv_V.
  unfold whiskerR.
  unfold inverse2.
  refine ((concat_1p _)^ @ _).
  rewrite concat_p_pp.
  refine (whiskerR _ _).
  apply moveL_pV.
  refine (concat_1p _ @ _).
  pointed_reduce.
  apply moveR_Vp.
  rewrite concat_p1.
  rewrite concat2_p1.
  set (whiskerR_p1 (ap inverse (ap10_path_forall x x (apD10 1) ispointed_type0))).
  apply moveL_pV in p.
  apply moveL_Vp in p.
  rewrite p; clear p.
  hott_simpl.
  change (transport
  (fun p : x = x => transport
    (fun f : A -> B => f ispointed_type0 = x ispointed_type0) p 1 = 1)
    (eissect apD10 1)^ 1
    = (transport_paths_Fl (path_forall x x (apD10 1)) 1 @
    concat_p1 (ap10 (path_forall x x (apD10 1)) ispointed_type0)^) @
    ap inverse (ap10_path_forall x x (apD10 1) ispointed_type0)).
  change (transport
  (fun p : x = x => transport
    (fun f : A -> B => f ispointed_type0 = x ispointed_type0) p 1 = 1)
    (eissect apD10 1)^ 1
    = (transport_paths_Fl (apD10^-1 (apD10 1)) 1 @
    concat_p1 (ap10 (path_forall x x (apD10 1)) ispointed_type0)^) @
    ap inverse (ap10_path_forall x x (apD10 1) ispointed_type0)).
Admitted.

Definition path_pmap_ap `{Funext} {A B C D : pType} {f g : A ->* B} (p : f ==* g)
  (h : (A ->* B) -> (C ->* D))
  : ap h (path_pmap p) = path_pmap (phomotopy_ap h p).
Proof.
  unfold phomotopy_ap.
  destruct (path_pmap p).
  simpl.
  symmetry.
  apply path_pmap_refl.
Defined.

Definition path_pmap_pp `{Funext} {A B : pType} {f g h : A ->* B}
  (p : f ==* g) (q : g ==* h) : path_pmap p @ path_pmap q = path_pmap (p @* q).
Proof.
  set (q' := path_pmap q).
  rewrite <- (eissect path_pmap q).
  change (path_pmap q) with q'.
  clearbody q'; clear q.
  destruct q'.
  set (p' := path_pmap p).
  rewrite <- (eissect path_pmap p).
  change (path_pmap p) with p'.
  clearbody p'; clear p.
  destruct p'.
  symmetry.
  refine (_ @ path_pmap_refl).
  apply ap.
  set (@path_pmap_refl _ _ _ f).
  apply (moveL_equiv_V _ _) in p.
  symmetry in p.
  rewrite p.
  cbv.
  by pointed_reduce.
Defined.

(* Pointed version of unit type *)
Notation punit := (Build_pType Unit tt).

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

(* note pMaps are pTypes *)
(* I wonder, can we get away with defining pointed maps as pTypes ? *)
Global Instance ispointed_pmap {A B} : IsPointed (A ->* B) := pmap_const.









