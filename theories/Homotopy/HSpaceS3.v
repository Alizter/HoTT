From HoTT Require Import Basics.
Require Import Types.Paths Types.Universe.
Require Import Classes.interfaces.abstract_algebra.
Require Import Pointed.Core Pointed.pEquiv Pointed.pSusp.
Require Import Spaces.Spheres.
Require Import Homotopy.Suspension Homotopy.HSpace.Core.
Require Import Homotopy.HSpaceS1 Homotopy.CayleyDickson.
Require Import Homotopy.Join.Core Homotopy.Join.JoinSusp.

Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.

(** * The H-space structure on the 3-sphere *)

#[export] Instance negate_s0 : Negate (Sphere 0) := susp_neg Empty.

#[export] Instance involutive_negate_s0 : Involutive negate_s0
  := susp_neg_inv Empty.

Definition conjugate_s1_beta_loop
  : ap (conj : Sphere 1 -> Sphere 1)
      (merid North @ (merid South)^)
    = (merid North @ (merid South)^)^.
Proof.
  rhs napply inv_pV.
  napply Susp_rec_beta_zigzag.
Defined.

#[export] Instance conjugate_s1_left_inverse
  : LeftInverse sgop_s1 conj North.
Proof.
  snapply Sph1_ind.
  - reflexivity.
  - transport_paths' (transport_paths_Fl
      (f:=fun x : Sphere 1 => sgop_s1 (conj x) x)).
    symmetry.
    lhs napply concat_p1.
    pose (l := merid (North : Sphere 0) @ (merid South)^).
    lhs_V napply (ap011_diag (fun x y => sgop_s1 (conj y) x) l).
    lhs napply (ap011_is_ap (fun x y => sgop_s1 (conj y) x)).
    lhs napply (ap_idmap l @@ 1).
    lhs napply (1 @@ ap_compose conj (fun z => sgop_s1 z North) l).
    lhs napply (1 @@ ap (ap (fun z => sgop_s1 z North))
      conjugate_s1_beta_loop).
    lhs rapply (1 @@ equiv_p1_1q^-1
      (concat_A1p rightidentity_s1 l^)).
    apply concat_pV.
Defined.

#[export] Instance factorneg_r_s1
  : FactorNegRight (negate_susp (Sphere 0) negate_s0) sgop_s1.
Proof.
  pose (N := fun x : Sphere 1 =>
    ap (susp_neg (Sphere 0)) (susp_neg_stable Empty x)
      @ susp_neg_inv (Sphere 0) x).
  intros x y.
  exact (ap (sgop_s1 x) (N y) @ (N (sgop_s1 x y))^).
Defined.

#[export] Instance cdi_s0 `{Univalence}
  : CayleyDicksonImaginaroid (Sphere 0)
  := Build_CayleyDicksonImaginaroid_assoc.

#[export] Instance hspace_s3 `{Univalence} : IsHSpace (psphere 3).
Proof.
  napply (ishspace_equiv_hspace (pequiv_pjoin_sphere 1 1)^-1*).
  rapply (hspace_cdi_susp_assoc (A:=Sphere 0)).
Defined.
