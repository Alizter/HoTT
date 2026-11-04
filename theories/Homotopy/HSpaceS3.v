From HoTT Require Import Basics.
Require Import Types.Universe.
Require Import Classes.interfaces.abstract_algebra.
Require Import Pointed.Core Pointed.pEquiv Pointed.pSusp.
Require Import Spaces.Spheres.
Require Import Homotopy.Suspension.
Require Import Homotopy.HSpace.Core Homotopy.HSpace.Coherent.
Require Import Homotopy.HSpaceS1 Homotopy.CayleyDickson.
Require Import Homotopy.Join.Core Homotopy.Join.JoinSusp.

Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.

(** * The H-space structure on the 3-sphere *)

#[export] Instance negate_s0 : Negate (Sphere 0) := susp_neg Empty.

#[export] Instance involutive_negate_s0 : Involutive negate_s0
  := susp_neg_inv Empty.

#[export] Instance conjugate_s1_left_inverse
  : LeftInverse sgop_s1 conj North
  := fun x => ap (fun z => sgop_s1 z x) (susp_neg_stable Empty x)
      @ @hspace_susp_neg (Sphere 0) hspace_s1 iscoherent_s1 x
      @ (merid (North : Sphere 0))^.

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
