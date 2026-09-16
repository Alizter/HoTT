From HoTT Require Import Basics.
Require Import Types.Paths Types.Universe.
Require Import Pointed.Core Spaces.Spheres.
Require Import Homotopy.HSpaceS3 Homotopy.CayleyDickson.
Require Import Homotopy.Join.Core.
Require Import Homotopy.HSpaceS7.LeftScalar.
Require Import Homotopy.HSpaceS7.Direct.Normalization.
Require Import Homotopy.HSpaceS7.Direct.Comparison.
Require Import Homotopy.HSpaceS7.Direct.RightRightMiddle.

Local Set Universe Minimization ToSet.
Local Open Scope pointed_scope.
Local Open Scope path_scope.

(** * The right-right eta comparison with its prescribed constructor computations *)
Module S7DirectRightRight.
Include S7DirectComparison.
Section Comparison.
  Universe u.
  Context `{Univalence}.
  Local Notation C := (Sphere 1).
  Local Notation J := (Join@{Set Set Set} C C).
  Local Notation mu := (@cd_op@{Set} (psphere 1)
    S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative cd_diamond_susp).
  Local Notation rr := (@cd_assoc_rr@{Set} (psphere 1)
    S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative cd_diamond_susp
    S7LeftScalar.circle_commutative).
  Local Notation middle_r := (S7RightRightMiddle.middle_r@{u}).

  (** Transport the actual last-left overlap through the last-input glue, then use the computed right column of the middle associator. *)
  Let comparison (c d t : C) (x : J)
    : eta_associator@{u} c d x (joinr t) = rr t d x
    := (last_associator_transport_normal_form@{u} x (joinr t) c d)^
      @ ((ap (transport
          (fun z => mu (mu x (joinr t)) z = mu x (mu (joinr t) z))
          (jglue c d)) (S7RightRightMiddle.overlap@{u} t x c)
        @ apD (middle_r t x) (jglue c d))
        @ S7RightRightMiddle.middle_r_joinr@{u} t d x).

  Let comparison_joinl (c d t a : C)
    : comparison c d t (joinl a) = eta_overlap_l@{u} a c d (joinr t).
  Proof.
    exact (ap (fun q =>
      (last_associator_transport_normal_form@{u} (joinl a) (joinr t) c d)^ @ q)
      (concat_p1 _)).
  Defined.

  Let comparison_joinr (c d t b : C)
    : comparison c d t (joinr b) = eta_overlap_r@{u} b c d (joinr t).
  Proof.
    exact (ap (fun q =>
      (last_associator_transport_normal_form@{u} (joinr b) (joinr t) c d)^ @ q)
      (concat_p1 _)).
  Defined.

  (** Use the prescribed endpoint proofs themselves, rather than merely proofs with the same endpoints. The glue comes from naturality of the complete comparison above. *)
  Definition eta_associator_rr (c d t : C) (x : J)
    : eta_associator@{u} c d x (joinr t) = rr t d x.
  Proof.
    revert x; snapply Join_ind.
    - exact (fun a => eta_overlap_l@{u} a c d (joinr t)).
    - exact (fun b => eta_overlap_r@{u} b c d (joinr t)).
    - intros a b.
      exact ((ap (transport _ (jglue a b)) (comparison_joinl c d t a)^
        @ apD (comparison c d t) (jglue a b)) @ comparison_joinr c d t b).
  Defined.

  Definition eta_associator_rr_beta_joinl (c d t a : C)
    : eta_associator_rr c d t (joinl a)
      = eta_overlap_l@{u} a c d (joinr t)
    := idpath.

  Definition eta_associator_rr_beta_joinr (c d t b : C)
    : eta_associator_rr c d t (joinr b)
      = eta_overlap_r@{u} b c d (joinr t)
    := idpath.
End Comparison.
End S7DirectRightRight.
