From HoTT Require Import Basics.
Require Import Types.Universe.
Require Import Classes.interfaces.abstract_algebra.
Require Import Pointed.Core Pointed.pEquiv.
Require Import Spaces.Spheres.
Require Import Homotopy.HSpace.Core Homotopy.HSpaceS1 Homotopy.HSpaceS3.
Require Import Homotopy.CayleyDickson.
Require Import Homotopy.Join.Core Homotopy.Join.JoinSusp.

Local Set Universe Minimization ToSet.

Local Open Scope pointed_scope.
Local Open Scope path_scope.

(** * The remaining input for the 7-sphere H-space *)

(** Work in join coordinates for the second doubling. Only the final H-space structure is transferred to a suspension sphere. *)
Definition pequiv_iterated_join_s1_s7
  : pjoin (pjoin (psphere 1) (Sphere 1)) (Join (Sphere 1) (Sphere 1))
      <~>* psphere 7.
Proof.
  refine (pequiv_pjoin_sphere 3 3 o*E _).
  snapply Build_pEquiv'.
  - exact (equiv_functor_join (pequiv_pjoin_sphere 1 1)
      (pequiv_pjoin_sphere 1 1)).
  - reflexivity.
Defined.

(** The diagonal circle-action approach starts with [cd_diamond_parameter_translate] and [cd_op_diamond_normalize]. The latter compares the actual mixed filler with postcomposition of the unit-normalized filler, retaining both sets of boundary witnesses. The multiplication-level equivariance, its point and glue computations, and the final compatibility of partial associators still need to be constructed; filler normalization alone does not establish associativity. *)

(** The four scalar-corner lemmas [cd_associativity_rectangle_ll], [cd_associativity_rectangle_lr], [cd_associativity_rectangle_rl], and [cd_associativity_rectangle_rr] supply the point cases of double join induction, using [commutative_sgop_s1]. Extending these particular fillers still requires glue coherences. For example, the first glue case would be:
<<
  transport (cd_associativity_rectangle a b (joinl c)) (jglue d e)
    (cd_associativity_rectangle_ll a b c d)
  = cd_associativity_rectangle_lr a b c e
>>
This compares the chosen fillers, not merely their endpoints. No extension of these scalar-normalized choices across the glues is asserted. *)

(** Proof skeleton with its remaining obligation exposed as an argument, not an axiom. The required family is the rectangle comparison for the chosen circle double, with both later arguments arbitrary join elements. No inhabitant of this family is supplied here. *)
Definition hspace_s7_from_rectangle `{Univalence}
  (h : forall (a b : Sphere 1) (u v : Join (Sphere 1) (Sphere 1)),
    cd_associativity_rectangle (X:=psphere 1) a b u v)
  : IsHSpace (psphere 7).
Proof.
  (** 1. The rectangle family gives associativity of the first double. *)
  pose proof (cd_assoc_from_rectangle h).
  (** 2. Inverse uniqueness completes its spheroid structure. *)
  pose (spheroid3 := cd_spheroid_of_associative (X:=psphere 1)).
  (** 3. Double again with the directly constructed join diamond. *)
  napply (ishspace_equiv_hspace pequiv_iterated_join_s1_s7^-1*).
  nrefine (@hspace_cd (pjoin (psphere 1) (Sphere 1)) spheroid3 _ _).
  - exact _.
  - exact cd_diamond_double.
Defined.

(** Normalizing in the middle argument gives a different choice of corners. The families [cd_associativity_rectangle_middle_l] and [cd_associativity_rectangle_middle_r] are defined for every [v], so both inner glue coherences are supplied by [apD]. The remaining outer glue compatibility follows if transport around each middle rectangle fixes the specified unit filler. This is a sufficient condition, not a claim that such invariance has been proved. *)
Definition hspace_s7_from_rectangle_invariance `{Univalence}
  (h : forall (a b c d : Sphere 1) (v : Join (Sphere 1) (Sphere 1)),
    transport (fun u => cd_associativity_rectangle (X:=psphere 1) a b u v)
      (join_rectangle_loop (A:=psphere 1) (B:=psphere 1) c d)
      (cd_associativity_rectangle_unit a b v)
    = cd_associativity_rectangle_unit a b v)
  : IsHSpace (psphere 7).
Proof.
  napply hspace_s7_from_rectangle.
  intros a b u v.
  exact (Join_ind_from_rectangle (A:=psphere 1) (B:=psphere 1)
    (fun u => cd_associativity_rectangle a b u v)
    (cd_associativity_rectangle_unit a b v) (fun c d => h a b c d v) u).
Defined.
