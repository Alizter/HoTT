From HoTT Require Import Basics Types.Universe Types.Paths.
From HoTT Require Import Classes.interfaces.abstract_algebra.
From HoTT Require Import Pointed.Core Spaces.Spheres Truncations.Connectedness.
From HoTT Require Import Homotopy.CayleyDickson Homotopy.Join.Core.
From HoTT Require Import Homotopy.HSpace.Core Homotopy.HSpaceS1 Homotopy.HSpaceS3.
From HoTT Require Import Homotopy.HSpaceS7.LeftScalar Homotopy.Suspension.
From HoTT_Tests Require Import Homotopy.S7OverlapScratch.

Local Set Universe Minimization ToSet.
Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.
Set Default Timeout 30.

Section Circle.
  Context `{Univalence}.
  Let circle_imaginaroid : CayleyDicksonImaginaroid (Sphere 0) := cdi_s0.
  Let circle_associative : Associative sgop_s1 := associative_sgop_s1.
  Let circle_commutative : Commutative sgop_s1 := commutative_sgop_s1.
  Local Existing Instances circle_imaginaroid circle_associative circle_commutative.
  Let circle_distropp : DistrOpp sgop_s1 conj := cds_conjug_distr.
  Local Existing Instance circle_distropp.
  Let circle_connected := (_ : IsConnected (0%trunc) (psphere 1)).
  Let circle_truncated := (_ : IsTrunc 1 (psphere 1)).
  Local Existing Instances circle_connected circle_truncated.
  Context (D0 : CayleyDicksonDiamond (psphere 1) (-)).
  Local Existing Instance D0.
  Local Notation C := (Sphere 1).
  Local Notation J := (Join@{Set Set Set} C C).
  Local Notation assoc := (simple_associativity (f:=sgop_s1)).
  Local Notation comm := (commutativity (f:=sgop_s1)).
  Local Opaque cd_diamond cd_op_diamond.
  Let AL := cd_assoc_last_joinl@{Set} (X:=psphere 1).
  Let qll := cd_assoc_last_joinl_first_ll@{Set} (X:=psphere 1).
  Let qlr := cd_assoc_last_joinl_first_lr@{Set} (X:=psphere 1).

  Definition overlap_scalar_l (s a c : C)
    : (cd_diamond_translate_l_neg_unit (X:=psphere 1) s a c)^ = (assoc s a c)^.
  Proof.
    revert s a c.
    do 3 srapply (conn_point_elim (-1) (A:=psphere 1)).
    reflexivity.
  Defined.

  Definition overlap_scalar_r (s b c : C)
    : (comm c (conj s * b)
        @ (cd_diamond_translate_r_parameter (X:=psphere 1) s North North b c)^)
        @ ap (conj s *.) (comm c b)^
      = assoc c (conj s) b
        @ (ap (.* b) (comm c (conj s)) @ (assoc (conj s) c b)^).
  Proof.
    revert s b c.
    do 3 srapply (conn_point_elim (-1) (A:=psphere 1)).
    reflexivity.
  Defined.

  Definition overlap_glue (s a b c : C)
    : concat_Ap (fun y => AL (joinl s) y c) (jglue a b) @ (qll s a c @@ 1)
      = (1 @@ qlr s b c) @ S7LeftScalar.first_l_glue_l D0 s a b c.
  Proof.
    lhs tapply (Joverlap (North : C) (North : C)
      (sgop_s1 s) (fun x => sgop_s1 x c) (sgop_s1 (conj s))
      (sgop_s1 c) (fun x => sgop_s1 x c)
      (comm c) (fun a => cd_diamond_translate_l_neg_unit (X:=psphere 1) s a c)
      (fun b => cd_diamond_translate_r_parameter (X:=psphere 1) s North North b c)
      (fun a => (assoc s a c)^)
      (fun b => assoc c (conj s) b
        @ (ap (.* b) (comm c (conj s)) @ (assoc (conj s) c b)^))
      (fun a => overlap_scalar_l s a c) (fun b => overlap_scalar_r s b c) a b).
    napply whiskerL.
    exact (Join_ind_FlFr_beta_jglue _ _ _ _ _ a b).
  Defined.
End Circle.
