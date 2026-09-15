From HoTT Require Import Basics.
Require Import Classes.interfaces.abstract_algebra.
Require Import Pointed.Core.
Require Import Homotopy.HSpace.Core Homotopy.CayleyDickson.

Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.

(** * Scalar rotation for the right-right diamond comparison *)
Module S7RightRightScalars.
Local Opaque cds_factorneg_l.
Section Scalars.
  Context {X : pType} `{CayleyDicksonSpheroid X}.

  (** Conjugation reverses the four factors of the parameter. *)
  Definition conjugate_parameter (a b c d : X)
    : conj (cd_diamond_parameter a b c d)
      = b * (conj d * (a * c)).
  Proof.
    unfold cd_diamond_parameter.
    lhs rapply distropp.
    lhs rapply (ap011 (.*.) (cds_conjug_inv b)
      (distropp (conj c * conj a) d)).
    napply (ap (fun z => b * (conj d * z))).
    exact (distropp (conj c) (conj a)
      @ ap011 (.*.) (cds_conjug_inv a) (cds_conjug_inv c)).
  Defined.

  Context `{!Associative (@hspace_op X _)}
    `{!Commutative (@hspace_op X _)}.
  Local Notation assoc := (simple_associativity (f:=hspace_op)).
  Local Notation comm := (commutativity (f:=hspace_op)).

  (** The parameters of the two right-right eta contributions are reciprocal, rather than equal. *)
  Definition parameter (t a b c d : X)
    : cd_diamond_parameter a b ((-d) * conj t) (t * c)
      = conj (cd_diamond_parameter ((-t) * conj b)
        (conj a * t) c d).
  Proof.
    rhs napply conjugate_parameter.
    unfold cd_diamond_parameter.
    lhs rapply (ap (fun z => z * conj a * (t * c) * conj b)
      (distropp (-d) (conj t)
        @ ap011 (.*.) (cds_conjug_inv t) (swapop d))).
    lhs rapply (ap (fun z => z * conj a * (t * c) * conj b)
      (factorneg_r t (conj d))).
    lhs rapply (ap (fun z => z * (t * c) * conj b)
      (factorneg_l (t * conj d) (conj a))).
    lhs rapply (ap (.* conj b)
      (factorneg_l (t * conj d * conj a) (t * c))).
    lhs rapply factorneg_l.
    rhs rapply (ap (fun z => (conj a * t) * (conj d * (z * c)))
      (factorneg_l t (conj b))).
    rhs rapply (ap (fun z => (conj a * t) * (conj d * z))
      (factorneg_l (t * conj b) c)).
    rhs rapply (ap ((conj a * t) *.)
      (factorneg_r (conj d) ((t * conj b) * c))).
    rhs rapply factorneg_r.
    napply (ap (-)).
    lhs rapply (ap (fun z => z * (t * c) * conj b)
      (comm (t * conj d) (conj a) @ assoc (conj a) t (conj d))).
    lhs rapply (assoc ((conj a * t) * conj d) (t * c) (conj b))^.
    lhs rapply (assoc (conj a * t) (conj d) ((t * c) * conj b))^.
    napply (ap (fun z => (conj a * t) * (conj d * z))).
    exact ((assoc t c (conj b))^
      @ ap (t *.) (comm c (conj b)) @ assoc t (conj b) c).
  Defined.

  Local Definition map_l_linear (a c x y : X)
    : cd_diamond_map_l a c (x * y)
      = cd_diamond_map_l a c x * y.
  Proof.
    unfold cd_diamond_map_l.
    lhs rapply (ap (fun z => a * (c * z)) (factorneg_l x y)^).
    lhs rapply (ap (a *.) (assoc c (-x) y)).
    exact (assoc a (c * -x) y).
  Defined.

  Local Definition map_r_linear (b c x y : X)
    : cd_diamond_map_r b c (x * y)
      = cd_diamond_map_r b c x * y.
  Proof.
    unfold cd_diamond_map_r.
    lhs rapply (ap (c *.) (assoc x y b)^).
    lhs rapply (ap (fun z => c * (x * z)) (comm y b)).
    lhs rapply (ap (c *.) (assoc x b y)).
    exact (assoc c (x * b) y).
  Defined.

  Definition map_l (t a b c d : X)
    : (fun z => cd_diamond_map_l ((-t) * conj b) c
        ((-cd_diamond_parameter ((-t) * conj b)
          (conj a * t) c d) * z))
      == cd_diamond_map_l a ((-d) * conj t).
  Proof.
    intro z.
    pose (u := cd_diamond_parameter ((-t) * conj b)
      (conj a * t) c d).
    lhs rapply (ap (cd_diamond_map_l ((-t) * conj b) c)
      (factorneg_l u z @ (factorneg_r u z)^)).
    lhs napply map_l_linear.
    lhs rapply (ap (.* -z) (cd_diamond_map_l_parameter
      ((-t) * conj b) (conj a * t) c d)).
    unfold cd_diamond_map_l.
    rhs rapply (assoc a ((-d) * conj t) (-z)).
    napply (ap (.* -z)).
    lhs rapply (ap ((-d) *.) (distropp (conj a) t)).
    lhs rapply (ap (fun x => (-d) * (conj t * x))
      (cds_conjug_inv a)).
    exact (assoc (-d) (conj t) a @ comm ((-d) * conj t) a).
  Defined.

  Definition map_r (t a b c d : X)
    : (fun z => cd_diamond_map_r (conj a * t) c
        (cd_diamond_parameter ((-t) * conj b)
          (conj a * t) c d * z))
      == cd_diamond_map_r b ((-d) * conj t).
  Proof.
    intro z.
    lhs napply map_r_linear.
    lhs rapply (ap (.* z) (cd_diamond_map_r_parameter
      ((-t) * conj b) (conj a * t) c d)).
    lhs rapply (ap (.* z) (cd_assoc_rr_scalar_r t d b)).
    unfold cd_diamond_map_r.
    exact ((assoc ((-d) * conj t) b z)^
      @ ap (((-d) * conj t) *.) (comm b z)).
  Defined.
End Scalars.
End S7RightRightScalars.
