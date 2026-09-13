From HoTT Require Import Basics.
Require Import Types.Paths Types.Prod.
Require Import Classes.interfaces.abstract_algebra.
Require Import Pointed.Core Pointed.pSusp.
Require Import Homotopy.HSpace.Core.
Require Import Homotopy.CayleyDickson Homotopy.Suspension Homotopy.Join.Core.
Require Import Homotopy.Join.SuspDiamond Homotopy.HSpaceS7.LeftScalar.

Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.

(** * First-right scalar actions and the actual turned diamond *)
Module S7RightScalar.
Local Opaque cds_factorneg_l.
Section Scalars.
  Context {X : pType} `{CayleyDicksonSpheroid X}
    `{!Associative (@hspace_op X _)}
    `{!Commutative (@hspace_op X _)}.
  Local Notation assoc := (simple_associativity (f:=hspace_op)).
  Local Notation comm := (commutativity (f:=hspace_op)).

  Definition parameter_swap (a b c d : X)
    : cd_diamond_parameter (-b) a c d = -cd_diamond_parameter a b c d.
  Proof.
    unfold cd_diamond_parameter.
    lhs rapply (ap (fun x => conj c * x * d * conj a) (swapop b)).
    lhs rapply (ap (fun x => x * d * conj a) (factorneg_r (conj c) (conj b))).
    lhs rapply (ap (.* conj a) (factorneg_l (conj c * conj b) d)).
    lhs rapply (factorneg_l (conj c * conj b * d) (conj a)).
    napply (ap (-)).
    lhs rapply (ap (.* conj a) (assoc (conj c) (conj b) d)^).
    lhs rapply (assoc (conj c) (conj b * d) (conj a))^.
    lhs rapply (ap (conj c *.) (comm (conj b * d) (conj a))).
    lhs rapply (ap (fun x => conj c * (conj a * x)) (comm (conj b) d)).
    lhs rapply (ap (conj c *.) (assoc (conj a) d (conj b))).
    lhs rapply (assoc (conj c) (conj a * d) (conj b)).
    exact (ap (.* conj b) (assoc (conj c) (conj a) d)).
  Defined.

  (** Left multiplication by a right-copy scalar exchanges the two labels. Its diamond parameter is the negation of the old parameter. *)
  Definition parameter (s a b c d : X)
    : cd_diamond_parameter ((-b) * conj s) (a * s) c d
      = -cd_diamond_parameter a b c d.
  Proof.
    lhs rapply (ap011 (fun x y => cd_diamond_parameter x y c d)
      (comm (-b) (conj s))
      (comm a s @ ap (.* a) (cds_conjug_inv s)^)).
    exact (S7LeftScalar.left_parameter (conj s) (-b) a c d
      @ parameter_swap a b c d).
  Defined.

  (** These compare the two maps after the actual turn, not just their endpoint values. *)
  Definition map_l (s a c : X)
    : (fun t => cd_diamond_map_l a c t * s)
      == (fun t => cd_diamond_map_r (a * s) c (-t)).
  Proof.
    intro t; unfold cd_diamond_map_l, cd_diamond_map_r.
    lhs rapply (ap (.* s) (comm a (c * -t))).
    lhs rapply (assoc (c * -t) a s)^.
    exact (assoc c (-t) (a * s))^.
  Defined.

  Definition map_r (s b c : X)
    : (fun t => (-cd_diamond_map_r b c t) * conj s)
      == (fun t => cd_diamond_map_l ((-b) * conj s) c (-t)).
  Proof.
    intro t; unfold cd_diamond_map_l, cd_diamond_map_r.
    rhs rapply (ap (fun x => ((-b) * conj s) * (c * x)) (cds_negate_inv t)).
    rhs rapply (assoc (-b) (conj s) (c * t))^.
    rhs rapply (ap ((-b) *.) (comm (conj s) (c * t))).
    rhs rapply (assoc (-b) (c * t) (conj s)).
    napply (ap (.* conj s)).
    rhs rapply (comm (-b) (c * t)).
    rhs rapply (factorneg_r (c * t) b).
    exact (ap (-) (assoc c t b)).
  Defined.
End Scalars.

Section Suspension.
  Universe u.
  Context {A : Type@{u}} `{CayleyDicksonImaginaroid A}
    `{!Associative (@hspace_op (psusp A) _)}
    `{!Commutative (@hspace_op (psusp A) _)}.
  Local Existing Instances negate_susp conjugate_susp cdi_susp_hspace.
  Local Notation X := (psusp A).
  (** Fix the scalar operation and the universe choices of the derived spheroid. The same boundary witnesses are used throughout the comparison. *)
  Local Instance scalar_op : SgOp X := @hspace_op X (@cdi_susp_hspace A H).
  Local Notation conj := (conjugate_susp A cdi_negate).
  Local Notation cds_susp_cdi :=
    (@cds_susp_cdi@{u u u u u u u u u u u u u u u u u u u u u} A).
  Local Notation cd_diamond_map_l := (cd_diamond_map_l (H:=cds_susp_cdi _)).
  Local Notation cd_diamond_map_r := (cd_diamond_map_r (H:=cds_susp_cdi _)).
  Local Notation cd_diamond_parameter := (cd_diamond_parameter (H:=cds_susp_cdi _)).
  Local Notation cd_diamond_map_l_neg_unit := (cd_diamond_map_l_neg_unit (H:=cds_susp_cdi _)).
  Local Notation cd_diamond_map_l_parameter := (cd_diamond_map_l_parameter (H:=cds_susp_cdi _)).
  Local Notation cd_diamond_map_r_unit := (cd_diamond_map_r_unit (H:=cds_susp_cdi _)).
  Local Notation cd_diamond_map_r_parameter := (cd_diamond_map_r_parameter (H:=cds_susp_cdi _)).
  Local Notation cd_op_diamond := (cd_op_diamond (H:=cds_susp_cdi _)).
  Local Notation cd_op_diamond_V := (cd_op_diamond_V (H:=cds_susp_cdi _)).
  Local Notation parameter := (parameter (H:=cds_susp_cdi _)).
  Local Notation map_l := (map_l (H:=cds_susp_cdi _)).
  Local Notation map_r := (map_r (H:=cds_susp_cdi _)).

  Definition e00 (s a c : X)
    : (a * c) * s = c * (a * s)
    := (ap (.* s) (cd_diamond_map_l_neg_unit a c))^
      @ map_l s a c South @ cd_diamond_map_r_unit (a * s) c.
  Definition e01 (s a b c d : X)
    : (-(conj a * d)) * conj s = (-d) * conj (a * s)
    := (ap (fun t => (-t) * conj s) (cd_diamond_map_r_parameter a b c d))^
      @ map_r s b c (cd_diamond_parameter a b c d)
      @ (ap (cd_diamond_map_l ((-b) * conj s) c) (parameter s a b c d)^
        @ cd_diamond_map_l_parameter ((-b) * conj s) (a * s) c d).
  Definition e10 (s b c : X)
    : (-(c * b)) * conj s = ((-b) * conj s) * c
    := (ap (fun t => (-t) * conj s) (cd_diamond_map_r_unit b c))^
      @ map_r s b c North @ cd_diamond_map_l_neg_unit ((-b) * conj s) c.
  Definition e11 (s a b c d : X)
    : ((-d) * conj b) * s = conj ((-b) * conj s) * d
    := (ap (.* s) (cd_diamond_map_l_parameter a b c d))^
      @ map_l s a c (cd_diamond_parameter a b c d)
      @ (ap (cd_diamond_map_r (a * s) c) (parameter s a b c d)^
        @ cd_diamond_map_r_parameter ((-b) * conj s) (a * s) c d).

  (** This compares the actual multiplication fillers. The right-copy left action turns the inverse of the old filler, and its four boundary comparisons run from the translated vertices to the new multiplication vertices. These paths have not yet been compared with the original associator's scalar witnesses. *)
  Definition diamond (s a b c d : X)
    : transport011
        (fun x : X * X => fun y : X * X =>
          zigzag (fst x) (snd x) (fst y) = zigzag (fst x) (snd x) (snd y))
        (path_prod' (e10 s b c) (e01 s a b c d))
        (path_prod' (e00 s a c) (e11 s a b c d))
        (join_diamond_turn (.* s) (fun t => (-t) * conj s)
          (cd_op_diamond a b c d)^)
      = (cd_op_diamond ((-b) * conj s) (a * s) c d)^.
  Proof.
    lhs napply (ap (transport011
      (fun x : X * X => fun y : X * X =>
        zigzag (fst x) (snd x) (fst y) = zigzag (fst x) (snd x) (snd y))
      (path_prod' (e10 s b c) (e01 s a b c d))
      (path_prod' (e00 s a c) (e11 s a b c d)))
      (ap (join_diamond_turn (.* s) (fun t => (-t) * conj s))
        (cd_op_diamond_V a b c d))).
    rhs napply (cd_op_diamond_V ((-b) * conj s) (a * s) c d).
    unfold e00, e01, e10, e11.
    lhs napply (join_diamond_turn_compare
      (cd_diamond_map_l a c) (cd_diamond_map_r b c)
      (.* s) (fun t => (-t) * conj s) (-) (-)
      (cd_diamond_map_l ((-b) * conj s) c) (cd_diamond_map_r (a * s) c)
      (map_l s a c) (map_r s b c) _ _ _ _ _ _ _ _
      (cd_diamond_susp (cd_diamond_parameter a b c d))
      (cd_diamond_susp (-cd_diamond_parameter a b c d))
      (diamond_susp_turn (-) (cd_diamond_parameter a b c d))).
    (** The reindexing argument has a free parameter path and free endpoint witnesses; it does not eliminate a fixed diamond. *)
    assert (R : forall (t t' : X) (p : t = t')
      (q : cd_diamond_map_l ((-b) * conj s) c t' = (-d) * conj (a * s))
      (r : cd_diamond_map_r (a * s) c t' = conj ((-b) * conj s) * d),
      join_zigzag_filler (cd_diamond_map_l ((-b) * conj s) c)
        (cd_diamond_map_r (a * s) c)
        (cd_diamond_map_l_neg_unit ((-b) * conj s) c)
        (ap (cd_diamond_map_l ((-b) * conj s) c) p @ q)
        (cd_diamond_map_r_unit (a * s) c)
        (ap (cd_diamond_map_r (a * s) c) p @ r) (cd_diamond_susp t)
      = join_zigzag_filler (cd_diamond_map_l ((-b) * conj s) c)
        (cd_diamond_map_r (a * s) c)
        (cd_diamond_map_l_neg_unit ((-b) * conj s) c) q
        (cd_diamond_map_r_unit (a * s) c) r (cd_diamond_susp t')).
    { intros t t' p q r; destruct p.
      exact (ap011 (fun q r => join_zigzag_filler
        (cd_diamond_map_l ((-b) * conj s) c) (cd_diamond_map_r (a * s) c)
        (cd_diamond_map_l_neg_unit ((-b) * conj s) c) q
        (cd_diamond_map_r_unit (a * s) c) r (cd_diamond_susp t))
        (concat_1p q) (concat_1p r)). }
    exact (R _ _ (parameter s a b c d)^ _ _).
  Defined.
End Suspension.

End S7RightScalar.
