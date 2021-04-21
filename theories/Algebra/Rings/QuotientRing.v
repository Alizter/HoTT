Require Import Basics Types WildCat.
Require Import Algebra.Congruence.
Require Import Algebra.AbGroups.
Require Import Algebra.Rings.CRing.
Require Import Algebra.Rings.Ideal.

Import Ideal.Notation.
Local Open Scope ring_scope.

(** In this file we define the quotient of a commutative ring by an ideal *)

Section QuotientRing.

  Context (R : CRing) (I : Ideal R).

  Instance plus_quotient_group : Plus (QuotientAbGroup R I) := group_sgop.

  Instance iscong_mult_incosetL
    : @IsCongruence R cring_mult (in_cosetL I).
  Proof.
    snrapply Build_IsCongruence.
    intros x x' y y' p q.
    change (I ( - (x * y) + (x' * y'))).
    change (I (-x + x')) in p.
    change (I (-y + y')) in q.
    rewrite <- (left_identity (op:=(+)) (x' * y') : 0 + (x' * y') = x' * y').
    rewrite <- (right_inverse (op:=(+)) (x' * y) : (x' * y) - (x' * y) = 0).
    rewrite 2 simple_associativity.
    rewrite negate_mult_distr_l.
    rewrite <- simple_distribute_r.
    rewrite <- simple_associativity.
    rewrite negate_mult_distr_r.
    rewrite <- simple_distribute_l.
    rapply subgroup_op.
    1: rewrite (commutativity _ y).
    all: by rapply isideal.
  Defined.

  Instance mult_quotient_group : Mult (QuotientAbGroup R I).
  Proof.
    intro x.
    srapply Quotient_rec.
    { intro y; revert x.
      srapply Quotient_rec.
      { intro x.
        apply class_of.
        exact (x * y). }
      intros x x' p.
      apply qglue.
      by rapply iscong. }
    intros y y' q.
    revert x.
    srapply Quotient_ind_hprop.
    intro x.
    simpl.
    apply qglue.
    by rapply iscong.
  Defined.

  Instance zero_quotient_abgroup : Zero (QuotientAbGroup R I) := class_of _ zero.
  Instance one_quotient_abgroup : One (QuotientAbGroup R I) := class_of _ one.

  Instance isring_quotient_abgroup : IsRing (QuotientAbGroup R I).
  Proof.
    split.
    1: exact _.
    1: repeat split.
    1: exact _.
    (** Associativity follows from the underlying operation *)
    { intros x y.
      snrapply Quotient_ind_hprop; [exact _ | intro z; revert y].
      snrapply Quotient_ind_hprop; [exact _ | intro y; revert x].
      snrapply Quotient_ind_hprop; [exact _ | intro x ].
      unfold sg_op, mult_is_sg_op, mult_quotient_group; simpl.
      apply ap.
      apply associativity. }
    (* Left and right identity follow from the underlying structure *)
    1,2: snrapply Quotient_ind_hprop; [exact _ | intro x].
    1-2: unfold sg_op, mult_is_sg_op, mult_quotient_group; simpl.
    1-2: apply ap.
    1: apply left_identity.
    1: apply right_identity.
    (** Commutativity also follows *)
    { intros x.
      snrapply Quotient_ind_hprop; [exact _ | intro y; revert x].
      snrapply Quotient_ind_hprop; [exact _ | intro x].
      unfold sg_op, mult_is_sg_op, mult_quotient_group; simpl.
      apply ap.
      apply commutativity. }
    (** Finally distributivity also follows *)
    { intros x y.
      snrapply Quotient_ind_hprop; [exact _ | intro z; revert y].
      snrapply Quotient_ind_hprop; [exact _ | intro y; revert x].
      snrapply Quotient_ind_hprop; [exact _ | intro x ].
      unfold sg_op, mult_is_sg_op, mult_quotient_group,
        plus, mult, plus_quotient_group; simpl.
      apply ap.
      apply simple_distribute_l. }
  Defined.

  Definition QuotientRing : CRing 
    := Build_CRing (QuotientAbGroup R I) _ _ _ _ _ _.

End QuotientRing.

Infix "/" := QuotientRing : ring_scope.

(** Quotient map *)
Definition rng_quotient_map {R : CRing} (I : Ideal R)
  : CRingHomomorphism R (R / I).
Proof.
  snrapply Build_CRingHomomorphism'.
  1: rapply grp_quotient_map.
  repeat split.
Defined.

Global Instance issurj_rng_quotient_map {R : CRing} (I : Ideal R)
  : IsSurjection (rng_quotient_map I).
Proof.
  exact _.
Defined.

(** First isomorphism theorem for commutative rings *)
Definition rng_first_iso `{Funext} {A B : CRing} (f : A $-> B)
  : A / ideal_kernel f ≅ rng_image f.
Proof.
  snrapply Build_CRingIsomorphism''.
  { etransitivity.
    2: exact (grp_first_iso f).
    apply grp_iso_quotient_normal. }
  split.
  { intros x.
    srapply Quotient_ind_hprop; intro y; revert x.
    srapply Quotient_ind_hprop; intro x.
    srapply path_sigma_hprop.
    exact (rng_homo_mult _ _ _). }
  srapply path_sigma_hprop.
  exact (rng_homo_one _).
Defined.

(** Invariance of equal ideals *)
Lemma rng_quotient_invar {R : CRing} {I J : Ideal R} (p : (I ↔ J)%ideal)
  : R / I ≅ R / J.
Proof.
  snrapply Build_CRingIsomorphism'.
  { srapply equiv_quotient_functor'.
    1: exact equiv_idmap.
    intros x y; cbn.
    apply p. }
  repeat split.
  1,2: intros x; simpl.
  1,2: srapply Quotient_ind_hprop.
  1,2: intros y; revert x.
  1,2: srapply Quotient_ind_hprop.
  1,2: intros x; rapply qglue.
  1: change (J ( - (x + y) + (x + y))).
  2: change (J (- ( x * y) + (x * y))).
  1,2: rewrite rng_plus_negate_l.
  1,2: apply ideal_in_zero.
Defined.

(** We phrase the first ring isomorphism theroem in a slightly differnt way so that it is easier to use. This form specifically asks for a surjective map *)
Definition rng_first_iso' `{Funext} {A B : CRing} (f : A $-> B)
  (issurj_f : IsSurjection f)
  (I : Ideal A) (p : (I ↔ ideal_kernel f)%ideal)
  : A / I ≅ B.
Proof.
  etransitivity.
  1: apply (rng_quotient_invar p).
  etransitivity.
  2: rapply (rng_image_issurj f).
  apply rng_first_iso.
Defined.

(** Chinese remainder theorem *)
Theorem chinese_remainder `{Univalence} {R : CRing} (I J : Ideal R) (c : Coprime I J)
  : R / (I ∩ J)%ideal ≅ (R / I) × (R / J).
Proof.
  (** We use the first isomorphism theorem *)
  srapply rng_first_iso'.
  { (** This is the corecursion of the two quotient maps *)
    apply cring_product_corec.
    1,2: apply rng_quotient_map. }
  { (** This map is surjective iff I and J are coprime *)
    hnf in c.
    pose (p := c cring_one).
    destruct p as [_ p].
    specialize (p tt).
    strip_truncations.
    destruct p.
    
    all: admit. }
  (** Finally we must show the ideal of this map is the intersection. *)
  apply ideal_subset_antisymm.
  - intros r [i j].
    apply path_prod; apply qglue.
    1: change (I (- r + 0)).
    2: change (J (- r + 0)).
    1,2: rewrite rng_plus_comm.
    1,2: apply ideal_in_plus_negate.
    1,3: apply ideal_in_zero.
    1,2: assumption.
  - intros i p.
    apply equiv_path_prod in p.
    destruct p as [p q].
    apply ideal_in_negate'.
    rewrite <- rng_plus_zero_r.
    split.
    1: exact (related_quotient_paths _ _ _ p).
    1: exact (related_quotient_paths _ _ _ q).
Admitted.

Theorem chinese_remainder_prod `{Univalence} {R : CRing} (I J : Ideal R) (c : Coprime I J)
  : R / (I ⋅ J)%ideal ≅ (R / I) × (R / J).
Proof.
  etransitivity.
  { rapply rng_quotient_invar.
    symmetry.
    rapply ideal_intersection_is_product. }
  rapply chinese_remainder.
Defined.
