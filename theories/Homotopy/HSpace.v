Require Import Basics.
Require Import abstract_algebra.
Require Import Types.
Require Import HIT.Truncations.
Require Import HIT.Connectedness.
Import TrM.

(* In this file we define HSpaces and other algebraic structures with identities up to homotopy, and prove some properties about their mapping spaces. *)

(* Here is a convienient notation for talking about the base point *)
Local Notation pt := (point _).

Local Open Scope trunc_scope.

Section HSpace.

  Global Instance mon_unit_ptype (A : pType) : MonUnit A := pt.

  (* A HSpace on A consists of an operation Aop, and proofs that the point is a left and right identity. This can be thought of as an untruncated Magma. *)
  Class HSpace (A : pType) `{SgOp A} := {
    hs_left_id :> LeftIdentity (&) pt;
    hs_right_id :> RightIdentity (&) pt;
  }.

  Context
   `{Univalence}
    {A : pType}
   `{HSpace A}
   `{IsConnected 0 A}.

  (* Left and right multiplications are equivalences for 0-connected HSpaces *)

  Lemma mu_l_equiv : forall (a : A), IsEquiv (a &).
  Proof.
    refine (conn_map_elim -1 (unit_name pt) _ _).
    + exact (conn_point_incl pt).
    + apply Unit_ind.
      serapply (isequiv_homotopic idmap).
      exact (fun a => (hs_left_id a)^).
  Defined.

  Lemma mu_r_equiv : forall (a : A), IsEquiv (& a).
  Proof.
    refine (conn_map_elim -1 (unit_name pt) _ _).
    + exact (conn_point_incl pt).
    + apply Unit_ind.
      serapply (isequiv_homotopic idmap).
      exact (fun a => (hs_right_id a)^).
  Defined.

  Definition mu_l_equiv' (a : A) : A <~> A
    := BuildEquiv _ _ _ (mu_l_equiv a).

  Definition mu_r_equiv' (a : A) : A <~> A
    := BuildEquiv _ _ _ (mu_r_equiv a).

End HSpace.

Class Coherent (X : pType) `{HSpace X} := {
    hspace_coh : hs_left_id pt = hs_right_id pt;
}.

(* A Coherent HSpace is a hspace where the left and right identity are equal. No such analogue exists for Magmas since this is a trivial consequence of being 0-truncated. *)
Class Coherent_HSpace (X : pType) `{SgOp X} := {
  chs_hs :> HSpace X;
  hspace_is_coh :> Coherent X;
}.

(* A HMonoid is an associative HSpace *)
Class HMonoid (A : pType) `{SgOp A} := {
  hm_hs :> HSpace A;
  hm_ass :> Associative (&);
}.

(* A HGroup is a HMonoid with left and right invereses *)
Class HGroup (A : pType) `{SgOp A} `{Negate A} := {
  hg_hm :> HMonoid A;
  hg_left_inv :> LeftInverse (&) (-) pt;
  hg_right_inv :> RightInverse (&) (-) pt;
}.

(* A HAbGroup is an abelian HGroup *)
Class HAbGroup (A : pType) `{SgOp A} `{Negate A} := {
  ha_hg :> HGroup A;
  ha_comm :> Commutative (&);
}.

(* Truncated H-structures are just the regular structures *)
Section HTrunc.

  Context `{Funext}.

  Global Instance monunit_tr `{MonUnit X} : MonUnit (Tr 0 X).
  Proof.
    apply tr, mon_unit.
  Defined.

  Global Instance sgop_tr `{SgOp X} : SgOp (Tr 0 X).
  Proof.
    serapply Trunc_rec; intro x.
    serapply Trunc_rec; intro y.
    exact (tr (x & y)).
  Defined.

  Global Instance sgop_tr_assoc `{op : SgOp X} `{Associative _ op}
    : Associative (sgop_tr).
  Proof.
    serapply Trunc_ind; intro x; cbn.
    serapply Trunc_ind; intro y; cbn.
    serapply Trunc_ind; intro z; cbn.
    apply ap, associativity.
  Defined.

  Global Instance sgop_tr_comm `{op : SgOp X} `{Commutative _ _ op}
    : Commutative (sgop_tr).
  Proof.
    serapply Trunc_ind; intro x; cbn.
    serapply Trunc_ind; intro y; cbn.
    apply ap, commutativity.
  Defined.

  Global Instance negate_tr `{Negate X} : Negate (Tr 0 X).
  Proof.
    serapply Trunc_rec; intro x; cbn.
    apply tr, negate, x.
  Defined.

  Global Instance hm_sg `{HMonoid X} : SemiGroup (Tr 0 X).
  Proof.
    serapply (Build_SemiGroup (Tr 0 X)).
  Defined.

  Global Instance hm_mon `{HMonoid X} : Monoid (Tr 0 X).
  Proof.
    serapply (Build_Monoid (Tr 0 X)).
    all: serapply Trunc_ind; intro; cbn.
    all: apply ap.
    1: apply left_identity.
    apply right_identity.
  Defined.

  Global Instance hg_grp `{HGroup X} : Group (Tr 0 X).
  Proof.
    serapply (Build_Group (Tr 0 X)).
    all: serapply Trunc_ind; intro; cbn.
    all: unfold mon_unit.
    all: apply ap.
    1: apply left_inverse.
    apply right_inverse.
  Defined.

  Global Instance hg_abgrp `{HAbGroup X} : AbGroup (Tr 0 X).
  Proof.
    serapply (Build_AbGroup (Tr 0 X)).
  Defined.

End HTrunc.

Require Import Pointed.Core.
Require Import Pointed.pMap.
Require Import Pointed.pHomotopy.

Local Open Scope pointed_scope.

Notation "X ->* Y" := (Build_pType (X ->* Y) _).

Section HMappingSpace.

  Context `{Funext}.

  Global Instance sgop_pmap {X Y : pType} `{HSpace Y}
    : SgOp (X ->* Y).
  Proof.
    intros f g.
    serapply Build_pMap.
    { intro x.
      exact (f x & g x). }
    cbn.
    destruct (point_eq g)^.
    destruct (point_eq f)^.
    apply right_identity.
  Defined.

  Global Instance foo `{HSpace Y} {coh : Coherent Y} : HSpace (X ->* Y).
  Proof.
    intro X.
    serapply Build_HSpace.
    { cbn.
      intro f.
      apply path_pmap.
      unfold sg_op, sgop_pmap.
      serapply Build_pHomotopy.
      1: intro; simpl; apply left_identity.
      cbn.
      rewrite <- (inv_V (point_eq f)).
      destruct (point_eq f)^.
      simpl; rewrite concat_p1.
      apply hspace_coh. }
    intro f.
    apply path_pmap.
    unfold sg_op, sgop_pmap.
    serapply Build_pHomotopy.
    1: intro; simpl; apply right_identity.
    pointed_reduce.
    pointed_reduce.
    reflexivity.
  Defined.

  Global Instance foo_neg `{HGroup Y} : Negate (X ->* Y).
  Proof.
    intros X f.
    serapply Build_pMap.
    { intro x.
      apply negate, f, x. }
    cbn.
    refine ((right_identity _)^ @ _ @ point_eq f).
    destruct (point_eq f)^.
    apply left_inverse.
  Defined.

  Global Instance bar `{HGroup Y} {coh : Coherent Y}
    : HGroup (X ->* Y).
  Proof.
    intro X.
    serapply Build_HGroup.
    { serapply Build_HMonoid.
      intros f g h.
      apply path_pmap.
      serapply Build_pHomotopy.
      1: intro; cbn; apply associativity.
      destruct f as [f fe], g as [g ge], h as [h he].
      simpl.
      rewrite <- he^.
      rewrite <- ge^.
      rewrite <- fe^.
      unfold right_identity.
      admit. }
    { intro.
      apply path_pmap.
      serapply Build_pHomotopy.
      1: intro; cbv; apply left_inverse.
      cbv beta.
      hott_simpl.
      unfold left_inverse.
      unfold sg_op.
      unfold sgop_pmap.
      unfold point_eq.
      simpl.
      destruct x as [x xe].
      simpl.
      rewrite <- (inv_V xe).
      destruct xe^.
      cbn.
      hott_simpl.
      destruct (left_inverse pt).
      
      admit. }
    { intro.
      apply path_pmap.
      serapply Build_pHomotopy.
      1: intro; cbv; apply right_inverse.
      cbv beta.
      hott_simpl.
      admit. }
  Admitted.


