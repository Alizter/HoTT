Require Import Basics Types.
Require Import Truncations.
Require Import HIT.Spheres.
Require Import Colimits.Pushout.
Require Import Limits.Pullback.
Require Import Spaces.Nat.
Require Import TruncType.
Require Import HIT.Flattening.

Local Open Scope nat_scope.

(** ** Connected components of universes *)

(** We use the connected component of a universe in order to define X-bundles where X is a given type. *)

(** The connected component of a universe consists of all types that are merely equal to the given type [X]. *)
Record ConnectedComponent@{i j} (X : Type@{i}) := {
  type_conncomp : Type@{i} ;
  merely_path_type_conncomp : merely (@paths@{j} Type@{i} type_conncomp X) ;
}.

(** We coerce elements of connected components to the underlying universe. *)
Coercion type_conncomp : ConnectedComponent >-> Sortclass.

Definition issig_ConnectedComponent (X : Type)
  : _ <~> ConnectedComponent X := ltac:(issig).




(** An X-bundle over a type [A] can be defined as a type family [F : A -> ConnectedComponent X] *)

(** The pullback of a bundle along the bundle on [1] is the total space of the bundle. *)
Theorem commsq_bundle (X : Type) (A : Type) (B : A -> ConnectedComponent X)
  : (fun _ => Build_ConnectedComponent X X (tr idpath)) o (fun _ => tt) == B o (@pr1 A B).
Proof.
  intros [a b].
  simpl.
  destruct (B a) as [Y p].
  destruct p.
  reflexivity.
Defined.

(** ** Real projective space *)

(** We define the [n]th real projective space and tautological bundle over that space mutually by induction on the natural number [n]. But since the type of the bundle depends on the real projective space this is a "recursive-recursive" definition, which isn't supported in Coq currently. This can be avoided by using the sigma-type trick, or in our case records. We combine this mutual definition into a single recursive one, by recursing into a record type. *)
Record RP_helper (n : nat) := {
  rp_helper_type : Type ;
  rp_helper_cov : rp_helper_type -> ConnectedComponent (Sphere 0) ;
}.

Definition RP_def (n : nat) : RP_helper n.
Proof.
  induction n as [|n IHn].
  { srapply Build_RP_helper.
    1: exact Unit.
    intro.
    srapply Build_ConnectedComponent.
    1: exact (Sphere 0).
    exact (idpath). }
  destruct IHn as [RPn covn].
  srapply Build_RP_helper.
  { exact (Pushout (@pr1 RPn covn) (fun _ => tt)). }
  hnf.
  srapply Pushout_rec.
  1: exact covn.
  { intro.
    srapply Build_ConnectedComponent.
    1: exact (Sphere 0).
    exact (idpath). }
  cbn.
  intros [x u].
  symmetry.
  exact (commsq_bundle (Sphere 0) RPn covn (x; u)).
Defined.

Definition RP (n : nat) := rp_helper_type n (RP_def n).
Definition rp_cov (n : nat) : RP n -> Type := rp_helper_cov n (RP_def n).

Definition rp_base (n : nat) : RP n :=
  match n with
  | 0 => tt
  | n.+1 => pushr tt
  end.

Definition rp_incl (n : nat) : RP n -> RP n.+1.
Proof.
  destruct n.
  1: intro; exact (rp_base _).
  apply pushl.
Defined.

Require Import Homotopy.Join.

Theorem equiv_rp_cov_total_sphere `{Univalence} (n : nat)
  : {x : RP n & rp_cov n x} <~> Sphere n.
Proof.
  induction n.
  1: cbn; apply (equiv_contr_sigma (fun _ => Sphere 0)).
  assert (J : Join (Sphere 0) (Sphere n) <~> Sphere n.+1%nat) by admit.
  refine (J oE _).
  refine (equiv_functor_join equiv_idmap IHn oE _).
  clear J IHn.
  Search sigT Pushout.
  (** By lemma 8.5.3 we have that the LHS is equivalent to the following *)
  assert (
  
  
  
  unfold rp_cov.
  unfold RP_def.
  change ({x : Pushout pr1 (fun _ : {x : rp_helper_type n (RP_def n) & rp_helper_cov n (RP_def n) x} => tt)
    & Pushout_rec (ConnectedComponent (Sphere 0)) (rp_helper_cov n (RP_def n)) (unit_name _)
        (fun a => (commsq_bundle (Sphere 0) (rp_helper_type n (RP_def n)) (rp_helper_cov n (RP_def n)) a)^) x}
    <~> Sphere (n.+1)%nat).
  
change (
  {x : rp_helper_type n.+1
    (nat_rect (fun n0 : nat => RP_helper n0)
       {| rp_helper_type := Unit; rp_helper_cov := unit_name {| type_conncomp := Sphere 0; merely_path_type_conncomp := 1 |} |}
       (fun (n0 : nat) (IHn0 : RP_helper n0) =>
        {|
        rp_helper_type := Pushout pr1 (fun _ : {x : rp_helper_type n0 IHn0 & rp_helper_cov n0 IHn0 x} => tt);
        rp_helper_cov := Pushout_rec (ConnectedComponent (Sphere 0)) (rp_helper_cov n0 IHn0)
                           (unit_name {| type_conncomp := Sphere 0; merely_path_type_conncomp := 1 |})
                           (fun a : {x : rp_helper_type n0 IHn0 & rp_helper_cov n0 IHn0 x} =>
                            (commsq_bundle (Sphere 0) (rp_helper_type n0 IHn0) (rp_helper_cov n0 IHn0) (a.1; a.2))^) |}) n.+1) &
rp_helper_cov n.+1
  (nat_rect (fun n0 : nat => RP_helper n0)
     {| rp_helper_type := Unit; rp_helper_cov := unit_name {| type_conncomp := Sphere 0; merely_path_type_conncomp := 1 |} |}
     (fun (n0 : nat) (IHn0 : RP_helper n0) =>
      {|
      rp_helper_type := Pushout pr1 (fun _ : {x0 : rp_helper_type n0 IHn0 & rp_helper_cov n0 IHn0 x0} => tt);
      rp_helper_cov := Pushout_rec (ConnectedComponent (Sphere 0)) (rp_helper_cov n0 IHn0)
                         (unit_name {| type_conncomp := Sphere 0; merely_path_type_conncomp := 1 |})
                         (fun a : {x0 : rp_helper_type n0 IHn0 & rp_helper_cov n0 IHn0 x0} =>
                          (commsq_bundle (Sphere 0) (rp_helper_type n0 IHn0) (rp_helper_cov n0 IHn0) (a.1; a.2))^) |}) n.+1) x} <~> 
Sphere (n.+1)%nat).
(*   
  unfold rp_helper_cov. *)
  (** Use flattening lemma for pushouts. *)
Admitted.

Require Import Diagrams.Sequence.
Require Import Colimits.Colimit.
Require Import Colimits.Sequential.
Require Import Homotopy.ClassifyingSpace.
Require Import Algebra.Group.
Require Import Algebra.AbelianGroup.

Definition xorb (a b : Bool) : Bool :=
  match a , b with
  | false , false => false
  | false , true => true
  | true , false => true
  | true , true => false
  end.

Definition Zmod2 : AbGroup.
Proof.
  snrapply (Build_AbGroup Bool).
  Search Bool.
  1: exact xorb.
  1: exact false.
  1: exact idmap.
  repeat split.
  1: exact _.
  1: by intros [] [] [].
  1-4: by intros [].
  by intros [] [].
Defined.

(** Infinite real projective space *)
Definition RPoo := Colimit (Build_Sequence RP rp_incl).



(** The infinite real projective space is the delooping of Zmod2 *)
Theorem equiv_rpoo_bz2 : RPoo <~> ClassifyingSpace Zmod2.
Proof.
Admitted.







