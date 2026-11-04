From HoTT Require Import Basics HSpace.Core Pointed.Core Pointed.Loops.
Require Import Pointed.pSusp Homotopy.Suspension.

Local Open Scope mc_mult_scope.
Local Open Scope pointed_scope.
Local Open Scope path_scope.

(** ** Coherent H-space structures *)

(** An H-space is coherent when the left and right identities agree at the base point. *)

Class IsCoherent (X : pType) `{IsHSpace X} :=
  iscoherent : left_identity pt = right_identity pt.

Record IsCohHSpace (A : pType) := {
    ishspace_cohhspace :: IsHSpace A;
    iscoherent_cohhspace :: IsCoherent A;
  }.

Definition issig_iscohhspace (A : pType)
  : { hspace_op : SgOp A
    & { hspace_left_identity : LeftIdentity hspace_op pt
    & { hspace_right_identity : RightIdentity hspace_op pt
    & hspace_left_identity pt = hspace_right_identity pt } } }
      <~> IsCohHSpace A
  := ltac:(make_equiv).

(** A type equivalent to a coherent H-space is a coherent H-space. *)
Definition iscohhspace_equiv_cohhspace {X Y : pType} `{IsCohHSpace Y} (f : X <~>* Y)
  : IsCohHSpace X.
Proof.
  snapply Build_IsCohHSpace.
  - rapply (ishspace_equiv_hspace f).
    apply ishspace_cohhspace; assumption.
  - unfold IsCoherent; cbn.
    refine (_ @@ 1).
    refine (ap (ap f^-1) _).
    pelim f.
    refine (1 @@ _).
    exact iscoherent.
Defined.

(** Every loop space is a coherent H-space. *)
Definition iscohhspace_loops {X : pType} : IsCohHSpace (loops X).
Proof.
  srapply Build_IsCohHSpace.
  - exact ishspace_loops.
  - reflexivity.
Defined.

(** In a coherent H-space on a suspension, multiplying the pole-exchanged reflection of a point by that point gives [South]. *)
Definition hspace_susp_neg {A : Type} `{hs : IsHSpace (psusp A)}
  `{coh : !IsCoherent (psusp A)} (x : Susp A)
  : @hspace_op _ hs (susp_neg A x) x = South.
Proof.
  pose (mu := @hspace_op _ hs).
  change (mu (susp_neg A x) x = South).
  revert x; snapply Susp_ind_FlFr.
  - exact (@hspace_right_identity _ hs South).
  - exact (@hspace_left_identity _ hs South).
  - intro a.
    rhs napply (1 @@ ap_const (merid a) South).
    rhs napply concat_p1.
    lhs_V napply (ap011_diag (fun x y => mu (susp_neg A x) y) (merid a) @@ 1).
    lhs napply (ap011_compose' mu (susp_neg A) idmap
      (merid a) (merid a) @@ 1).
    lhs napply (ap022 mu (Susp_rec_beta_merid a)
      (ap_idmap (merid a)) @@ 1).
    change (ap011 mu (merid a)^ (merid a)
      @ @hspace_left_identity _ hs South = @hspace_right_identity _ hs South).
    generalize (merid a).
    generalize (South : Susp A).
    intros y p; destruct p.
    lhs napply concat_1p.
    exact iscoherent.
Defined.
