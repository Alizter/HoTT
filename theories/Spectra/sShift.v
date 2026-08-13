Require Import Basics.Overture Basics.Tactics Basics.Equivalences.
Require Import Spaces.Nat.Core.
Require Import WildCat.Core WildCat.Equiv WildCat.NatTrans
  WildCat.PointedCat.
Require Import Pointed.Core Pointed.Loops.
Require Import Spectra.Spectrum Spectra.sEquiv Spectra.sZero.

Local Open Scope pointed_scope.

(** * Shifts of spectra *)

(** ** The shift functor *)

(** Shifting a prespectrum discards its zeroth space. *)
Definition psShift (X : PreSpectrum) : PreSpectrum
  := (deloop X; isprespectrum_deloop X X.2).

(** Shifting a spectrum again gives a spectrum. *)
Definition sShift (X : Spectrum) : Spectrum
  := ((deloop X; isprespectrum_deloop X X.1.2);
      @isspectrum_deloop X X.1.2 X.2).

Instance is0functor_psshift : Is0Functor psShift.
Proof.
  snapply Build_Is0Functor.
  intros X Y f.
  exact (smap_deloop' f).
Defined.

Instance is1functor_psshift : Is1Functor psShift.
Proof.
  snapply Build_Is1Functor.
  - intros X Y f g p.
    snapply exist.
    + exact (smap_homotopy_deloop p.2).
    + exact (smap_homotopy_deloop_is p.2).
  - intros X.
    exact (Id _).
  - intros X Y Z f g.
    exact (Id _).
Defined.

Instance is0functor_sshift : Is0Functor sShift.
Proof.
  snapply Build_Is0Functor.
  intros X Y f.
  exact (smap_deloop' f).
Defined.

Instance is1functor_sshift : Is1Functor sShift.
Proof.
  snapply Build_Is1Functor.
  - intros X Y f g p.
    snapply exist.
    + exact (smap_homotopy_deloop p.2).
    + exact (smap_homotopy_deloop_is p.2).
  - intros X.
    exact (Id _).
  - intros X Y Z f g.
    exact (Id _).
Defined.

(** Iterated shifts are again wild 1-functors. *)
Definition iterated_psShift (n : nat) (X : PreSpectrum)
  : PreSpectrum
  := nat_iter n psShift X.

Instance is0functor_iterated_psshift (n : nat)
  : Is0Functor (iterated_psShift n).
Proof.
  induction n.
  1: exact _.
  napply is0functor_compose; exact _.
Defined.

Instance is1functor_iterated_psshift (n : nat)
  : Is1Functor (iterated_psShift n).
Proof.
  induction n.
  1: exact _.
  napply is1functor_compose; exact _.
Defined.

Definition iterated_sShift (n : nat) (X : Spectrum)
  : Spectrum
  := nat_iter n sShift X.

Instance is0functor_iterated_sshift (n : nat)
  : Is0Functor (iterated_sShift n).
Proof.
  induction n.
  1: exact _.
  napply is0functor_compose; exact _.
Defined.

Instance is1functor_iterated_sshift (n : nat)
  : Is1Functor (iterated_sShift n).
Proof.
  induction n.
  1: exact _.
  napply is1functor_compose; exact _.
Defined.

(** ** The levelwise loops functor *)

Definition psLoops (X : PreSpectrum) : PreSpectrum
  := (loops X; isprespectrum_loops X).

(** Levelwise loops preserve the spectrum condition. *)
CoFixpoint isspectrum_loops
  (X : pType) `{psX : IsPreSpectrum X}
  `{sX : @IsSpectrum X psX}
  : @IsSpectrum (loops X) (isprespectrum_loops X).
Proof.
  snapply Build_IsSpectrum.
  - change (IsEquiv (fmap loops (glue X))).
    exact (equiv_isequiv
      (pequiv_fmap_loops (equiv_glue X))).
  - napply isspectrum_loops; exact _.
Defined.

Global Existing Instance isspectrum_loops.

Definition sLoops (X : Spectrum) : Spectrum
  := ((loops X; isprespectrum_loops X); isspectrum_loops X).

Instance is0functor_psloops : Is0Functor psLoops.
Proof.
  snapply Build_Is0Functor.
  intros X Y f.
  exact (smap_loops f).
Defined.

Instance is1functor_psloops : Is1Functor psLoops.
Proof.
  snapply Build_Is1Functor.
  - intros X Y f g p.
    snapply exist.
    + exact (fmap2 loops p.1).
    + exact (smap_homotopy_loops p.2).
  - intros X.
    snapply exist.
    + exact (fmap_id loops X).
    + exact (smap_homotopy_loops_id X).
  - intros X Y Z f g.
    snapply exist.
    + exact (fmap_comp loops (smap f) (smap g)).
    + exact (smap_homotopy_loops_compose g f).
Defined.

Instance is0functor_sloops : Is0Functor sLoops.
Proof.
  snapply Build_Is0Functor.
  intros X Y f.
  exact (smap_loops f).
Defined.

Instance is1functor_sloops : Is1Functor sLoops.
Proof.
  snapply Build_Is1Functor.
  - intros X Y f g p.
    snapply exist.
    + exact (fmap2 loops p.1).
    + exact (smap_homotopy_loops p.2).
  - intros X.
    snapply exist.
    + exact (fmap_id loops X).
    + exact (smap_homotopy_loops_id X).
  - intros X Y Z f g.
    snapply exist.
    + exact (fmap_comp loops (smap f) (smap g)).
    + exact (smap_homotopy_loops_compose g f).
Defined.

Definition iterated_psLoops (n : nat) (X : PreSpectrum)
  : PreSpectrum
  := nat_iter n psLoops X.

Instance is0functor_iterated_psloops (n : nat)
  : Is0Functor (iterated_psLoops n).
Proof.
  induction n.
  1: exact _.
  napply is0functor_compose; exact _.
Defined.

Instance is1functor_iterated_psloops (n : nat)
  : Is1Functor (iterated_psLoops n).
Proof.
  induction n.
  1: exact _.
  napply is1functor_compose; exact _.
Defined.

Definition iterated_sLoops (n : nat) (X : Spectrum)
  : Spectrum
  := nat_iter n sLoops X.

Instance is0functor_iterated_sloops (n : nat)
  : Is0Functor (iterated_sLoops n).
Proof.
  induction n.
  1: exact _.
  napply is0functor_compose; exact _.
Defined.

Instance is1functor_iterated_sloops (n : nat)
  : Is1Functor (iterated_sLoops n).
Proof.
  induction n.
  1: exact _.
  napply is1functor_compose; exact _.
Defined.

(** ** Shift equivalences *)

(** The structure maps give a natural transformation from the identity to levelwise loops after shifting. *)
Definition nattrans_glue_psloops_psshift
  : NatTrans idmap (psLoops o psShift).
Proof.
  snapply Build_NatTrans.
  - exact (fun X => smap_glue X).
  - snapply Build_Is1Natural.
    intros X Y f.
    snapply exist.
    + exact (smap_square (smap f)).
    + exact (smap_homotopy_glue_natural f).
Defined.

Definition nattrans_glue_sloops_sshift
  : NatTrans idmap (sLoops o sShift).
Proof.
  snapply Build_NatTrans.
  - exact (fun X => smap_glue X).
  - snapply Build_Is1Natural.
    intros X Y f.
    snapply exist.
    + exact (smap_square (smap f)).
    + exact (smap_homotopy_glue_natural f).
Defined.

Definition natequiv_sloops_sshift
  : NatEquiv idmap (sLoops o sShift).
Proof.
  assert (forall X : Spectrum,
      CatIsEquiv (nattrans_glue_sloops_sshift X)).
  { intro X.
    napply catie_sequiv_spectrum.
    exact (@issequiv_smap_glue X X.1.2 X.2). }
  exact (Build_NatEquiv' nattrans_glue_sloops_sshift).
Defined.

(** Shift and levelwise loops commute definitionally on objects and maps.  Their composite functor instances need not agree definitionally, so the other natural transformation is stated separately. *)
Definition nattrans_glue_psshift_psloops
  : NatTrans idmap (psShift o psLoops).
Proof.
  snapply Build_NatTrans.
  - exact (fun X => smap_glue X).
  - snapply Build_Is1Natural.
    intros X Y f.
    snapply exist.
    + exact (smap_square (smap f)).
    + exact (smap_homotopy_glue_natural f).
Defined.

Definition nattrans_glue_sshift_sloops
  : NatTrans idmap (sShift o sLoops).
Proof.
  snapply Build_NatTrans.
  - exact (fun X => smap_glue X).
  - snapply Build_Is1Natural.
    intros X Y f.
    snapply exist.
    + exact (smap_square (smap f)).
    + exact (smap_homotopy_glue_natural f).
Defined.

Definition natequiv_sshift_sloops
  : NatEquiv idmap (sShift o sLoops).
Proof.
  assert (forall X : Spectrum,
      CatIsEquiv (nattrans_glue_sshift_sloops X)).
  { intro X.
    napply catie_sequiv_spectrum.
    exact (@issequiv_smap_glue X X.1.2 X.2). }
  exact (Build_NatEquiv' nattrans_glue_sshift_sloops).
Defined.

(** Shift and levelwise loops preserve the zero spectrum. *)
Instance ispointedfunctor_sshift : IsPointedFunctor sShift.
Proof.
  snapply Build_IsPointedFunctor'.
  1-4: exact _.
  change (sZero $<~> sZero).
  reflexivity.
Defined.

Instance ispointedfunctor_sloops : IsPointedFunctor sLoops.
Proof.
  snapply Build_IsPointedFunctor'.
  1-4: exact _.
  exact (natequiv_sloops_sshift sZero)^-1$.
Defined.
