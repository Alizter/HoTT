Require Import Basics.Overture Basics.Tactics.
Require Import WildCat.Core WildCat.Universe.
Require Import Pointed.Core Pointed.Loops Pointed.pSusp.
Require Import Spectra.Spectrum.

Local Open Scope pointed_scope.

(** * Suspension prespectra *)

(** The iterated suspensions of a pointed type form a prespectrum.  Constructing its associated suspension spectrum will require spectrification. *)
CoFixpoint isprespectrum_suspension (X : pType)
  : IsPreSpectrum X.
Proof.
  snapply Build_IsPreSpectrum.
  - exact (psusp X).
  - exact (loop_susp_unit X).
  - napply isprespectrum_suspension.
Defined.

Definition suspension_prespectrum (X : pType) : PreSpectrum
  := (X; isprespectrum_suspension X).

CoFixpoint issmap_suspension
  {X Y : pType} (f : X ->* Y)
  : @IsSpectrumMap X Y
      (isprespectrum_suspension X)
      (isprespectrum_suspension Y) f.
Proof.
  snapply Build_IsSForall.
  - exact (fmap psusp f).
  - exact (loop_susp_unit_natural f).
  - napply issmap_suspension.
Defined.

Definition smap_suspension
  {X Y : pType} (f : X ->* Y)
  : suspension_prespectrum X $-> suspension_prespectrum Y.
Proof.
  snapply exist.
  - exact f.
  - napply issmap_suspension.
Defined.

Instance is0functor_suspension_prespectrum
  : Is0Functor suspension_prespectrum.
Proof.
  snapply Build_Is0Functor.
  intros X Y f.
  exact (smap_suspension f).
Defined.
