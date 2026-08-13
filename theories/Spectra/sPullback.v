Require Import Basics.Overture Basics.Tactics Basics.Equivalences.
Require Import WildCat.Core.
Require Import Pointed.Core Pointed.pEquiv Pointed.pPullback.
Require Import Spectra.Spectrum.

Local Open Scope pointed_scope.

(** * Pullbacks of spectra *)

(** Pointed pullbacks applied levelwise preserve prespectra. *)
CoFixpoint isprespectrum_ppullback {X Y Z : pType}
  `{IsPreSpectrum X, IsPreSpectrum Y, IsPreSpectrum Z}
  (f : SpectrumMap X Z) (g : SpectrumMap Y Z)
  : IsPreSpectrum (pPullback f g).
Proof.
  snapply Build_IsPreSpectrum.
  - exact (pPullback (smap_deloop' f)
      (smap_deloop' g)).
  - exact ((loops_ppullback (smap_deloop' f)
        (smap_deloop' g))^-1*
      o* functor_ppullback (glue Z) (glue X) (glue Y)
        (smap_square f)^*
        (smap_square g)^*).
  - napply isprespectrum_ppullback.
Defined.

Global Existing Instance isprespectrum_ppullback.

(** Levelwise pullbacks of maps of spectra are spectra. *)
CoFixpoint isspectrum_ppullback {X Y Z : pType}
  `{IsPreSpectrum X, IsPreSpectrum Y,IsPreSpectrum Z,
    !IsSpectrum X, !IsSpectrum Y, !IsSpectrum Z}
  (f : SpectrumMap X Z) (g : SpectrumMap Y Z)
  : @IsSpectrum (pPullback f g) (isprespectrum_ppullback f g).
Proof.
  snapply Build_IsSpectrum.
  - change (IsEquiv
      ((loops_ppullback (smap_deloop' f)
          (smap_deloop' g))^-1*
        o* functor_ppullback (glue Z) (glue X) (glue Y)
          (smap_square f)^*
          (smap_square g)^*)).
    napply isequiv_compose.
    + change (IsEquiv (pequiv_ppullback
        (equiv_glue Z) (equiv_glue X) (equiv_glue Y)
        (smap_square f)^*
        (smap_square g)^*)).
      exact _.
    + exact _.
  - change (@IsSpectrum
      (pPullback (smap_deloop' f)
        (smap_deloop' g))
      (isprespectrum_ppullback (smap_deloop' f)
        (smap_deloop' g))).
    napply isspectrum_ppullback; exact _.
Defined.

Global Existing Instance isspectrum_ppullback.

(** The pullback spectrum of two maps with a common codomain. *)
Definition sPullback {X Y Z : Spectrum} (f : X $-> Z) (g : Y $-> Z)
  : Spectrum.
Proof.
  change (@SpectrumMap X Z X.1.2 Z.1.2) in f.
  change (@SpectrumMap Y Z Y.1.2 Z.1.2) in g.
  snapply exist.
  - snapply exist.
    + exact (pPullback f g).
    + napply isprespectrum_ppullback.
  - napply isspectrum_ppullback; exact _.
Defined.
