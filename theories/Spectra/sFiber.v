Require Import Basics.Overture Basics.Tactics Basics.Equivalences.
Require Import WildCat.Core.
Require Import Pointed.Core Pointed.Loops Pointed.pFiber.
Require Import Spectra.Spectrum.

Local Open Scope pointed_scope.

(** * Fibers of spectra *)

(** Pointed fibers applied levelwise preserve prespectra.  The structure map is the fiber map induced by the map square, followed by the comparison between the fiber of a looped map and the loops of its fiber. *)
CoFixpoint isprespectrum_pfiber
  {X Y : pType} `{IsPreSpectrum X} `{IsPreSpectrum Y}
  (f : SpectrumMap X Y)
  : IsPreSpectrum (pfiber f).
Proof.
  snapply Build_IsPreSpectrum.
  - exact (pfiber (smap_deloop' f)).
  - exact (pfiber_fmap_loops (smap_deloop' f)
      o* functor_pfiber (smap_square f)).
  - napply isprespectrum_pfiber.
Defined.

Global Existing Instance isprespectrum_pfiber.

(** When the source and target are spectra, the induced fiber map is an equivalence because both vertical maps in the defining square are equivalences. *)
CoFixpoint isspectrum_pfiber
  {X Y : pType}
  `{psX : IsPreSpectrum X} `{psY : IsPreSpectrum Y}
  `{sX : @IsSpectrum X psX} `{sY : @IsSpectrum Y psY}
  (f : SpectrumMap X Y)
  : @IsSpectrum (pfiber f) (isprespectrum_pfiber f).
Proof.
  snapply Build_IsSpectrum.
  - change (IsEquiv
      (pfiber_fmap_loops (smap_deloop' f)
        o* functor_pfiber (smap_square f))).
    napply isequiv_compose.
    + change (IsEquiv (pequiv_pfiber
        (equiv_glue X) (equiv_glue Y)
        (smap_square f))).
      exact _.
    + exact _.
  - change (@IsSpectrum (pfiber (smap_deloop' f))
      (isprespectrum_pfiber (smap_deloop' f))).
    napply isspectrum_pfiber; exact _.
Defined.

Global Existing Instance isspectrum_pfiber.

(** The fiber spectrum of a map of spectra. *)
Definition sFiber {X Y : Spectrum} (f : X $-> Y) : Spectrum.
Proof.
  change (@SpectrumMap X Y X.1.2 Y.1.2) in f.
  snapply exist.
  - snapply exist.
    + exact (pfiber f).
    + napply isprespectrum_pfiber.
  - napply isspectrum_pfiber; exact _.
Defined.
