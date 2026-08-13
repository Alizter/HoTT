Require Import Basics.Overture Basics.Tactics.
Require Import Types.Universe.
Require Import WildCat.Core.
Require Import Algebra.AbGroups.AbelianGroup.
Require Import Pointed.Core Pointed.Loops.
Require Import Homotopy.EMSpace.
Require Import Spectra.Spectrum.

Local Open Scope pointed_scope.

(** * Eilenberg-Mac Lane spectra *)

Section EilenbergMacLaneSpectrum.
  Context `{Univalence}.

  (** The level-[n] space of the Eilenberg-Mac Lane spectrum of [G] is [K(G,n)]. *)
  Definition eilenberg_maclane_spectrum (G : AbGroup) : Spectrum
    := spectrum_from_sequence
      (fun n => K(G, n)) (pequiv_loops_em_em G).

  Local Instance isprespectrum_eilenberg_maclane
    (G : AbGroup) (n : nat)
    : IsPreSpectrum K(G, n)
    := isprespectrum_from_sequence
      (fun n => K(G, n))
      (fun n => (pequiv_loops_em_em G n
        : K(G, n) ->* loops K(G, S n))) n.

  CoFixpoint issmap_eilenberg_maclane
    {G G' : AbGroup} (f : G $-> G') (n : nat)
    : IsSpectrumMap (fmap (K' n) f).
  Proof.
    snapply Build_IsSForall.
    - exact (fmap (K' (S n)) f).
    - exact (em_fmap_loops_natural f n)^*.
    - change (IsSpectrumMap (fmap (K' (S n)) f)).
      napply issmap_eilenberg_maclane.
  Defined.

  (** A group homomorphism induces a map of Eilenberg-Mac Lane spectra. *)
  Definition smap_eilenberg_maclane
    {G G' : AbGroup} (f : G $-> G')
    : eilenberg_maclane_spectrum G
      $-> eilenberg_maclane_spectrum G'.
  Proof.
    snapply exist.
    - exact (fmap (K' O) f).
    - napply issmap_eilenberg_maclane.
  Defined.

  Instance is0functor_eilenberg_maclane_spectrum
    : Is0Functor eilenberg_maclane_spectrum.
  Proof.
    snapply Build_Is0Functor.
    intros G G' f.
    exact (smap_eilenberg_maclane f).
  Defined.
End EilenbergMacLaneSpectrum.
