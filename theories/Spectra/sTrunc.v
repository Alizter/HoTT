Require Import Basics.Overture Basics.Tactics Basics.Equivalences.
Require Import Types.Universe.
Require Import WildCat.Core.
Require Import Pointed.Core Pointed.Loops Pointed.pTrunc.
Require Import Spectra.Spectrum.

Local Open Scope pointed_scope.

(** * Truncation of spectra *)

Local Open Scope trunc_scope.

CoFixpoint isprespectrum_ptr `{Univalence}
  (n : trunc_index) (X : pType) `{IsPreSpectrum X}
  : IsPreSpectrum (pTr n X).
Proof.
  snapply Build_IsPreSpectrum.
  - exact (pTr n.+1 (deloop X)).
  - exact (ptr_loops n (deloop X)
      o* fmap (pTr n) (glue X)).
  - napply isprespectrum_ptr; exact _.
Defined.

Global Existing Instance isprespectrum_ptr.

Definition sTr `{Univalence}
  (n : trunc_index) (E : PreSpectrum) : PreSpectrum
  := (pTr n E; isprespectrum_ptr n E).

CoFixpoint isspectrum_ptr `{Univalence}
  (n : trunc_index) (X : pType)
  `{psX : IsPreSpectrum X} `{sX : @IsSpectrum X psX}
  : @IsSpectrum (pTr n X) (isprespectrum_ptr n X).
Proof.
  snapply Build_IsSpectrum.
  - change (IsEquiv (ptr_loops n (deloop X) o*
      pequiv_ptr_functor n (equiv_glue X))).
    napply isequiv_compose; exact _.
  - napply isspectrum_ptr; exact _.
Defined.

Global Existing Instance isspectrum_ptr.

Definition strunc `{Univalence}
  (n : trunc_index) (E : Spectrum) : Spectrum
  := ((pTr n E; isprespectrum_ptr n E); isspectrum_ptr n E).
