Require Import Basics.Overture Basics.Tactics Basics.Equivalences.
Require Import Pointed.Core Pointed.Loops Pointed.pEquiv.
Require Import Spectra.Spectrum.

Local Open Scope pointed_scope.

(** * Products of spectra *)

(** The product of two prespectra is formed levelwise. *)
CoFixpoint isprespectrum_product
  (X Y : pType) `{IsPreSpectrum X} `{IsPreSpectrum Y}
  : IsPreSpectrum (X * Y).
Proof.
  snapply Build_IsPreSpectrum.
  - exact (deloop X * deloop Y).
  - exact ((loops_prod (deloop X) (deloop Y))^-1*
      o* functor_pprod (glue X) (glue Y)).
  - napply isprespectrum_product; exact _.
Defined.

Global Existing Instance isprespectrum_product.

Definition psProduct (X Y : PreSpectrum) : PreSpectrum
  := (X * Y; isprespectrum_product X Y).

(** Levelwise products of spectra are spectra. *)
CoFixpoint isspectrum_product
  (X Y : pType)
  `{psX : IsPreSpectrum X} `{psY : IsPreSpectrum Y}
  `{sX : @IsSpectrum X psX} `{sY : @IsSpectrum Y psY}
  : @IsSpectrum (X * Y) (isprespectrum_product X Y).
Proof.
  snapply Build_IsSpectrum.
  - change (IsEquiv
      ((loops_prod (deloop X) (deloop Y))^-1*
        o* functor_pprod (glue X) (glue Y))).
    napply isequiv_compose.
    + change (IsEquiv (equiv_functor_pprod
        (equiv_glue X) (equiv_glue Y))).
      exact _.
    + exact _.
  - change (@IsSpectrum (deloop X * deloop Y)
      (isprespectrum_product (deloop X) (deloop Y))).
    napply isspectrum_product; exact _.
Defined.

Global Existing Instance isspectrum_product.

Definition sProduct (X Y : Spectrum) : Spectrum
  := ((X * Y; isprespectrum_product X Y);
      isspectrum_product X Y).
