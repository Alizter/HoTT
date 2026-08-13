Require Import Basics.Overture Basics.Tactics Basics.Equivalences.
Require Import Pointed.Core Pointed.Loops Pointed.pMap Pointed.pEquiv.
Require Import Spectra.Spectrum.

Local Open Scope pointed_scope.

(** * Pointed dependent products of spectra *)

(** Pointed dependent products applied levelwise preserve prespectra. *)
CoFixpoint isprespectrum_ppforall `{Funext}
  (A : pType) (B : A -> pType)
  `{forall a, IsPreSpectrum (B a)}
  : IsPreSpectrum (ppforall a : A, B a).
Proof.
  snapply Build_IsPreSpectrum.
  - exact (ppforall a : A, deloop (B a)).
  - refine ((equiv_loops_ppforall
        (fun a => deloop (B a)))^-1* o* _).
    napply functor_ppforall.
    exact (fun a => glue (B a)).
  - napply isprespectrum_ppforall; exact _.
Defined.

Global Existing Instance isprespectrum_ppforall.

(** The pointed dependent product of a family of prespectra. *)
Definition psForall `{Funext}
  (A : pType) (B : A -> PreSpectrum) : PreSpectrum
  := (ppforall a : A, B a; isprespectrum_ppforall A (fun a => B a)).

(** Pointed dependent products applied levelwise preserve spectra. *)
CoFixpoint isspectrum_ppforall `{Funext}
  (A : pType) (B : A -> pType)
  `{psB : forall a, IsPreSpectrum (B a)}
  `{forall a, @IsSpectrum (B a) (psB a)}
  : @IsSpectrum (ppforall a : A, B a)
      (isprespectrum_ppforall A B).
Proof.
  snapply Build_IsSpectrum.
  - change (IsEquiv
      ((equiv_loops_ppforall
          (fun a => deloop (B a)))^-1* o*
        functor_ppforall (fun a => glue (B a)))).
    napply isequiv_compose.
    + change (IsEquiv
        (equiv_functor_ppforall (fun a => equiv_glue (B a)))).
      exact _.
    + exact _.
  - napply isspectrum_ppforall; exact _.
Defined.

Global Existing Instance isspectrum_ppforall.

(** The pointed dependent product, or spectrum of pointed sections, of a family of spectra. *)
Definition ssForall `{Funext}
  (A : pType) (B : A -> Spectrum) : Spectrum
  := ((ppforall a : A, B a;
        isprespectrum_ppforall A (fun a => B a));
      isspectrum_ppforall A (fun a => B a)).
