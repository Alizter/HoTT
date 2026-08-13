Require Import Basics.Overture Basics.Tactics Basics.Equivalences.
Require Import Types.Unit.
Require Import WildCat.Core WildCat.PointedCat.
Require Import Pointed.Core Pointed.Loops Pointed.pMap Pointed.pEquiv.
Require Import Spectra.Spectrum.

Local Open Scope pointed_scope.

(** * The zero spectrum *)

(** The constant prespectrum on the pointed unit type. *)
CoFixpoint isprespectrum_punit : IsPreSpectrum pUnit.
Proof.
  snapply Build_IsPreSpectrum.
  - exact pUnit.
  - exact pequiv_loops_punit^-1*.
  - napply isprespectrum_punit.
Defined.

Global Existing Instance isprespectrum_punit.

(** Every structure map of the constant prespectrum is an equivalence. *)
CoFixpoint isspectrum_punit
  : @IsSpectrum pUnit isprespectrum_punit.
Proof.
  snapply Build_IsSpectrum.
  - change (IsEquiv pequiv_loops_punit^-1*).
    exact _.
  - napply isspectrum_punit.
Defined.

Global Existing Instance isspectrum_punit.

Definition sZero : Spectrum := ((pUnit; _); isspectrum_punit).

(** ** Mapping property *)

(** Every map out of the zero spectrum is homotopic to the constant map. *)
CoFixpoint smap_homotopy_pconst_source
  {Y : pType} `{IsPreSpectrum Y}
  (f : @SpectrumMap pUnit Y isprespectrum_punit _)
  : SpectrumMapHomotopy smap_pconst f
      (punit_pmap_pconst f).
Proof.
  snapply Build_IsSForall.
  - exact (punit_pmap_pconst (smap_deloop' f)).
  - exact tt.
  - napply smap_homotopy_pconst_source.
Defined.

(** Every map into the zero spectrum is homotopic to the constant map. *)
CoFixpoint smap_homotopy_pconst_target
  {X : pType} `{IsPreSpectrum X}
  (f : @SpectrumMap X pUnit _ isprespectrum_punit)
  : SpectrumMapHomotopy smap_pconst f
      (phomotopy_pconst_contr f).
Proof.
  snapply Build_IsSForall.
  - exact (phomotopy_pconst_contr
      (smap_deloop' f)).
  - exact tt.
  - napply smap_homotopy_pconst_target.
Defined.

Instance isinitial_szero : IsInitial sZero.
Proof.
  intro X.
  exists smap_pconst.
  intro f.
  change (@SpectrumMap pUnit X
    isprespectrum_punit X.1.2) in f.
  snapply exist.
  - exact (punit_pmap_pconst f).
  - exact (smap_homotopy_pconst_source f).
Defined.

Instance isterminal_szero : IsTerminal sZero.
Proof.
  intro X.
  exists smap_pconst.
  intro f.
  change (@SpectrumMap X pUnit
    X.1.2 isprespectrum_punit) in f.
  snapply exist.
  - exact (phomotopy_pconst_contr f).
  - exact (smap_homotopy_pconst_target f).
Defined.

Instance ispointedcat_spectrum : IsPointedCat Spectrum.
Proof.
  snapply Build_IsPointedCat.
  - exact sZero.
  - exact _.
  - exact _.
Defined.
