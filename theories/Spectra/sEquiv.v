Require Import Basics.Overture Basics.Tactics Basics.Equivalences.
Require Import WildCat.Core WildCat.Equiv WildCat.Square.
Require Import Pointed.Core Pointed.Loops Pointed.pEquiv.
Require Import Spectra.Spectrum.

Local Open Scope pointed_scope.

(** * Equivalences of spectra *)

(** A spectrum equivalence is a map of prespectra that is a pointed equivalence at every level. *)
CoInductive IsSEquiv {X Y : pType}
  `{IsPreSpectrum X} `{IsPreSpectrum Y}
  (f : SpectrumMap X Y) := {
  isequiv_smap :: IsEquiv f ;
  issequiv_deloop : IsSEquiv (smap_deloop' f) ;
}.

Existing Class IsSEquiv.
Global Existing Instance issequiv_deloop.

Definition sEquiv (X Y : pType)
  `{IsPreSpectrum X} `{IsPreSpectrum Y}
  := {f : SpectrumMap X Y & IsSEquiv f}.

Definition sequiv_map {X Y : pType}
  `{IsPreSpectrum X} `{IsPreSpectrum Y}
  (f : sEquiv X Y) : SpectrumMap X Y
  := f.1.

Coercion sequiv_map : sEquiv >-> SpectrumMap.

Instance issequiv_sequiv {X Y : pType}
  `{IsPreSpectrum X} `{IsPreSpectrum Y}
  (f : sEquiv X Y)
  : IsSEquiv f
  := f.2.

Definition sequiv_pequiv {X Y : pType}
  `{IsPreSpectrum X} `{IsPreSpectrum Y}
  (f : sEquiv X Y) : X <~>* Y.
Proof.
  snapply Build_pEquiv.
  - exact f.
  - exact _.
Defined.

Definition sequiv_deloop {X Y : pType}
  `{IsPreSpectrum X} `{IsPreSpectrum Y}
  (f : sEquiv X Y)
  : sEquiv (deloop X) (deloop Y).
Proof.
  snapply exist.
  - exact (smap_deloop' f).
  - exact (issequiv_deloop f f.2).
Defined.

(** Levelwise loops preserve levelwise equivalences. *)
CoFixpoint issequiv_smap_loops
  {X Y : pType} `{IsPreSpectrum X} `{IsPreSpectrum Y}
  (f : sEquiv X Y)
  : IsSEquiv (smap_loops f).
Proof.
  snapply Build_IsSEquiv.
  - change (IsEquiv (fmap loops f)).
    exact (equiv_isequiv
      (pequiv_fmap_loops (sequiv_pequiv f))).
  - exact (@issequiv_smap_loops
      (deloop X) (deloop Y) _ _ (sequiv_deloop f)).
Defined.

Definition sequiv_loops
  {X Y : pType} `{IsPreSpectrum X} `{IsPreSpectrum Y}
  (f : sEquiv X Y)
  : sEquiv (loops X) (loops Y).
Proof.
  snapply exist.
  - exact (smap_loops f).
  - napply issequiv_smap_loops.
Defined.

(** The structure map of a spectrum is a levelwise equivalence. *)
CoFixpoint issequiv_smap_glue
  (X : pType) `{psX : IsPreSpectrum X}
  `{sX : @IsSpectrum X psX}
  : IsSEquiv (smap_glue X).
Proof.
  snapply Build_IsSEquiv.
  - change (IsEquiv (glue X)).
    exact _.
  - napply issequiv_smap_glue; exact _.
Defined.

Global Existing Instance issequiv_smap_glue.

Definition sequiv_glue
  (X : pType) `{psX : IsPreSpectrum X}
  `{sX : @IsSpectrum X psX}
  : sEquiv X (loops (deloop X)).
Proof.
  snapply exist.
  - exact (smap_glue X).
  - napply issequiv_smap_glue; exact _.
Defined.

(** The inverse of a levelwise equivalence again commutes with the structure maps. *)
CoFixpoint issmap_sequiv_inverse
  {X Y : pType} `{IsPreSpectrum X} `{IsPreSpectrum Y}
  (f : sEquiv X Y)
  : IsSpectrumMap (sequiv_pequiv f)^-1*.
Proof.
  snapply Build_IsSForall.
  - exact (sequiv_pequiv (sequiv_deloop f))^-1*.
  - change (Square (A := pType) (glue Y) (glue X)
      (sequiv_pequiv f)^-1*
      (fmap loops (sequiv_pequiv (sequiv_deloop f))^-1*)).
    napply vconcatR.
    + rapply hinverse.
      napply vconcatR.
      * rapply smap_square.
      * napply cate_buildequiv_fun.
        exact (iemap loops (sequiv_pequiv (sequiv_deloop f))).
    + exact (emap_inv' loops
        (sequiv_pequiv (sequiv_deloop f)))^$.
  - napply issmap_sequiv_inverse.
Defined.

Definition smap_sequiv_inverse {X Y : pType}
  `{IsPreSpectrum X} `{IsPreSpectrum Y}
  (f : sEquiv X Y) : SpectrumMap Y X.
Proof.
  snapply exist.
  - exact (sequiv_pequiv f)^-1*.
  - napply issmap_sequiv_inverse.
Defined.

CoFixpoint issequiv_smap_sequiv_inverse
  {X Y : pType} `{IsPreSpectrum X} `{IsPreSpectrum Y}
  (f : sEquiv X Y)
  : IsSEquiv (smap_sequiv_inverse f).
Proof.
  snapply Build_IsSEquiv.
  - change (IsEquiv (sequiv_pequiv f)^-1*).
    exact _.
  - change (IsSEquiv
      (smap_sequiv_inverse (sequiv_deloop f))).
    napply issequiv_smap_sequiv_inverse.
Defined.

Definition sequiv_inverse {X Y : pType}
  `{IsPreSpectrum X} `{IsPreSpectrum Y}
  (f : sEquiv X Y) : sEquiv Y X
  := (smap_sequiv_inverse f;
      issequiv_smap_sequiv_inverse f).

CoFixpoint issequiv_smap_id
  (X : pType) `{IsPreSpectrum X}
  : IsSEquiv (smap_id X).
Proof.
  snapply Build_IsSEquiv.
  - exact (isequiv_idmap X).
  - napply issequiv_smap_id.
Defined.

Definition sequiv_id (X : pType) `{IsPreSpectrum X}
  : sEquiv X X
  := (smap_id X; issequiv_smap_id X).

CoFixpoint issequiv_smap_compose
  {X Y Z : pType}
  `{IsPreSpectrum X} `{IsPreSpectrum Y} `{IsPreSpectrum Z}
  (g : sEquiv Y Z) (f : sEquiv X Y)
  : IsSEquiv (smap_compose g f).
Proof.
  snapply Build_IsSEquiv.
  - change (IsEquiv (g o* f)).
    exact _.
  - change (IsSEquiv (smap_compose
      (sequiv_deloop g) (sequiv_deloop f))).
    napply issequiv_smap_compose.
Defined.

Definition sequiv_compose
  {X Y Z : pType}
  `{IsPreSpectrum X} `{IsPreSpectrum Y} `{IsPreSpectrum Z}
  (g : sEquiv Y Z) (f : sEquiv X Y)
  : sEquiv X Z
  := (smap_compose g f;
      issequiv_smap_compose g f).

CoFixpoint issmap_homotopy_sequiv_issect
  {X Y : pType} `{IsPreSpectrum X} `{IsPreSpectrum Y}
  (f : sEquiv X Y)
  : SpectrumMapHomotopy
      (smap_compose (sequiv_inverse f) f)
      (smap_id X)
      (peissect (sequiv_pequiv f)).
Proof.
  snapply Build_IsSForall.
  - exact (peissect (sequiv_pequiv (sequiv_deloop f))).
  - exact tt.
  - napply issmap_homotopy_sequiv_issect.
Defined.

CoFixpoint issmap_homotopy_sequiv_isretr
  {X Y : pType} `{IsPreSpectrum X} `{IsPreSpectrum Y}
  (f : sEquiv X Y)
  : SpectrumMapHomotopy
      (smap_compose f (sequiv_inverse f))
      (smap_id Y)
      (peisretr (sequiv_pequiv f)).
Proof.
  snapply Build_IsSForall.
  - exact (peisretr (sequiv_pequiv (sequiv_deloop f))).
  - exact tt.
  - napply issmap_homotopy_sequiv_isretr.
Defined.

Definition sequiv_issect
  {X Y : pType} `{IsPreSpectrum X} `{IsPreSpectrum Y}
  (f : sEquiv X Y)
  : sHomotopy
      (smap_compose (sequiv_inverse f) f)
      (smap_id X)
  := (peissect (sequiv_pequiv f);
      issmap_homotopy_sequiv_issect f).

Definition sequiv_isretr
  {X Y : pType} `{IsPreSpectrum X} `{IsPreSpectrum Y}
  (f : sEquiv X Y)
  : sHomotopy
      (smap_compose f (sequiv_inverse f))
      (smap_id Y)
  := (peisretr (sequiv_pequiv f);
      issmap_homotopy_sequiv_isretr f).

(** Every levelwise equivalence is a categorical equivalence of prespectra. *)
Instance catie_sequiv_prespectrum
  {X Y : PreSpectrum} (f : X $-> Y)
  `{sf : @IsSEquiv X Y X.2 Y.2 f}
  : CatIsEquiv f.
Proof.
  pose (e := ((f; sf) : sEquiv X Y)).
  napply (catie_adjointify f (smap_sequiv_inverse e)).
  - exact (sequiv_isretr e).
  - exact (sequiv_issect e).
Defined.

(** The induced categorical structure on spectra has the same equivalences. *)
Instance catie_sequiv_spectrum
  {X Y : Spectrum} (f : X $-> Y)
  `{sf : @IsSEquiv X Y X.1.2 Y.1.2 f}
  : CatIsEquiv f
  := catie_sequiv_prespectrum f.
