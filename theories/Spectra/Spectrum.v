Require Import Basics.Overture Basics.Tactics Basics.Equivalences.
Require Import Types.Sigma.
Require Import WildCat.Core WildCat.Displayed WildCat.Equiv WildCat.Induced
  WildCat.Square.
Require Import Pointed.Core Pointed.Loops Pointed.pMap.

Local Open Scope pointed_scope.

(** * Spectra as coalgebras *)

(** ** Prespectra *)

CoInductive IsPreSpectrum (X : pType) := {
  deloop : pType ;
  glue : X ->* loops deloop ;
  isprespectrum_deloop : IsPreSpectrum deloop ;
}.

Arguments deloop X {_}.
Arguments glue X {_}.

Existing Class IsPreSpectrum.
Global Existing Instance isprespectrum_deloop.

(** A family over a prespectrum has a pointed family at each level and a relation expressing compatibility between a section and its delooping. *)
CoInductive IsSFam {X : pType} `{IsPreSpectrum X}
  (P : pFam X) := {
  sfam_deloop_pfam : pFam (deloop X) ;
  sfam_deloop_is : IsSFam sfam_deloop_pfam ;
  sfam_glue_is
    : forall (f : pForall X P)
        (g : pForall (deloop X) sfam_deloop_pfam),
        Type ;
}.

Definition sFam (X : pType) `{IsPreSpectrum X}
  := {P : pFam X & IsSFam P}.

Definition sfam_pfam {X : pType} `{IsPreSpectrum X}
  (P : sFam X) : pFam X
  := P.1.

Definition sfam_deloop {X : pType} `{IsPreSpectrum X}
  (P : sFam X) : sFam (deloop X)
  := (@sfam_deloop_pfam X _ P.1 P.2;
      @sfam_deloop_is X _ P.1 P.2).

Definition sfam_glue {X : pType} `{IsPreSpectrum X}
  (P : sFam X)
  (f : pForall X (sfam_pfam P))
  (g : pForall (deloop X) (sfam_pfam (sfam_deloop P)))
  : Type
  := @sfam_glue_is X _ P.1 P.2 f g.

(** A section of a spectrum family consists of a pointed section at each level satisfying the specified compatibility relation. *)
CoInductive IsSForall {X : pType} `{IsPreSpectrum X}
  (P : sFam X) (f : pForall X (sfam_pfam P)) := {
  sforall_deloop
    : pForall (deloop X) (sfam_pfam (sfam_deloop P)) ;
  sforall_glue : sfam_glue P f sforall_deloop ;
  issforall_deloop
    : IsSForall (sfam_deloop P) sforall_deloop ;
}.

Existing Class IsSForall.

Arguments sforall_deloop {X _ P f} _.
Arguments sforall_glue {X _ P f} _.
Arguments issforall_deloop {X _ P f} _.

Definition sForall {X : pType} `{IsPreSpectrum X} (P : sFam X)
  := {f : pForall X (sfam_pfam P) & IsSForall P f}.

Definition sforall_fun {X : pType} `{IsPreSpectrum X}
  {P : sFam X} (f : sForall P)
  : pForall X (sfam_pfam P)
  := f.1.

Coercion sforall_fun : sForall >-> pForall.

Instance issforall_sforall {X : pType} `{IsPreSpectrum X}
  {P : sFam X} (f : sForall P)
  : IsSForall P f
  := f.2.

Definition sforall_deloop' {X : pType} `{IsPreSpectrum X}
  {P : sFam X} (f : sForall P)
  : sForall (sfam_deloop P).
Proof.
  snapply exist.
  - exact (sforall_deloop f.2).
  - exact (issforall_deloop f.2).
Defined.

(** The type of prespectra is the total type of [IsPreSpectrum]. *)
Definition PreSpectrum := {X : pType & IsPreSpectrum X}.
Definition prespectrum_type (X : PreSpectrum) : pType := X.1.
Coercion prespectrum_type : PreSpectrum >-> pType.

Instance isprespectrum_prespectrum (X : PreSpectrum)
  : IsPreSpectrum X
  := X.2.

(** ** Spectra *)

(** A spectrum structure on a fixed prespectrum asserts recursively that each of its structure maps is an equivalence. *)
CoInductive IsSpectrum (X : pType) `{IsPreSpectrum X} := {
  isequiv_glue :: IsEquiv (glue X) ;
  isspectrum_deloop : IsSpectrum (deloop X) ;
}.

Existing Class IsSpectrum.
Global Existing Instance isspectrum_deloop.

(** The type of spectra is the total type of [IsSpectrum] over [PreSpectrum]. *)
Definition Spectrum := {X : PreSpectrum & IsSpectrum X}.

Definition loops_oo (X : Spectrum) : pType
  := X.1.1.

Coercion loops_oo : Spectrum >-> pType.

Instance isspectrum_loops_oo (X : Spectrum)
  : IsSpectrum X
  := X.2.

Definition equiv_glue (X : pType) `{psX : IsPreSpectrum X}
  `{sX : @IsSpectrum X psX}
  : X <~>* loops (deloop X).
Proof.
  snapply Build_pEquiv.
  - exact (glue X).
  - exact _.
Defined.

(** ** Construction from natural-number-indexed data *)

(** A sequence of pointed types and structure maps determines a prespectrum. *)
CoFixpoint isprespectrum_from_sequence
  (X : nat -> pType)
  (g : forall n, X n ->* loops (X (S n)))
  (n : nat)
  : IsPreSpectrum (X n).
Proof.
  snapply Build_IsPreSpectrum.
  - exact (X (S n)).
  - exact (g n).
  - napply isprespectrum_from_sequence.
    exact g.
Defined.

Definition prespectrum_from_sequence
  (X : nat -> pType)
  (g : forall n, X n ->* loops (X (S n)))
  : PreSpectrum
  := (X O; isprespectrum_from_sequence X g O).

(** If every structure map is a pointed equivalence, the resulting prespectrum is a spectrum. *)
CoFixpoint isspectrum_from_sequence
  (X : nat -> pType)
  (g : forall n, X n <~>* loops (X (S n)))
  (n : nat)
  : @IsSpectrum (X n)
      (isprespectrum_from_sequence X (fun n => g n) n).
Proof.
  snapply Build_IsSpectrum.
  - change (IsEquiv (g n)).
    exact _.
  - change (@IsSpectrum (X (S n))
      (isprespectrum_from_sequence X (fun n => g n) (S n))).
    napply isspectrum_from_sequence.
Defined.

Definition spectrum_from_sequence
  (X : nat -> pType)
  (g : forall n, X n <~>* loops (X (S n)))
  : Spectrum
  := ((X O; isprespectrum_from_sequence X (fun n => g n) O);
      isspectrum_from_sequence X g O).

(** ** Map from spectra to prespectra *)

Definition prespectrum_spectrum : Spectrum -> PreSpectrum := pr1.

(** ** Maps of spectra *)

(** This notion only uses prespectrum structures, and hence applies to spectra as well: the maps commute with the structure maps up to pointed homotopy at every delooping. *)

CoFixpoint issfam_const {X Y : pType}
  `{IsPreSpectrum X} `{IsPreSpectrum Y}
  : IsSFam (@pfam_const X Y).
Proof.
  snapply Build_IsSFam.
  - exact (@pfam_const (deloop X) (deloop Y)).
  - exact (@issfam_const (deloop X) (deloop Y) _ _).
  - intros f g.
    exact (Square (A := pType) (glue X) (glue Y) f
      (fmap loops g)).
Defined.

Definition sfam_const {X Y : pType}
  `{IsPreSpectrum X} `{IsPreSpectrum Y}
  : sFam X
  := (@pfam_const X Y; issfam_const).

Definition IsSpectrumMap {X Y : pType}
  `{IsPreSpectrum X} `{IsPreSpectrum Y} (f : X ->* Y)
  := IsSForall (@sfam_const X Y _ _) f.

Existing Class IsSpectrumMap.
Arguments IsSpectrumMap {X Y _ _} f.

Definition smap_deloop {X Y : pType}
  `{IsPreSpectrum X} `{IsPreSpectrum Y} (f : X ->* Y)
  {sf : IsSpectrumMap f}
  : deloop X ->* deloop Y
  := sforall_deloop sf.

Definition smap_square {X Y : pType}
  `{IsPreSpectrum X} `{IsPreSpectrum Y} (f : X ->* Y)
  {sf : IsSpectrumMap f}
  : Square (A := pType) (glue X) (glue Y) f
      (fmap loops (smap_deloop f))
  := sforall_glue sf.

Instance issmap_deloop {X Y : pType}
  `{IsPreSpectrum X} `{IsPreSpectrum Y} (f : X ->* Y)
  {sf : IsSpectrumMap f}
  : IsSpectrumMap (smap_deloop f)
  := issforall_deloop sf.

Arguments smap_deloop {X Y _ _} f {_}.
Arguments smap_square {X Y _ _} f {_}.

Global Existing Instance issmap_deloop.

Definition SpectrumMap (X Y : pType)
  `{IsPreSpectrum X} `{IsPreSpectrum Y}
  := sForall (@sfam_const X Y _ _).

Definition smap {X Y : pType}
  `{IsPreSpectrum X} `{IsPreSpectrum Y}
  (f : SpectrumMap X Y) : X ->* Y
  := sforall_fun f.

Arguments smap {X Y _ _} _.
Coercion smap : SpectrumMap >-> pForall.

Instance issmap {X Y : pType}
  `{IsPreSpectrum X} `{IsPreSpectrum Y}
  (f : SpectrumMap X Y) : IsSpectrumMap f
  := issforall_sforall f.

Definition smap_deloop' {X Y : pType}
  {psX : IsPreSpectrum X} {psY : IsPreSpectrum Y}
  (f : @SpectrumMap X Y psX psY)
  : @SpectrumMap (deloop X) (deloop Y)
      (isprespectrum_deloop X psX) (isprespectrum_deloop Y psY)
.
Proof.
  exact (sforall_deloop' f).
Defined.

(** Applying loops at every level gives another prespectrum. *)
CoFixpoint isprespectrum_loops
  (X : pType) `{IsPreSpectrum X}
  : IsPreSpectrum (loops X).
Proof.
  snapply Build_IsPreSpectrum.
  - exact (loops (deloop X)).
  - exact (fmap loops (glue X)).
  - napply isprespectrum_loops; exact _.
Defined.

Global Existing Instance isprespectrum_loops.

(** Levelwise loops of a map of prespectra. *)
CoFixpoint issmap_loops
  {X Y : pType}
  {psX : IsPreSpectrum X} {psY : IsPreSpectrum Y}
  (f : @SpectrumMap X Y psX psY)
  : @IsSpectrumMap (loops X) (loops Y)
      (isprespectrum_loops X) (isprespectrum_loops Y)
      (fmap loops f).
Proof.
  snapply Build_IsSForall.
  - exact (fmap loops (smap_deloop' f)).
  - exact (fmap_square loops (smap_square f)).
  - napply issmap_loops.
Defined.

Definition smap_loops
  {X Y : pType}
  {psX : IsPreSpectrum X} {psY : IsPreSpectrum Y}
  (f : @SpectrumMap X Y psX psY)
  : @SpectrumMap (loops X) (loops Y)
      (isprespectrum_loops X) (isprespectrum_loops Y).
Proof.
  snapply exist.
  - exact (fmap loops f).
  - napply issmap_loops.
Defined.

(** The structure map of a prespectrum is itself a map of prespectra. *)
CoFixpoint issmap_glue
  (X : pType) `{IsPreSpectrum X}
  : IsSpectrumMap (glue X).
Proof.
  snapply Build_IsSForall.
  - exact (glue (deloop X)).
  - change (fmap loops (glue (deloop X)) o* glue X ==*
      fmap loops (glue (deloop X)) o* glue X).
    exact (phomotopy_reflexive _).
  - napply issmap_glue.
Defined.

Definition smap_glue
  (X : pType) `{IsPreSpectrum X}
  : SpectrumMap X (loops (deloop X)).
Proof.
  snapply exist.
  - exact (glue X).
  - napply issmap_glue.
Defined.

(** The constant pointed map is a map of prespectra. *)
CoFixpoint issmap_pconst
  {X Y : pType} `{IsPreSpectrum X} `{IsPreSpectrum Y}
  : IsSpectrumMap (@pconst X Y).
Proof.
  snapply Build_IsSForall.
  - exact pconst.
  - change (glue Y o* pconst ==*
      fmap loops pconst o* glue X).
    refine (precompose_pconst (glue Y) @* _).
    refine ((postcompose_pconst (glue X))^* @* _).
    exact (pmap_prewhisker (glue X) fmap_loops_pconst)^*.
  - napply issmap_pconst.
Defined.

Definition smap_pconst
  {X Y : pType} `{IsPreSpectrum X} `{IsPreSpectrum Y}
  : SpectrumMap X Y.
Proof.
  snapply exist.
  - exact pconst.
  - napply issmap_pconst.
Defined.

(** ** Higher globes of maps *)

(** Homotopies and all higher globes are obtained by iterating [sForall], just as the globes of [pType] are obtained by iterating [pForall].  No compatibility with the proof-valued relation of the preceding globe is imposed. *)
CoFixpoint issfam_homotopy {X : pType} `{IsPreSpectrum X}
  (P : sFam X) (f g : sForall P)
  : IsSFam (pfam_phomotopy f g).
Proof.
  snapply Build_IsSFam.
  - exact (pfam_phomotopy
      (sforall_deloop' f) (sforall_deloop' g)).
  - exact (@issfam_homotopy (deloop X) _
      (sfam_deloop P) (sforall_deloop' f)
      (sforall_deloop' g)).
  - intros p q.
    exact Unit.
Defined.

Definition sfam_homotopy {X : pType} `{IsPreSpectrum X}
  {P : sFam X} (f g : sForall P)
  : sFam X
  := (pfam_phomotopy f g; issfam_homotopy P f g).

Definition sHomotopy {X : pType} `{IsPreSpectrum X}
  {P : sFam X} (f g : sForall P)
  := sForall (sfam_homotopy f g).

Definition SpectrumMapHomotopy {X Y : pType}
  `{IsPreSpectrum X} `{IsPreSpectrum Y}
  (f g : SpectrumMap X Y)
  (p : smap f $== smap g)
  := IsSForall (sfam_homotopy f g) p.

Definition smap_homotopy_deloop
  {X Y : pType} `{IsPreSpectrum X} `{IsPreSpectrum Y}
  {f g : SpectrumMap X Y}
  {p : smap f $== smap g}
  (sp : SpectrumMapHomotopy f g p)
  : smap (smap_deloop' f)
    $== smap (smap_deloop' g)
  := sforall_deloop sp.

Definition smap_homotopy_deloop_is
  {X Y : pType} `{IsPreSpectrum X} `{IsPreSpectrum Y}
  {f g : SpectrumMap X Y}
  {p : smap f $== smap g}
  (sp : SpectrumMapHomotopy f g p)
  : SpectrumMapHomotopy
      (smap_deloop' f) (smap_deloop' g)
      (smap_homotopy_deloop sp)
  := issforall_deloop sp.

Arguments smap_homotopy_deloop
  {X Y _ _ f g p} _.
Arguments smap_homotopy_deloop_is
  {X Y _ _ f g p} _.

(** Levelwise loops of a homotopy of maps of prespectra. *)
CoFixpoint smap_homotopy_loops
  {X Y : pType} `{IsPreSpectrum X} `{IsPreSpectrum Y}
  {f g : SpectrumMap X Y}
  {p : smap f $== smap g}
  (sp : SpectrumMapHomotopy f g p)
  : SpectrumMapHomotopy (smap_loops f) (smap_loops g)
      (fmap2 loops p).
Proof.
  snapply Build_IsSForall.
  - exact (fmap2 loops (smap_homotopy_deloop sp)).
  - exact tt.
  - napply smap_homotopy_loops.
    exact (smap_homotopy_deloop_is sp).
Defined.

(** ** Identity and composition *)

CoFixpoint issmap_id (X : pType) `{IsPreSpectrum X}
  : IsSpectrumMap (@pmap_idmap X)
.
Proof.
  snapply Build_IsSForall.
  - exact pmap_idmap.
  - change (Square (A := pType) (glue X) (glue X)
      pmap_idmap (fmap loops pmap_idmap)).
    napply vconcatR.
    + napply hrefl.
    + exact (fmap_id loops (deloop X)).
  - napply issmap_id.
Defined.

CoFixpoint issmap_compose {X Y Z : pType}
  `{IsPreSpectrum X} `{IsPreSpectrum Y} `{IsPreSpectrum Z}
  (g : SpectrumMap Y Z) (f : SpectrumMap X Y)
  : IsSpectrumMap (g o* f)
.
Proof.
  snapply Build_IsSForall.
  - exact (smap_deloop g o* smap_deloop f).
  - change (Square (A := pType) (glue X) (glue Z)
      (g o* f)
      (fmap loops
        (smap_deloop g o* smap_deloop f))).
    napply vconcatR.
    + napply hconcat.
      * rapply smap_square.
      * rapply smap_square.
    + exact (fmap_comp loops
        (smap_deloop f) (smap_deloop g)).
  - change (IsSpectrumMap
      (smap_deloop' g o* smap_deloop' f)).
    napply issmap_compose.
Defined.

Definition smap_id (X : pType) `{IsPreSpectrum X}
  : SpectrumMap X X.
Proof.
  snapply exist.
  - exact pmap_idmap.
  - napply issmap_id.
Defined.

Definition smap_compose {X Y Z : pType}
  `{IsPreSpectrum X} `{IsPreSpectrum Y} `{IsPreSpectrum Z}
  (g : SpectrumMap Y Z) (f : SpectrumMap X Y)
  : SpectrumMap X Z.
Proof.
  snapply exist.
  - exact (g o* f).
  - napply issmap_compose.
Defined.

CoFixpoint smap_homotopy_loops_id
  (X : pType) `{IsPreSpectrum X}
  : SpectrumMapHomotopy
      (smap_loops (smap_id X)) (smap_id (loops X))
      (fmap_id loops X).
Proof.
  snapply Build_IsSForall.
  - exact (fmap_id loops (deloop X)).
  - exact tt.
  - napply smap_homotopy_loops_id.
Defined.

CoFixpoint smap_homotopy_loops_compose
  {X Y Z : pType}
  `{IsPreSpectrum X} `{IsPreSpectrum Y} `{IsPreSpectrum Z}
  (g : SpectrumMap Y Z) (f : SpectrumMap X Y)
  : SpectrumMapHomotopy
      (smap_loops (smap_compose g f))
      (smap_compose (smap_loops g) (smap_loops f))
      (fmap_comp loops f g).
Proof.
  snapply Build_IsSForall.
  - exact (fmap_comp loops
      (smap_deloop' f) (smap_deloop' g)).
  - exact tt.
  - exact (@smap_homotopy_loops_compose
      (deloop X) (deloop Y) (deloop Z) _ _ _
      (smap_deloop' g) (smap_deloop' f)).
Defined.

(** The structure maps are natural in maps of prespectra. *)
CoFixpoint smap_homotopy_glue_natural
  {X Y : pType} `{IsPreSpectrum X} `{IsPreSpectrum Y}
  (f : SpectrumMap X Y)
  : SpectrumMapHomotopy
      (smap_compose (smap_glue Y) f)
      (smap_compose (smap_loops (smap_deloop' f))
        (smap_glue X))
      (smap_square f).
Proof.
  snapply Build_IsSForall.
  - exact (smap_square (smap_deloop' f)).
  - exact tt.
  - exact (@smap_homotopy_glue_natural
      (deloop X) (deloop Y) _ _ (smap_deloop' f)).
Defined.

(** ** Operations on higher globes *)

CoFixpoint smap_homotopy_id {X Y : pType}
  `{IsPreSpectrum X} `{IsPreSpectrum Y}
  (f : SpectrumMap X Y)
  : SpectrumMapHomotopy f f (Id (smap f)).
Proof.
  snapply Build_IsSForall.
  - exact (Id (smap (smap_deloop' f))).
  - exact tt.
  - napply smap_homotopy_id.
Defined.

CoFixpoint smap_homotopy_compose {X Y : pType}
  `{IsPreSpectrum X} `{IsPreSpectrum Y}
  {f g h : SpectrumMap X Y}
  {p : smap f $== smap g}
  {q : smap g $== smap h}
  (sq : SpectrumMapHomotopy g h q)
  (sp : SpectrumMapHomotopy f g p)
  : SpectrumMapHomotopy f h (p $@ q).
Proof.
  snapply Build_IsSForall.
  - exact (smap_homotopy_deloop sp
      $@ smap_homotopy_deloop sq).
  - exact tt.
  - napply (@smap_homotopy_compose
      (deloop X) (deloop Y)).
    + exact (smap_homotopy_deloop_is sq).
    + exact (smap_homotopy_deloop_is sp).
Defined.

CoFixpoint smap_homotopy_rev {X Y : pType}
  `{IsPreSpectrum X} `{IsPreSpectrum Y}
  {f g : SpectrumMap X Y}
  {p : smap f $== smap g}
  (sp : SpectrumMapHomotopy f g p)
  : SpectrumMapHomotopy g f p^$.
Proof.
  snapply Build_IsSForall.
  - exact (smap_homotopy_deloop sp)^$.
  - exact tt.
  - napply (@smap_homotopy_rev
      (deloop X) (deloop Y)).
    exact (smap_homotopy_deloop_is sp).
Defined.

Arguments smap_homotopy_id {X Y _ _} _.
Arguments smap_homotopy_compose
  {X Y _ _ f g h p q} _ _.
Arguments smap_homotopy_rev
  {X Y _ _ f g p} _.

CoFixpoint smap_homotopy_postwhisker
  {X Y Z : pType}
  `{IsPreSpectrum X} `{IsPreSpectrum Y} `{IsPreSpectrum Z}
  (h : SpectrumMap Y Z)
  {f g : SpectrumMap X Y}
  {p : smap f $== smap g}
  (sp : SpectrumMapHomotopy f g p)
  : SpectrumMapHomotopy
      (smap_compose h f)
      (smap_compose h g)
      (pmap_postwhisker h p).
Proof.
  snapply Build_IsSForall.
  - exact (pmap_postwhisker
      (smap (smap_deloop' h))
      (smap_homotopy_deloop sp)).
  - exact tt.
  - exact (@smap_homotopy_postwhisker
      (deloop X) (deloop Y) (deloop Z) _ _ _
      (smap_deloop' h)
      (smap_deloop' f) (smap_deloop' g)
      (smap_homotopy_deloop sp)
      (smap_homotopy_deloop_is sp)).
Defined.

CoFixpoint smap_homotopy_prewhisker
  {X Y Z : pType}
  `{IsPreSpectrum X} `{IsPreSpectrum Y} `{IsPreSpectrum Z}
  (f : SpectrumMap X Y)
  {g h : SpectrumMap Y Z}
  {p : smap g $== smap h}
  (sp : SpectrumMapHomotopy g h p)
  : SpectrumMapHomotopy
      (smap_compose g f)
      (smap_compose h f)
      (pmap_prewhisker f p).
Proof.
  snapply Build_IsSForall.
  - exact (pmap_prewhisker
      (smap (smap_deloop' f))
      (smap_homotopy_deloop sp)).
  - exact tt.
  - exact (@smap_homotopy_prewhisker
      (deloop X) (deloop Y) (deloop Z) _ _ _
      (smap_deloop' f)
      (smap_deloop' g) (smap_deloop' h)
      (smap_homotopy_deloop sp)
      (smap_homotopy_deloop_is sp)).
Defined.

Arguments smap_homotopy_postwhisker
  {X Y Z _ _ _} _ {f g p} _.
Arguments smap_homotopy_prewhisker
  {X Y Z _ _ _} _ {g h p} _.

CoFixpoint smap_homotopy_assoc
  {W X Y Z : pType}
  `{IsPreSpectrum W} `{IsPreSpectrum X}
  `{IsPreSpectrum Y} `{IsPreSpectrum Z}
  (f : SpectrumMap W X) (g : SpectrumMap X Y)
  (h : SpectrumMap Y Z)
  : SpectrumMapHomotopy
      (smap_compose (smap_compose h g) f)
      (smap_compose h (smap_compose g f))
      (pmap_compose_assoc h g f).
Proof.
  snapply Build_IsSForall.
  - exact (pmap_compose_assoc
      (smap (smap_deloop' h))
      (smap (smap_deloop' g))
      (smap (smap_deloop' f))).
  - exact tt.
  - exact (@smap_homotopy_assoc
      (deloop W) (deloop X) (deloop Y) (deloop Z)
      _ _ _ _ (smap_deloop' f)
      (smap_deloop' g) (smap_deloop' h)).
Defined.

Definition smap_homotopy_assoc_opp
  {W X Y Z : pType}
  `{IsPreSpectrum W} `{IsPreSpectrum X}
  `{IsPreSpectrum Y} `{IsPreSpectrum Z}
  (f : SpectrumMap W X) (g : SpectrumMap X Y)
  (h : SpectrumMap Y Z)
  : SpectrumMapHomotopy
      (smap_compose h (smap_compose g f))
      (smap_compose (smap_compose h g) f)
      (pmap_compose_assoc h g f)^$.
Proof.
  napply smap_homotopy_rev.
  napply smap_homotopy_assoc.
Defined.

CoFixpoint smap_homotopy_idl {X Y : pType}
  `{IsPreSpectrum X} `{IsPreSpectrum Y}
  (f : SpectrumMap X Y)
  : SpectrumMapHomotopy
      (smap_compose (smap_id Y) f) f
      (pmap_postcompose_idmap f).
Proof.
  snapply Build_IsSForall.
  - exact (pmap_postcompose_idmap
      (smap (smap_deloop' f))).
  - exact tt.
  - exact (@smap_homotopy_idl
      (deloop X) (deloop Y) _ _
      (smap_deloop' f)).
Defined.

CoFixpoint smap_homotopy_idr {X Y : pType}
  `{IsPreSpectrum X} `{IsPreSpectrum Y}
  (f : SpectrumMap X Y)
  : SpectrumMapHomotopy
      (smap_compose f (smap_id X)) f
      (pmap_precompose_idmap f).
Proof.
  snapply Build_IsSForall.
  - exact (pmap_precompose_idmap
      (smap (smap_deloop' f))).
  - exact tt.
  - exact (@smap_homotopy_idr
      (deloop X) (deloop Y) _ _
      (smap_deloop' f)).
Defined.

(** ** Displayed wild category structures *)

Instance isdgraph_isprespectrum : IsDGraph IsPreSpectrum.
Proof.
  intros X Y f psX psY.
  exact (@IsSpectrumMap X Y psX psY f).
Defined.

Instance isd01cat_isprespectrum : IsD01Cat IsPreSpectrum.
Proof.
  snapply Build_IsD01Cat.
  - intros X psX.
    napply issmap_id.
  - intros X Y Z g f psX psY psZ sg sf.
    exact (issmap_compose
      (g; sg) (f; sf)).
Defined.

Instance isd2graph_isprespectrum : IsD2Graph IsPreSpectrum.
Proof.
  intros X Y psX psY.
  intros f g p sf sg.
  exact (SpectrumMapHomotopy (f; sf) (g; sg) p).
Defined.

Instance isd1cat_isprespectrum : IsD1Cat IsPreSpectrum.
Proof.
  snapply Build_IsD1Cat.
  - intros X Y psX psY.
    snapply Build_IsD01Cat.
    + intros f sf.
      exact (smap_homotopy_id (f; sf)).
    + intros f g h q p sf sg sh sq sp.
      exact (smap_homotopy_compose sq sp).
  - intros X Y psX psY f g p sf sg sp.
    exact (smap_homotopy_rev sp).
  - intros X Y Z g psX psY psZ sg.
    intros f h p sf sh sp.
    exact (smap_homotopy_postwhisker (g; sg) sp).
  - intros X Y Z f psX psY psZ sf.
    intros g h p sg sh sp.
    exact (smap_homotopy_prewhisker (f; sf) sp).
  - intros W X Y Z f g h psW psX psY psZ sf sg sh.
    exact (smap_homotopy_assoc
      (f; sf) (g; sg) (h; sh)).
  - intros W X Y Z f g h psW psX psY psZ sf sg sh.
    exact (smap_homotopy_assoc_opp
      (f; sf) (g; sg) (h; sh)).
  - intros X Y f psX psY sf.
    exact (smap_homotopy_idl (f; sf)).
  - intros X Y f psX psY sf.
    exact (smap_homotopy_idr (f; sf)).
Defined.

(** Since [PreSpectrum] is a total type, its wild category structure is induced by the displayed instances above. *)
Instance isgraph_prespectrum : IsGraph PreSpectrum
  := isgraph_total IsPreSpectrum.

Instance is2graph_prespectrum : Is2Graph PreSpectrum
  := is2graph_total IsPreSpectrum.

Instance is01cat_prespectrum : Is01Cat PreSpectrum
  := is01cat_total IsPreSpectrum.

Instance is1cat_prespectrum : Is1Cat PreSpectrum
  := is1cat_total IsPreSpectrum.

(** Equivalences of prespectra are the bi-invertible maps in their wild 1-category. *)
Instance hasequivs_prespectrum : HasEquivs PreSpectrum
  := cat_hasequivs PreSpectrum.

Instance isgraph_spectrum : IsGraph Spectrum
  := isgraph_induced prespectrum_spectrum.

Instance is01cat_spectrum : Is01Cat Spectrum
  := is01cat_induced prespectrum_spectrum.

Instance is2graph_spectrum : Is2Graph Spectrum
  := is2graph_induced prespectrum_spectrum.

Instance is1cat_spectrum : Is1Cat Spectrum
  := is1cat_induced prespectrum_spectrum.

Instance hasequivs_spectrum : HasEquivs Spectrum
  := hasequivs_induced prespectrum_spectrum.

(** The wild category structure on [Spectrum] and the functoriality of the forgetful map are induced directly from [PreSpectrum]. *)
Instance is0functor_prespectrum_spectrum
  : Is0Functor prespectrum_spectrum
  := is0functor_induced prespectrum_spectrum.

Instance is1functor_prespectrum_spectrum
  : Is1Functor prespectrum_spectrum
  := is1functor_induced prespectrum_spectrum.
