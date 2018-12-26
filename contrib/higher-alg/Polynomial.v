Require Import HoTT.Basics.
Require Import HoTT.Types.
Require Import Basics.Equivalences.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Section Polynomial.
  
  (** Type of polynomials **)
  Record Poly (I  : Type) : Type := {
    Op : I -> Type;
    Param {i : I} : Op i -> I -> Type;
  }.
  
  (** We add our type of sorts I to the contet **)
  Context {I : Type}.
  
  (** Type of operators of a polynomial **)
  Definition Ops (P : Poly I) : Type := 
    exists (i : I), Op P i.
  
  (** Type of Arities of a polynomial **)
  Definition Arity (P : Poly I) {i : I} (f : Op P i) : Type :=
    exists (j : I), Param P f j.
  
  (** Eric uses a double bracket notation in agda for phi **)
  Definition br (P : Poly I) (X : I -> Type) (i : I) : Type
    := exists (f : Op P i), forall j, Param P f j -> X j.
  
  (** We add a polynomial P to the environment **)
   Context {P : Poly I}.
  
  (** The type of Trees (given a polynomial P) **)
  Inductive Tree : I -> Type :=
    | lf (i : I) : Tree i
    | nd {i : I} : (br P) Tree i -> Tree i.
  
  (** The type of leaves of a tree **)
  Fixpoint Leaf {i : I} (w : Tree i) : I -> Type.
  Proof.
    induction w.
    + intro j; refine (i = j).
    + destruct b as [f phi]; intro j.
      refine (exists (k : I) (p : Param P f k), Leaf _ (phi k p) j).
  Defined.
  
  (** The type of nodes of a tree **)
  Fixpoint Node {i : I} (w : Tree i) : Ops P -> Type.
  Proof.
    induction w.
    + intro p; refine (Lift Empty).
    + intro jg. destruct jg as [j g]. destruct b as [f phi].
      refine (
        ((i;f) = (j;g)) + 
        exists (k : I) (p : Param P f k), Node _(phi k p) (j;g)).
  Defined.
  
  (** The frame of a tree (draw a box around a tree to
      package it into an operator). **)
  Definition Frame  {i : I} (w : Tree i) (f : Op P i) : Type :=
    forall (j : I), Leaf w j <~> Param P f j.
  
  Definition InFrame (m : Ops P) : Type :=
    match m with (i; f) => exists (w : Tree i), Frame w f end.
  
  Definition OutFrame {i : I} (w : Tree i) : Type :=
    exists (f : Op P i), Frame w f.
  
  (** Polynomial relation **)
  Definition PolyRel := forall (f : Ops P), InFrame f -> Type.
  
  (** Coroll a? I think these are corollaries? **)
  Corollary Corolla {i : I} (f : Op P i) : Tree i.
  Proof.
    refine (nd (f; fun j p => lf j)).
  Defined.
  
   (** Corolla-frm **)
  Corollary Corolla_Frm  {i : I} (f : Op P i) (j : I) 
    : Leaf (Corolla f) j <~> Param _ f j.
  Proof.
    serapply (equiv_adjointify).
    + intro; destruct X as [a b]; destruct b as [b c]; destruct c; refine b.
    + refine (fun p => (j ; p ; idpath)).
    + refine (fun p => idpath).
    + refine (fun x => match x with (a ; p ; c) => _ end);
        destruct c; refine idpath.
  Defined.
  
End Polynomial.
  
Section PolyMagma.

  (** Type of polynomial magmas **)
  Record PolyMagma {I : Type} (P : Poly I) : Type := 
    mgm {
      mu {i : I} (w : @Tree _ P i) : Op P i ;
      mu_frm {i : I} (w : @Tree _ P i) : Frame w (mu w) ;
  }.
  
  (** Slice of polynomial by a relation **)
  Definition PolySlice {I : Type} (P : Poly I) (R : PolyRel)
    : Poly (Ops P) := Build_Poly
      (fun f => exists (e : InFrame f), R f e) 
      (fun f t => match t with ((w ; _) ; _) => Node w end).
  
  (** The relation induced by a magma **)
  Definition MagmaRel {I : Type} {P : Poly I} (M : PolyMagma P) : @PolyRel _ P.
  Proof.
    intro i_f; destruct i_f as [i f];
    intro w_a; destruct w_a as [w a];
    refine ((mu M w; mu_frm M w) = (f; a)).
  Defined.
  
End PolyMagma.

Notation "P // R" := (@PolySlice _ P R) : polyscope.


Section PolyMonad.
  
  Context {I : Type} {P : Poly I} {R : @PolyRel _ P}.
  
  Global Open Scope polyscope.
  
   (** Flatten a sliced tree **)
  Definition Flatten {i : I} {f : Op P i} (w : @Tree _ (P // R) (i; f)) : @Tree _ P i.
  Proof.
    induction w.
    + refine (@Corolla _ P _ f).
    + 
      match w with
      | (lf (i; f)) => corolla P f
      | (nd (((w; a); _); k)) =>


 *)


