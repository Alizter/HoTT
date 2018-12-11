Require Import HoTT.Basics.
Require Import HoTT.Types.

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
  Context (P : Poly I).
  
  (** The type of Trees (given a polynomial P) **)
  Inductive Tree : I -> Type :=
    | lf (i : I) : Tree i
    | nd {i : I} : (br P) Tree i -> Tree i.
  
  (** The type of leaves of a tree **)
  Fixpoint Leaf {i : I} (w : Tree i) (j : I) : Type :=
    match w with
      | lf _ => i = j
      | nd _ (f; phi) => 
          exists (k:I) (p : Param P f k), Leaf (phi k p) j
    end.
  
  (** The type of nodes of a tree **)
  Fixpoint Node {i : I} (w : Tree i) (p : Ops P) : Type :=
    match w with
      | lf _ => Lift Empty
      | nd j (f; phi) => 
          ((j; f) = p) + 
          exists (k : I) (q : Param P f k), Node (phi k q) p
    end.
  
  (** The frame of a tree (draw a box around a tree to
      package it into an operator). **)
  Definition Frame {i : I} (w : Tree i) (f : Op P i) : Type :=
    forall (j : I), Leaf w j <~> Param P f j.
  
  Definition InFrame (m : Ops P) : Type :=
    match m with (i; f) => exists (w : Tree i), Frame w f end.
  
  Definition OutFrame {i : I} (w : Tree i) : Type :=
    exists (f : Op P i), Frame w f.
  
  (** Polynomial relation **)
  Definition PolyRel : Type :=
    forall (f : Ops P), InFrame f -> Type.
  
End Polynomial.
  
Section PolyMagma.

  (** Type of polynomial magmas **)
  Record PolyMagma {I : Type} (P : Poly I) : Type := 
    mgm {
      mu {i : I} (w : Tree P i) : Op P i ;
      mu_frm {i : I} (w : Tree P i) : Frame w (mu w) ;
  }.
  
  (** Slice of polynomial by a relation **)
  Definition PolySlice {I : Type} (P : Poly I) (R : PolyRel P)
    : Poly (Ops P) := Build_Poly
      (fun f => exists (e : InFrame f), R f e) 
      (fun f t => match t with ((w ; _) ; _) => Node w end).
  
  (** The relation induced by a magma **)
  Definition MagmaRel {I : Type} {P : Poly I} (M : PolyMagma P) : PolyRel P.
  Proof.
    intro i_f; destruct i_f as [i f];
    intro w_a; destruct w_a as [w a];
    refine ((mu M w; mu_frm M w) = (f; a)).
  Defined.
  
End PolyMagma.

Notation "P // R" := (@PolySlice _ P R) : polyscope.

Section PolyMonad.
  
  Context {I : Type} {P : Poly I} (R : PolyRel P).
  
  Global Open Scope polyscope.
  
  (* (** Flatten a sliced tree **)
  Definition Flatten {i : I} {f : Op P i} (w : Tree (P // R) (i; f)) : Tree P i :=
    match w with
      | (lf (i; f)) => corolla P f
      | (nd (((w; a); _); k)) =>


 *)


