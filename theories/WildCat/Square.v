Require Import Basics.Overture Basics.Tactics.
Require Import WildCat.Core.
Require Import WildCat.Equiv.

(** * Squares of morphisms in a Wild Category.  *)

(** These come up a lot as naturality squares. In this file we define basic operations on squares, to conveniently work with them. *)

(** A Square is a cubical 2-cell in a 1-category. The order of the arguments is left-right-top-bottom: [Square l r t b].  It is defined to be [r $o t $== b $o l]. *)

Definition Square@{u v w} {A : Type@{u}} `{Is1Cat@{u w v} A} {x00 x20 x02 x22 : A}
  (f01 : x00 $-> x02) (f21 : x20 $-> x22) (f10 : x00 $-> x20) (f12 : x02 $-> x22) 
  : Type@{w}
  := f21 $o f10 $== f12 $o f01.

Section Squares.
  (* We declare a context with a lot of variables: the first component is horizontal, the second vertical.
    x00 f10 x20 f30 x40
    f01     f21     f41
    x02 f12 x22 f32 x42
    f03     f23     f43
    x04 f14 x24 f34 x44 
  All morphisms are pointed to the right or down. *)
  Context {A : Type} `{Is1Cat A} {x x' x00 x20 x40 x02 x22 x42 x04 x24 x44 : A}
    {f10 f10' : x00 $-> x20} {f30 : x20 $-> x40} 
    {f12 f12' : x02 $-> x22} {f32 : x22 $-> x42} 
    {f14 : x04 $-> x24} {f34 : x24 $-> x44}
    {f01 f01' : x00 $-> x02} {f21 f21' : x20 $-> x22} {f41 f41' : x40 $-> x42}
    {f03 : x02 $-> x04} {f23 : x22 $-> x24} {f43 : x42 $-> x44}.

  (** We give a "constructor" and "destructor" for squares. *)
  Definition Build_Square (p : f21 $o f10 $== f12 $o f01) : Square f01 f21 f10 f12 := p.
  Definition gpdhom_square (s : Square f01 f21 f10 f12) : f21 $o f10 $== f12 $o f01 := s.

  (** Squares degenerate in two sides given by a single 2-morphism. *)
  Definition hdeg_square {f f' : x $-> x'} (p : f $== f') : Square f f' (Id x) (Id x')
    := cat_idr f' $@ p^$ $@ (cat_idl f)^$.
  Definition vdeg_square {f f' : x $-> x'} (p : f $== f') : Square (Id x) (Id x') f f'
    := cat_idl f $@ p $@ (cat_idr f')^$.

  (** Squares degenerate in two sides given by the identity 2-morphism at some morphism. *)
  Definition hrefl (f : x $-> x') : Square f f (Id x) (Id x')
    := cat_idr f $@ (cat_idl f)^$.
  Definition vrefl (f : x $-> x') : Square (Id x) (Id x') f f
    := cat_idl f $@ (cat_idr f)^$.

  (** The transpose of a square *)
  Definition transpose (s : Square f01 f21 f10 f12) : Square f10 f12 f01 f21 := s^$.

  (** Horizontal and vertical concatenation of squares *)
  Definition hconcat (s : Square f01 f21 f10 f12) (t : Square f21 f41 f30 f32)
    : Square f01 f41 (f30 $o f10) (f32 $o f12)
    := (cat_assoc _ _ _)^$ $@ (t $@R f10) $@ cat_assoc _ _ _ $@ (f32 $@L s) $@ (cat_assoc _ _ _)^$.
  Definition vconcat (s : Square f01 f21 f10 f12) (t : Square f03 f23 f12 f14)
    : Square (f03 $o f01) (f23 $o f21) f10 f14
  := (cat_assoc _ _ _ $@ (f23 $@L s))
    $@ ((cat_assoc_opp _ _ _ $@ (t $@R f01))
      $@ cat_assoc _ _ _).

  (** If the horizontal morphisms in a square are equivalences then we can flip the square by inverting them. *)
  Definition hinverse {HE : HasEquivs A} (f10 : x00 $<~> x20) (f12 : x02 $<~> x22) (s : Square f01 f21 f10 f12)
    : Square f21 f01 f10^-1$ f12^-1$
    := (cat_idl _)^$ $@ ((cate_issect f12)^$ $@R _) $@ cat_assoc _ _ _
      $@ (_ $@L ((cat_assoc _ _ _)^$ $@ (s^$ $@R _) $@ cat_assoc _ _ _
      $@ (_ $@L cate_isretr f10) $@ cat_idr _)).

  (** The following four declarations modify one side of a Square using a 2-cell. The L or R indicate the side of the 2-cell. This can be thought of as rewriting the sides of a square using a homotopy. *)

  (** Rewriting the left edge. *)
  Definition hconcatL (p : f01' $== f01) (s : Square f01 f21 f10 f12)
    : Square f01' f21 f10 f12
    := s $@ (f12 $@L p^$).

  (** Rewriting the right edge. *)
  Definition hconcatR (s : Square f01 f21 f10 f12) (p : f21' $== f21)
    : Square f01 f21' f10 f12
    := (p $@R f10) $@ s.

  (** Rewriting the top edge. *)
  Definition vconcatL (p : f10' $== f10) (s : Square f01 f21 f10 f12)
    : Square f01 f21 f10' f12
    := (f21 $@L p) $@ s.

  (** Rewriting the bottom edge. *)
  Definition vconcatR (s : Square f01 f21 f10 f12) (p : f12' $== f12)
    : Square f01 f21 f10 f12'
    := s $@ (p^$ $@R f01).

End Squares.

(** Reversing a square in a 1-groupoid reverses its two vertical
    edges and exchanges its top and bottom. *)
Definition vinverse_square_gpd
  {A : Type} `{Is1Gpd A}
  {x00 x20 x02 x22 : A}
  {f01 : x00 $-> x02} {f21 : x20 $-> x22}
  {f10 : x00 $-> x20} {f12 : x02 $-> x22}
  (s : Square f01 f21 f10 f12)
  : Square f01^$ f21^$ f12 f10.
Proof.
  apply gpd_moveR_Vh.
  rapply (_ $@ cat_assoc _ _ _).
  apply gpd_moveL_hV.
  exact (transpose s).
Defined.

(** Reversing the horizontal edges is obtained by transposing,
    reversing the vertical edges, and transposing back. *)
Definition hinverse_square_gpd
  {A : Type} `{Is1Gpd A}
  {x00 x20 x02 x22 : A}
  {f01 : x00 $-> x02} {f21 : x20 $-> x22}
  {f10 : x00 $-> x20} {f12 : x02 $-> x22}
  (s : Square f01 f21 f10 f12)
  : Square f21 f01 f10^$ f12^$
  := transpose (vinverse_square_gpd (transpose s)).

(** Rotate a square after exposing one factor at each end of its
    horizontal boundary. *)
Definition square_rotate_composites
  {A : Type} `{Is1Gpd A}
  {x0 x1 x2 x3 x4 x5 : A}
  {l : x0 $-> x1} {r : x2 $-> x3}
  {t0 : x0 $-> x4} {t1 : x4 $-> x2}
  {b0 : x1 $-> x5} {b1 : x5 $-> x3}
  (s : Square l r (t1 $o t0) (b1 $o b0))
  : Square t1 b0 (l $o t0^$) (b1^$ $o r).
Proof.
  unfold Square in *.
  rhs' exact (cat_assoc t1 r b1^$).
  apply gpd_moveL_Vh.
  lhs' exact (cat_assoc_opp (l $o t0^$) b0 b1).
  lhs' exact (cat_assoc_opp t0^$ l (b1 $o b0)).
  apply gpd_moveR_hV.
  exact (s^$ $@ cat_assoc_opp t0 t1 r).
Defined.

(** Whiskering a corner of a square by an invertible morphism in a
    1-groupoid. *)
Definition whiskerTR_gpd
  {A : Type} `{Is1Gpd A}
  {x x00 x20 x02 x22 : A}
  {t : x00 $-> x20} {b : x02 $-> x22}
  {l : x00 $-> x02} {r : x20 $-> x22}
  (f : x20 $-> x) (s : Square l r t b)
  : Square l (r $o f^$) (f $o t) b
  := cat_assoc _ _ _ $@ (r $@L gpd_V_hh f t) $@ s.

Definition whiskerBL_gpd
  {A : Type} `{Is1Gpd A}
  {x x00 x20 x02 x22 : A}
  {t : x00 $-> x20} {b : x02 $-> x22}
  {l : x00 $-> x02} {r : x20 $-> x22}
  (f : x $-> x02) (s : Square l r t b)
  : Square (f^$ $o l) r t (b $o f)
  := s $@ ((gpd_hh_V b f)^$ $@R l) $@ cat_assoc _ _ _.

(** Whisker the lower-left corner in a 1-groupoid, using the canonical
    inverse of the new edge. *)
Definition whiskerLB_gpd
  {A : Type} `{Is1Gpd A}
  {x x00 x20 x02 x22 : A}
  {t : x00 $-> x20} {b : x02 $-> x22}
  {l : x00 $-> x02} {r : x20 $-> x22}
  (f : x02 $-> x) (s : Square l r t b)
  : Square (f $o l) r t (b $o f^$)
  := s $@ ((gpd_hV_h b f)^$ $@R l) $@ cat_assoc _ _ _.

Section Squares2.

  (** We declare the context again, so that we can reuse some declarations where the variables have been inserted. This would not need to be done if Coq could generalize variables within sections. Currently this is possible in Lean and Agda. *)
  Context {A : Type} `{HasEquivs A}
    {x x' x00 x20 x40 x02 x22 x42 x04 x24 x44 : A}
    {f10 f10' : x00 $-> x20} {f30 : x20 $-> x40} 
    {f12 f12' : x02 $-> x22} {f32 : x22 $-> x42} 
    {f14 : x04 $-> x24} {f34 : x24 $-> x44}
    {f01 f01' : x00 $-> x02} {f21 f21' : x20 $-> x22} {f41 f41' : x40 $-> x42}
    {f03 : x02 $-> x04} {f23 : x22 $-> x24} {f43 : x42 $-> x44}.

  (** If the vertical morphisms in a square are equivalences then we can flip the square by inverting them. *)
  Definition vinverse (f01 : x00 $<~> x02) (f21 : x20 $<~> x22) (s : Square f01 f21 f10 f12)
    : Square (f01^-1$) (f21^-1$) f12 f10
    := transpose (hinverse _ _ (transpose s)).

  (** Whisker a map in one of the corners. For the bottom-left and top-right we have two choices. *)

  Definition whiskerTL {f : x $-> x00} (s : Square f01 f21 f10 f12)
    : Square (f01 $o f) f21 (f10 $o f) f12
    := (cat_assoc _ _ _)^$ $@ (s $@R f) $@ cat_assoc _ _ _.

  Definition whiskerBR {f : x22 $-> x} (s : Square f01 f21 f10 f12)
    : Square f01 (f $o f21) f10 (f $o f12)
    := cat_assoc _ _ _ $@ (f $@L s) $@ (cat_assoc _ _ _)^$.

  Definition whiskerBL {f : x $<~> x02} (s : Square f01 f21 f10 f12)
    : Square (f^-1$ $o f01) f21 f10 (f12 $o f)
    := s $@ ((compose_hh_V _ _)^$ $@R f01) $@ cat_assoc _ _ _.

  Definition whiskerLB {f : x02 $<~> x} (s : Square f01 f21 f10 f12)
    : Square (f $o f01) f21 f10 (f12 $o f^-1$)
    := s $@ ((compose_hV_h _ _)^$ $@R f01) $@ cat_assoc _ _ _.

  Definition whiskerTR {f : x20 $<~> x} (s : Square f01 f21 f10 f12)
    : Square f01 (f21 $o f^-1$) (f $o f10) f12
    := cat_assoc _ _ _ $@ (f21 $@L compose_V_hh _ _) $@ s.

  Definition whiskerRT {f : x $<~> x20} (s : Square f01 f21 f10 f12)
    : Square f01 (f21 $o f) (f^-1$ $o f10) f12
    := cat_assoc _ _ _ $@ (f21 $@L compose_h_Vh _ _) $@ s.

  (** Moving around maps in a square. Associativity laws. *)

  Definition move_bottom_left {f01 : x00 $-> x} {f01' : x $-> x02}
    (s : Square (f01' $o f01) f21 f10 f12) 
    : Square f01 f21 f10 (f12 $o f01')
    := s $@ (cat_assoc _ _ _)^$.

  Definition move_left_bottom {f12 : x02 $-> x} {f12' : x $-> x22}
    (s : Square f01 f21 f10 (f12' $o f12)) 
    : Square (f12 $o f01) f21 f10 f12'
    := s $@ cat_assoc _ _ _.

  Definition move_right_top {f10 : x00 $-> x} {f10' : x $-> x20}
    (s : Square f01 f21 (f10' $o f10) f12) 
    : Square f01 (f21 $o f10') f10 f12
    := cat_assoc _ _ _ $@ s.

  Definition move_top_right {f21 : x20 $-> x} {f21' : x $-> x22}
    (s : Square f01 (f21' $o f21) f10 f12) 
    : Square f01 f21' (f21 $o f10) f12
    := (cat_assoc _ _ _)^$ $@ s.

  Definition fmap_square {B : Type} `{Is1Cat B} (f : A -> B) `{!Is0Functor f} `{!Is1Functor f}
    (s : Square f01 f21 f10 f12)
    : Square (fmap f f01) (fmap f f21) (fmap f f10) (fmap f f12)
    := (fmap_comp f _ _)^$ $@ fmap2 f s $@ fmap_comp f _ _.

End Squares2.

(** Named boundary eliminators for tactic proofs.  Representation-sensitive
    type inspection stays in this module rather than in square clients. *)
Tactic Notation "square_left" constr(s) "as" ident(left) :=
  let S := type of s in
  lazymatch S with
  | Square ?l _ _ _ => pose (left := l)
  end.

Tactic Notation "square_right" constr(s) "as" ident(right) :=
  let S := type of s in
  lazymatch S with
  | Square _ ?r _ _ => pose (right := r)
  end.

Tactic Notation "square_top" constr(s) "as" ident(top) :=
  let S := type of s in
  lazymatch S with
  | Square _ _ ?t _ => pose (top := t)
  end.

Tactic Notation "square_bottom" constr(s) "as" ident(bottom) :=
  let S := type of s in
  lazymatch S with
  | Square _ _ _ ?b => pose (bottom := b)
  end.

Tactic Notation "square_boundaries" constr(s) "as"
  ident(left) ident(right) ident(top) ident(bottom) :=
  square_left s as left;
  square_right s as right;
  square_top s as top;
  square_bottom s as bottom.

Notation "s $@h t" := (hconcat s t).
Notation "s $@v t" := (vconcat s t).
Notation "s $@hR p" := (hconcatR s p).
Notation "s $@hL p" := (hconcatL p s).
Notation "s $@vR p" := (vconcatR s p).
Notation "s $@vL p" := (vconcatL p s).
Notation "s ^h$" := (hinverse _ _ s).
Notation "s ^v$" := (vinverse _ _ s).
