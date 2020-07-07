Require Import Basics.
Require Import Types.
Require Import Cubical.DPath.
Require Import Cubical.PathSquare.

Declare Scope dsquare_scope.
Delimit Scope dsquare_scope with dsquare.

Local Open Scope dpath_scope.

(* Dependent squares *)

Definition DPathSquare {A} (P : A -> Type) {a00 a10 a01 a11}
  {px0 : a00 = a10} {px1 : a01 = a11} {p0x p1x}
  (s : PathSquare px0 px1 p0x p1x) {b00 b10 b01 b11}
  (qx0 : DPath P px0 b00 b10) (qx1 : DPath P px1 b01 b11)
  (q0x : DPath P p0x b00 b01) (q1x : DPath P p1x b10 b11) : Type.
Proof.
  destruct s.
  exact (PathSquare qx0 qx1 q0x q1x).
Defined.

Definition ds_id {A} {P : A -> Type} {a00 b00}
  : DPathSquare P sq_id 1 1 1 1 (a00:=a00) (b00:=b00).
Proof.
  apply sq_id.
Defined.

Notation "1" := ds_id : dsquare_scope.

Section DPathSquareConstructors.

  (* Different ways of constructing dependent squares *)

  Context {A} {a0 a1 : A} {p : a0 = a1} {P : A -> Type}
    {b0 b1} (dp : DPath P p b0 b1).

  Definition ds_refl_h : DPathSquare P (sq_refl_h _) dp dp 1 1.
  Proof.
    destruct p.
    apply sq_refl_h.
  Defined.

  Definition ds_refl_v : DPathSquare P (sq_refl_v _) 1 1 dp dp.
  Proof.
    destruct p.
    apply sq_refl_v.
  Defined.

End DPathSquareConstructors.

(* DPathSquares can be given by 2-dimensional DPaths *)
Definition equiv_ds_dpath {A} (P : A -> Type) {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11}
  {p0x : a00 = a01} {p1x : a10 = a11}
  (s : px0 @ p1x = p0x @ px1) {b00 b10 b01 b11}
  {qx0 : DPath P px0 b00 b10} {qx1 : DPath P px1 b01 b11}
  {q0x : DPath P p0x b00 b01} {q1x : DPath P p1x b10 b11}
  : DPath (fun p => DPath P p b00 b11) s (qx0 @D q1x) (q0x @D qx1)
    <~> DPathSquare P (sq_path s) qx0 qx1 q0x q1x.
Proof.
  set (s' := sq_path s).
  rewrite <- (eissect sq_path s : sq_path^-1 s' = s).
  clearbody s'; clear s.
  destruct s'; cbn.
  apply sq_path.
Defined.

Notation ds_dpath := equiv_ds_dpath.

(* We have an apD for DPathSquares *)
Definition ds_apD {A} {B : A -> Type} (f : forall a, B a) {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11} {p0x p1x} (s : PathSquare px0 px1 p0x p1x)
  : DPathSquare B s (dp_apD f px0) (dp_apD f px1) (dp_apD f p0x) (dp_apD f p1x).
Proof.
  by destruct s.
Defined.

(* A DPathSquare over a constant family is given by just a square *)
Definition ds_const {A P : Type} {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11} {p0x : a00 = a01} {p1x : a10 = a11}
  {s : PathSquare px0 px1 p0x p1x} {b00 b10 b01 b11 : P}
  {qx0 : b00 = b10} {qx1 : b01 = b11} {q0x : b00 = b01} {q1x : b10 = b11}
  : PathSquare qx0 qx1 q0x q1x <~> DPathSquare (fun _ => P) s (dp_const qx0)
      (dp_const qx1) (dp_const q0x) (dp_const q1x).
Proof.
  by destruct s.
Defined.

(* Sometimes we want the DPathSquare to be typed differently *)
(* This could be achieved with some clever rewriting of squares and DPathSquares *)
(* It seems that writing it like this might get in the way, Cube.v has
   some examples of this. *)
Definition equiv_ds_const' {A P : Type} {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11} {p0x : a00 = a01} {p1x : a10 = a11}
  {s : PathSquare px0 px1 p0x p1x} {b00 b10 b01 b11 : P}
  {qx0 : DPath (fun _ => P) px0 b00 b10}
  {qx1 : DPath (fun _ => P) px1 b01 b11}
  {q0x : DPath (fun _ => P) p0x b00 b01}
  {q1x : DPath (fun _ => P) p1x b10 b11}
  : PathSquare (dp_const^-1 qx0) (dp_const^-1 qx1)
    (dp_const^-1 q0x) (dp_const^-1 q1x)
    <~> DPathSquare (fun _ => P) s qx0 qx1 q0x q1x.
Proof.
  by destruct s.
Defined.

Notation ds_const' := equiv_ds_const'.

(* dp_apD fits into a natural square *)
Definition dp_apD_nat {A} {P : A -> Type} {f g : forall x, P x} {x y : A}
  (q : f == g) (p : x = y)
  : DPathSquare P (sq_refl_h _) (dp_apD f p) (dp_apD g p) (q x) (q y).
Proof.
  destruct p.
  by apply sq_1G.
Defined.

Definition equiv_ds_G1 {A} (P : A -> Type) {a00 a10}
  {px0 px1 : a00 = a10} {p : px0 = px1} {b00 b10}
  (qx0 : DPath P px0 b00 b10) (qx1 : DPath P px1 b00 b10)
  : DPath (fun x => DPath P x b00 b10) p qx0 qx1
      <~> DPathSquare P (sq_G1 p) qx0 qx1 1 1.
Proof.
  destruct p, px0.
  apply sq_G1.
Defined.

Notation ds_G1 := equiv_ds_G1.

Definition equiv_ds_1G {A} (P : A -> Type) {a00 a01}
  {p0x p1x : a00 = a01} {p : p0x = p1x} {b00 b01}
  (q0x : DPath P p0x b00 b01) (q1x : DPath P p1x b00 b01)
  : DPath (fun x => DPath P x b00 b01) p q0x q1x
      <~> DPathSquare P (sq_1G p) 1 1 q0x q1x.
Proof.
  destruct p, p0x.
  apply sq_1G.
Defined.

Notation ds_1G := equiv_ds_1G.

(** A DPath in a path-type is naturally a DPathSquare.  *)

Definition equiv_ds_dp {A : Type} {B : A -> Type} (f g : forall a : A, B a)
  {x1 x2 : A} (p : x1 = x2) (q1 : f x1 = g x1) (q2 : f x2 = g x2)
  : DPath (fun x : A => f x = g x) p q1 q2
    <~> DPathSquare B (sq_refl_h p) (dp_apD f p) (dp_apD g p) q1 q2.
Proof.
  destruct p.
  exact sq_1G.
Defined.

Notation ds_dp := equiv_ds_dp.

(** DPath's over DPath's become DSquares *)
Definition equiv_ds_nat_dp_dp {A B : Type} {C : B -> Type}
  {a1 a2 : A} {p : a1 = a2} {f g : A -> B}
  {l : forall a, C (f a)} {r : forall a, C (g a)}
  {k : forall a, f a = g a}
  (q1 : DPath C (k a1) (l a1) (r a1))
  (q2 : DPath C (k a2) (l a2) (r a2))
  : DPath (fun a : A => DPath C (k a) (l a) (r a)) p q1 q2
    <~> DPathSquare C (ap_nat k p)
      (dp_compose _ _ _ (dp_apD l p)) (dp_compose _ _ _ (dp_apD r p)) q1 q2.
Proof.
  destruct p.
  exact (ds_1G C (p:=idpath) q1 q2).
Defined.

(** dp_apD fits into a (degenerate) DPathSquare relating it to dp_const applied to ap *)
(** Note that this is oriented differently to dp_apD_const. *)
Definition dp_apD_const_ds {A B : Type} (f : A -> B) {x y : A} (p : x = y)
  : DPathSquare _ (sq_refl_h p) (dp_const (ap f p)) (dp_apD f p) 1 1.
Proof.
  by destruct p.
Defined.

(** Dependent Kan operations *)

Section Kan.

  Context {A : Type} {P : A -> Type} {a00 a10 a01 a11 : A}
          {px0 : a00 = a10} {px1 : a01 = a11} {p0x p1x}
          (s : PathSquare px0 px1 p0x p1x)
          {b00 : P a00} {b10 : P a10} {b01 : P a01} {b11 : P a11}.

  Definition ds_fill_l (qx1 : DPath P px1 b01 b11)
             (q0x : DPath P p0x b00 b01) (q1x : DPath P p1x b10 b11)
    : {qx0 : DPath P px0 b00 b10 & DPathSquare P s qx0 qx1 q0x q1x}.
  Proof.
    destruct s; apply sq_fill_l.
  Defined.

  Definition ds_fill_l_uniq {qx1 : DPath P px1 b01 b11}
             {q0x : DPath P p0x b00 b01} {q1x : DPath P p1x b10 b11}
             {qx0 : DPath P px0 b00 b10}
             (t : DPathSquare P s qx0 qx1 q0x q1x)
             {qx0' : DPath P px0 b00 b10}
             (t' : DPathSquare P s qx0' qx1 q0x q1x)
    : qx0 = qx0'.
  Proof.
    destruct s.
    exact (sq_fill_l_uniq t t').
  Defined.

  Definition ds_fill_r (qx0 : DPath P px0 b00 b10)
             (q0x : DPath P p0x b00 b01) (q1x : DPath P p1x b10 b11)
    : {qx1 : DPath P px1 b01 b11 & DPathSquare P s qx0 qx1 q0x q1x}.
  Proof.
    destruct s; apply sq_fill_r.
  Defined.

  Definition ds_fill_r_uniq {qx0 : DPath P px0 b00 b10}
             {q0x : DPath P p0x b00 b01} {q1x : DPath P p1x b10 b11}
             {qx1 : DPath P px1 b01 b11}
             (t : DPathSquare P s qx0 qx1 q0x q1x)
             {qx1' : DPath P px1 b01 b11}
             (t' : DPathSquare P s qx0 qx1' q0x q1x)
    : qx1 = qx1'.
  Proof.
    destruct s.
    exact (sq_fill_r_uniq t t').
  Defined.

  Definition equiv_ds_fill_lr
             {q0x : DPath P p0x b00 b01} {q1x : DPath P p1x b10 b11}
    : (DPath P px0 b00 b10) <~> (DPath P px1 b01 b11).
  Proof.
    srapply equiv_adjointify.
    - intros qx0; exact (ds_fill_r qx0 q0x q1x).1.
    - intros qx1; exact (ds_fill_l qx1 q0x q1x).1.
    - intros qx1.
      exact (ds_fill_r_uniq (ds_fill_r _ q0x q1x).2
                            (ds_fill_l qx1 q0x q1x).2).
    - intros qx0.
      exact (ds_fill_l_uniq (ds_fill_l _ q0x q1x).2
                            (ds_fill_r qx0 q0x q1x).2).
  Defined.

  Definition ds_fill_t (qx0 : DPath P px0 b00 b10)
             (qx1 : DPath P px1 b01 b11) (q1x : DPath P p1x b10 b11)
    : {q0x : DPath P p0x b00 b01 & DPathSquare P s qx0 qx1 q0x q1x}.
  Proof.
    destruct s; apply sq_fill_t.
  Defined.

  Definition ds_fill_b (qx0 : DPath P px0 b00 b10)
             (qx1 : DPath P px1 b01 b11) (q0x : DPath P p0x b00 b01)
    : {q1x : DPath P p1x b10 b11 & DPathSquare P s qx0 qx1 q0x q1x}.
  Proof.
    destruct s; apply sq_fill_b.
  Defined.

End Kan.

(** Another equivalent formulation of a dependent square over reflexivity *)
Definition equiv_ds_transport_dpath {A} {a0 a1 : A} {p : a0 = a1}
           {P : A -> Type} {b00 b10 b01 b11}
           (qx0 : DPath P p b00 b10) (qx1 : DPath P p b01 b11)
           (q0x : b00 = b01) (q1x : b10 = b11)
  : DPathSquare P (sq_refl_h p) qx0 qx1 q0x q1x
    <~> transport (fun y => DPath P p y b11) q0x
          (transport (fun y => DPath P p b00 y) q1x
                     qx0) = qx1.
Proof.
  destruct p; cbn.
  refine (_ oE sq_path^-1).
  refine (equiv_concat_l _ _ oE _).
  { apply transport_paths_l. }
  refine (equiv_moveR_Vp _ _ _ oE _).
  refine (equiv_concat_l _ _).
  apply transport_paths_r.
Defined.

Notation ds_transport_dpath := equiv_ds_transport_dpath.

(** Dependent square concatenation *)
Section DPathSquareConcat.

  Context {A : Type} {P : A -> Type} {a00 a10 a01 a11 : A}
    {px0 : a00 = a10} {px1 : a01 = a11}
    {p0x : a00 = a01} {p1x : a10 = a11}
    {s : PathSquare px0 px1 p0x p1x} {b00 b10 b01 b11}
    {qx0 : DPath P px0 b00 b10} {qx1 : DPath P px1 b01 b11}
    {q0x : DPath P p0x b00 b01} {q1x : DPath P p1x b10 b11}.

  (* Horizontal concatenation of dependent squares *)
  Definition ds_concat_h  {a02 a12 : A} {b02 b12}
    {p0y : a01 = a02} {p1y : a11 = a12} {px2 : a02 = a12}
    {q0y : DPath P p0y b01 b02} {q1y : DPath P p1y b11 b12}
    {qx2 : DPath P px2 b02 b12} {t : PathSquare px1 px2 p0y p1y}
    : DPathSquare P s qx0 qx1 q0x q1x
      -> DPathSquare P t qx1 qx2 q0y q1y
      -> DPathSquare P (sq_concat_h s t) qx0 qx2 (q0x @D q0y) (q1x @D q1y).
  Proof.
    intros a b.
    destruct t, b, p0x, p1x, q0x, q1x.
    assumption.
  Defined.

  (* Vertical concatenation of dependent squares *)
  Definition ds_concat_v {a20 a21 : A} {b20 b21}
    {py0 : a10 = a20} {py1 : a11 = a21} {p2x : a20 = a21}
    {qy0 : DPath P py0 b10 b20} {qy1 : DPath P py1 b11 b21}
    {q2x : DPath P p2x b20 b21} {t : PathSquare py0 py1 p1x p2x}
    : DPathSquare P s qx0 qx1 q0x q1x
      -> DPathSquare P t qy0 qy1 q1x q2x
      -> DPathSquare P (sq_concat_v s t) (qx0 @D qy0) (qx1 @D qy1) q0x q2x.
  Proof.
    intros a b.
    destruct t, b, px0, px1, qx0, qx1.
    assumption.
  Defined.

End DPathSquareConcat.

(* Lemmas for rewriting sides of dependent squares along DPaths. *)
Section DPathSquareRewriting.

  Universe i.

  Context {A : Type@{i}} {P : A -> Type@{i}} 
    {a00 a10 a01 a11 : A}
    {px0 : a00 = a10} {px1 : a01 = a11}
    {p0x : a00 = a01} {p1x : a10 = a11}
    {s : PathSquare px0 px1 p0x p1x} {b00 b10 b01 b11}
    {qx0 : DPath P px0 b00 b10} {qx1 : DPath P px1 b01 b11}
    {q0x : DPath P p0x b00 b01} {q1x : DPath P p1x b10 b11}.

  Definition equiv_ds_GGGG@{}
    {px0' : a00 = a10} {px1' : a01 = a11}
    {p0x' : a00 = a01} {p1x' : a10 = a11}
    {rx0 : px0 = px0'}
    {rx1 : px1 = px1'}
    {r0x : p0x = p0x'}
    {r1x : p1x = p1x'}
    {qx0' : DPath P px0' b00 b10}
    {qx1' : DPath P px1' b01 b11}
    {q0x' : DPath P p0x' b00 b01}
    {q1x' : DPath P p1x' b10 b11}
    (dx0 : DPath (fun x => DPath P x b00 b10) rx0 qx0 qx0')
    (dx1 : DPath (fun x => DPath P x b01 b11) rx1 qx1 qx1')
    (d0x : DPath (fun x => DPath P x b00 b01) r0x q0x q0x')
    (d1x : DPath (fun x => DPath P x b10 b11) r1x q1x q1x')
    : DPathSquare P s qx0 qx1 q0x q1x
    <~> DPathSquare P (sq_GGGG rx0 rx1 r0x r1x s) qx0' qx1' q0x' q1x'.
  Proof.
    destruct s, rx0, rx1, r0x, r1x.
    by apply sq_GGGG.
  Defined.

  Context
    {px0' : a00 = a10} {px1' : a01 = a11}
    {p0x' : a00 = a01} {p1x' : a10 = a11}
    {rx0 : px0 = px0'}
    {rx1 : px1 = px1'}
    {r0x : p0x = p0x'}
    {r1x : p1x = p1x'}
    {qx0' : DPath P px0' b00 b10}
    {qx1' : DPath P px1' b01 b11}
    {q0x' : DPath P p0x' b00 b01}
    {q1x' : DPath P p1x' b10 b11}
    (dx0 : DPath (fun x => DPath P x b00 b10) rx0 qx0 qx0')
    (dx1 : DPath (fun x => DPath P x b01 b11) rx1 qx1 qx1')
    (d0x : DPath (fun x => DPath P x b00 b01) r0x q0x q0x')
    (d1x : DPath (fun x => DPath P x b10 b11) r1x q1x q1x').

  Definition equiv_ds_Gccc := equiv_ds_GGGG dx0 1 1 1.
  Definition equiv_ds_cGcc := equiv_ds_GGGG 1 dx1 1 1.
  Definition equiv_ds_ccGc := equiv_ds_GGGG 1 1 d0x 1.
  Definition equiv_ds_cccG := equiv_ds_GGGG 1 1 1 d1x.
  Definition equiv_ds_GGcc := equiv_ds_GGGG dx0 dx1 1 1.
  Definition equiv_ds_GcGc := equiv_ds_GGGG dx0 1 d0x 1.
  Definition equiv_ds_GccG := equiv_ds_GGGG dx0 1 1 d1x.
  Definition equiv_ds_cGGc := equiv_ds_GGGG 1 dx1 d0x 1.
  Definition equiv_ds_cGcG := equiv_ds_GGGG 1 dx1 1 d1x.
  Definition equiv_ds_ccGG := equiv_ds_GGGG 1 1 d0x d1x.
  Definition equiv_ds_GGGc := equiv_ds_GGGG dx0 dx1 d0x 1.
  Definition equiv_ds_cGGG := equiv_ds_GGGG 1 dx1 d0x d1x.

End DPathSquareRewriting.

Notation ds_GGGG := equiv_ds_GGGG.
Notation ds_Gccc := equiv_ds_Gccc.
Notation ds_cGcc := equiv_ds_cGcc.
Notation ds_ccGc := equiv_ds_ccGc.
Notation ds_cccG := equiv_ds_cccG.
Notation ds_GGcc := equiv_ds_GGcc.
Notation ds_GcGc := equiv_ds_GcGc.
Notation ds_GccG := equiv_ds_GccG.
Notation ds_cGGc := equiv_ds_cGGc.
Notation ds_cGcG := equiv_ds_cGcG.
Notation ds_ccGG := equiv_ds_ccGG.
Notation ds_GGGc := equiv_ds_GGGc.
Notation ds_cGGG := equiv_ds_cGGG.

