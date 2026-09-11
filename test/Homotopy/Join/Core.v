From HoTT Require Import Basics.
From HoTT Require Import Pointed.Core Homotopy.Join.Core.

Local Open Scope path_scope.

Section ZigzagNaturality.
  Universe u v w.
  Constraint u <= w.
  Constraint v <= w.
  Context {A : Type@{u}} {B : Type@{v}}.

  Example zigzag_natsq_universes
    {a a' c c' : A} {b b' : B}
    (p : a = a') (q : c = c') (r : b = b')
    : ap joinl p @ zigzag@{u v w} a' c' b'
      = zigzag@{u v w} a c b @ ap joinl q
    := zigzag_natsq@{u v w} p q r.

  Example zigzag_natsq_idpath (a c : A) (b : B)
    : zigzag_natsq (idpath a) (idpath c) (idpath b)
      = concat_1p_p1 (zigzag a c b) := idpath.
End ZigzagNaturality.

(** Mapping fillers imposes no ordering between the source and target join universes. *)
Section ZigzagFillers.
  Universe i j k l m n.
  Constraint i <= k.
  Constraint j <= k.
  Constraint l <= n.
  Constraint m <= n.
  Context {A : Type@{i}} {B : Type@{j}} {C : Type@{l}} {D : Type@{m}}.

  Example zigzag_filler_universes (f : A -> C) (g : B -> D)
    {a a' : A} {b b' : B}
    (h : zigzag@{i j k} a a' b = zigzag@{i j k} a a' b')
    : zigzag@{l m n} (f a) (f a') (g b)
      = zigzag@{l m n} (f a) (f a') (g b')
    := join_zigzag_filler@{i j l m n k} f g 1 1 1 1 h.
End ZigzagFillers.

(** The two join factors and the codomain may live in independent universes. *)
Section RectangleHomotopy.
  Universe i j k l.
  Constraint i <= k.
  Constraint j <= k.
  Context {A : pType@{i}} {B : pType@{j}} {Y : Type@{l}}.

  Example rectangle_homotopy_universes (F G : Join@{i j k} A B -> Y)
    (q : F (joinl (point A)) = G (joinl (point A)))
    (h : forall (a : A) (b : B),
      ap F (join_rectangle_loop@{i j k} a b) @ q
        = q @ ap G (join_rectangle_loop@{i j k} a b))
    : F == G
    := Join_homotopy_from_rectangle@{i j l k} F G q h.
End RectangleHomotopy.

(** The diamond twist is a dependent path between equalities of zigzags, without a PathSquare. *)
Example diamond_twist_path {A : Type} {a a' : A} (p : a = a')
  : transport (fun x => zigzag a' x a = zigzag a' x x) p
      (diamond_v a' a 1) = diamond_h a a' 1
  := diamond_twist p.

Example diamond_twist_idpath {A : Type} (a : A)
  : diamond_twist (idpath a) = diamond_symm a a := idpath.

Example diamond_join_left {A B : Type} (n e a : A) (b0 : B)
  : diamond_join n e b0 (joinl a)
    = diamond_h (joinl e) (joinl a) (zigzag n a b0) := idpath.

Example diamond_join_right {A B : Type} (n e : A) (b0 b : B)
  : diamond_join n e b0 (joinr b)
    = diamond_v (joinl n) (joinr b) (jglue e b) := idpath.
