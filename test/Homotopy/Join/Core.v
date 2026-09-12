From HoTT Require Import Basics Types.Prod.
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

(** Composition retains arbitrary boundary witnesses and independent source, intermediate, and target join universes. *)
Section ZigzagFillerComposition.
  Universe uA uB uC uD uE uF uS uM uT.
  Constraint uA <= uS.
  Constraint uB <= uS.
  Constraint uC <= uM.
  Constraint uD <= uM.
  Constraint uE <= uT.
  Constraint uF <= uT.
  Context {A : Type@{uA}} {B : Type@{uB}} {C : Type@{uC}}
    {D : Type@{uD}} {E : Type@{uE}} {F : Type@{uF}}.

  Example zigzag_filler_compose_universes
    (f : A -> C) (g : B -> D) (k : C -> E) (l : D -> F)
    {a a' : A} {b b' : B} {c c' : C} {d d' : D}
    (p : f a = c) (q : f a' = c') (r : g b = d) (s : g b' = d')
    (h : zigzag@{uA uB uS} a a' b = zigzag@{uA uB uS} a a' b')
    : join_zigzag_filler@{uC uD uE uF uT uM} k l 1 1 1 1
        (join_zigzag_filler@{uA uB uC uD uM uS} f g p q r s h)
      = join_zigzag_filler@{uA uB uE uF uT uS} (k o f) (l o g)
        (ap k p) (ap k q) (ap l r) (ap l s) h
    := join_zigzag_filler_compose@{uA uB uC uD uE uF uT uM uS}
         f g k l p q r s h.
End ZigzagFillerComposition.

(** Map homotopies and parameter changes need no function extensionality and impose no ordering between the two join universes. Both sets of boundary witnesses are arbitrary. *)
Section ZigzagFillerChange.
  Universe uX uC uD uS uT.
  Constraint uX <= uS.
  Constraint uC <= uT.
  Constraint uD <= uT.
  Context {X : Type@{uX}} {C : Type@{uC}} {D : Type@{uD}} {n e : X}.

  Example zigzag_filler_change_without_funext
    (h : forall t, zigzag@{uX uX uS} n t t = zigzag n t e)
    {f f' : X -> C} {g g' : X -> D} (pf : f == f') (pg : g == g')
    {t t' : X} (p_t : t = t')
    {c c' k k' : C} {d d' l l' : D}
    (p : f n = c) (q : f t = c') (r : g t = d) (s : g e = d')
    (p' : f' n = k) (q' : f' t' = k') (r' : g' t' = l) (s' : g' e = l')
    : transport011
        (fun x : C * C => fun y : D * D =>
          zigzag@{uC uD uT} (fst x) (snd x) (fst y)
            = zigzag (fst x) (snd x) (snd y))
        (path_prod' (p^ @ pf n @ p') (q^ @ (pf t @ ap f' p_t) @ q'))
        (path_prod' (r^ @ (pg t @ ap g' p_t) @ r') (s^ @ pg e @ s'))
        (join_zigzag_filler f g p q r s (h t))
      = join_zigzag_filler f' g' p' q' r' s' (h t')
    := join_zigzag_filler_change@{uX uC uD uS uT}
         h pf pg p_t p q r s p' q' r' s'.
End ZigzagFillerChange.

(** Bypassing the 0-groupoid wrapper changes neither the map nor its chosen glue computation. *)
Example functor_join_recdata_compatibility {A B C D : Type}
  (f : A -> C) (g : B -> D)
  : functor_join f g = join_rec (functor_join_recdata f g) := idpath.

Example functor_join_recdata_beta_compatibility {A B C D : Type}
  (f : A -> C) (g : B -> D) (a : A) (b : B)
  : functor_join_beta_jglue f g a b
    = join_rec_beta_jg (functor_join_recdata f g) a b := idpath.

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
