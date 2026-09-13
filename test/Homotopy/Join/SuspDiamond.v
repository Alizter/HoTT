From HoTT Require Import Basics Types.Paths Types.Prod.
From HoTT Require Import Classes.interfaces.canonical_names.
From HoTT Require Import Homotopy.CayleyDickson Homotopy.Join.Core.
From HoTT Require Import Homotopy.Join.SuspDiamond Homotopy.Suspension.

Local Open Scope path_scope.

(** Independent source and target universes, without extensionality or scalar algebra. *)
Section Universes.
  Universe u v.
  Context {A : Type@{u}} {B : Type@{v}} (f : A -> B).

  Check (@join_diamond_turn@{u u v v v u} A A B B f f).
  Check (@diamond_susp_turn@{u v u v} A B f).

  Example turn_vertical (a a' b : A)
    : join_diamond_turn f f (diamond_v a a' (idpath b))
      = diamond_h (f a) (f a') (idpath (f b))
    := join_diamond_turn_v f f a a' b.
  Example turn_horizontal (a b b' : A)
    : join_diamond_turn f f (diamond_h b b' (idpath a))
      = diamond_v (f b) (f b') (idpath (f a))
    := join_diamond_turn_h f f a b b'.

  Example turn_north
    : diamond_susp_turn f North
      = join_diamond_turn_v (susp_neg B o functor_susp f)
          (susp_neg B o functor_susp f) South North North
    := idpath.
  Example turn_south
    : diamond_susp_turn f South
      = join_diamond_turn_h (susp_neg B o functor_susp f)
          (susp_neg B o functor_susp f) South North South
    := idpath.
End Universes.

(** The two scalar maps of a turn need not have the same domain or codomain. No ordering between the four universes is imposed. *)
Section GeneralTurns.
  Universe u v w z s t.
  Constraint u <= s.
  Constraint v <= s.
  Constraint w <= t.
  Constraint z <= t.
  Context {A : Type@{u}} {B : Type@{v}} {C : Type@{w}} {D : Type@{z}}.
  Context (f : A -> D) (g : B -> C).

  Check (@join_turn@{u v w z s t} A B C D f g).
  Check (@join_diamond_turn@{u v w z t s} A B C D f g).

  Example turn_left (a : A) : join_turn f g (joinl a) = joinr (f a) := 1.
  Example turn_right (b : B) : join_turn f g (joinr b) = joinl (g b) := 1.
  Example turn_glue (a : A) : forall b,
    ap (join_turn f g) (jglue a b) = (jglue (g b) (f a))^
    := fun b => Join_rec_beta_jglue _ _ _ a b.
End GeneralTurns.

Section TurnComposition.
  Universe uA uB uC uD uE uF.
  Context {A : Type@{uA}} {B : Type@{uB}} {C : Type@{uC}}
    {D : Type@{uD}} {E : Type@{uE}} {F : Type@{uF}}.
  Context (f : A -> C) (g : B -> D) (k : C -> F) (l : D -> E).

  (** Arbitrary chosen boundaries survive mapping and turning in either order. *)
  Example turn_after_map {a a' : A} {b b' : B} {c c' : C} {d d' : D}
    (p : f a = c) (q : f a' = c') (r : g b = d) (s : g b' = d')
    (h : zigzag a a' b = zigzag a a' b')
    : join_diamond_turn k l (join_zigzag_filler f g p q r s h)
      = transport011
        (fun x : E * E => fun y : F * F =>
          zigzag (fst x) (snd x) (fst y) = zigzag (fst x) (snd x) (snd y))
        (path_prod' (ap l r) (ap l s)) (path_prod' (ap k p) (ap k q))
        (join_diamond_turn (k o f) (l o g) h)
    := join_diamond_turn_map f g k l p q r s h.

  Example map_after_turn {a a' : A} {b b' : B} {e e' : E} {d d' : F}
    (p : l (g b) = e) (q : l (g b') = e')
    (r : k (f a) = d) (s : k (f a') = d')
    (h : zigzag a a' b = zigzag a a' b')
    : join_zigzag_filler l k p q r s (join_diamond_turn f g h)
      = transport011
        (fun x : E * E => fun y : F * F =>
          zigzag (fst x) (snd x) (fst y) = zigzag (fst x) (snd x) (snd y))
        (path_prod' p q) (path_prod' r s)
        (join_diamond_turn (k o f) (l o g) h)
    := join_diamond_map_turn f g l k p q r s h.
End TurnComposition.

(** The theorem applies to the actual canonical Cayley-Dickson diamond, not a replacement filler. No laws for the negation of [A] are required. *)
Example canonical_diamond_turn {A : Type} `{Negate A} (t : Susp A)
  : join_diamond_turn (negate_susp A (-)) (negate_susp A (-))
      (cd_diamond_susp t)
    = cd_diamond_susp (negate_susp A (-) t)
  := diamond_susp_turn (-) t.
