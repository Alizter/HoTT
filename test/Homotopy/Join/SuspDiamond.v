From HoTT Require Import Basics.
From HoTT Require Import Classes.interfaces.canonical_names.
From HoTT Require Import Homotopy.CayleyDickson Homotopy.Join.Core.
From HoTT Require Import Homotopy.Join.SuspDiamond Homotopy.Suspension.

Local Open Scope path_scope.

(** Independent source and target universes, without extensionality or scalar algebra. *)
Section Universes.
  Universe u v.
  Context {A : Type@{u}} {B : Type@{v}} (f : A -> B).

  Check (@join_diamond_turn@{u v} A B f).
  Check (@diamond_susp_turn@{u v u v} A B f).

  Example turn_vertical (a a' b : A)
    : join_diamond_turn f (diamond_v a a' (idpath b))
      = diamond_h (f a) (f a') (idpath (f b))
    := join_diamond_turn_v f a a' b.
  Example turn_horizontal (a b b' : A)
    : join_diamond_turn f (diamond_h b b' (idpath a))
      = diamond_v (f b) (f b') (idpath (f a))
    := join_diamond_turn_h f a b b'.

  Example turn_north
    : diamond_susp_turn f North
      = join_diamond_turn_v (susp_neg B o functor_susp f) South North North
    := idpath.
  Example turn_south
    : diamond_susp_turn f South
      = join_diamond_turn_h (susp_neg B o functor_susp f) South North South
    := idpath.
End Universes.

(** The theorem applies to the actual canonical Cayley-Dickson diamond, not a replacement filler. No laws for the negation of [A] are required. *)
Example canonical_diamond_turn {A : Type} `{Negate A} (t : Susp A)
  : join_diamond_turn (negate_susp A (-)) (cd_diamond_susp t)
    = cd_diamond_susp (negate_susp A (-) t)
  := diamond_susp_turn (-) t.
