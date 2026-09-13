From HoTT Require Import Basics.
From HoTT Require Import Homotopy.Join.Core Homotopy.Join.MapCoherence.

Local Open Scope path_scope.
Module J := JoinMapCoherence.

Section Composite.
  Universe u v.
  Context {A : Type@{u}} {B : Type@{v}}
    (f t l : A -> A) (g u' r : B -> B)
    (el : forall a, l a = t (f a)) (er : forall b, r b = u' (g b)).

  Example split_l (a : A)
    : J.split f t l g u' r el er (joinl a) = ap joinl (el a)
    := idpath.
  Example split_r (b : B)
    : J.split f t l g u' r el er (joinr b) = ap joinr (er b)
    := idpath.
  Example inverse_l (a : A)
    : J.split_inverse f t l g u' r el er (joinl a)
      = (ap_V (joinl (B:=B)) (el a))^
    := idpath.
  Example inverse_r (b : B)
    : J.split_inverse f t l g u' r el er (joinr b)
      = (ap_V (joinr (A:=A)) (er b))^
    := idpath.

  Context `{Funext} (a0 : A) (b0 : B) (w : B -> B) (d : w == u')
    (pl : forall a, t (f a) = l a) (pr : forall b, w (g b) = r b)
    (cl : forall a, (el a)^ = pl a)
    (cr : forall b, d (g b) @ (er b)^ = pr b).

  Check (J.translated_composite_comparison a0 b0 f t l g w u' r
    d el er pl pr cl cr).
End Composite.

Section Turn.
  Universe uA uB.
  Context {A : Type@{uA}} {B : Type@{uB}}
    (f : A -> B) (g : B -> A) (t : A -> A) (u : B -> B)
    (el : forall b, g (u b) = t (g b))
    (er : forall a, f (t a) = u (f a)).

  Example turn_commute_l (a : A)
    : J.turn_commute f g t u el er (joinl a) = ap joinr (er a) := idpath.
  Example turn_commute_r (b : B)
    : J.turn_commute f g t u el er (joinr b) = ap joinl (el b) := idpath.
  Example turn_inverse_l (a : A)
    : J.turn_commute_inverse f g t u el er (joinl a)
      = (ap_V (joinr (A:=A)) (er a))^ := idpath.
  Example turn_inverse_r (b : B)
    : J.turn_commute_inverse f g t u el er (joinr b)
      = (ap_V (joinl (B:=B)) (el b))^ := idpath.

  Context `{Funext} (a0 : A) (b0 : B) (w : B -> B) (d : w == u)
    (pl : forall a, w (f a) = f (t a))
    (pr : forall b, t (g b) = g (w b))
    (cl : forall a, d (f a) @ (er a)^ = pl a)
    (cr : forall b, (el b)^ @ ap g (d b)^ = pr b).

  Example commute_turn_l (a : A)
    : J.commute_turn f g t w pl pr (joinl a) = ap joinr (pl a) := idpath.
  Example commute_turn_r (b : B)
    : J.commute_turn f g t w pl pr (joinr b) = ap joinl (pr b) := idpath.
  Check (J.translation_turn_comparison a0 b0 f g t w u d el er pl pr cl cr).
End Turn.
