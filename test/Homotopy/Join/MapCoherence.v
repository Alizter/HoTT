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
