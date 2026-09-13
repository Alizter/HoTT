From HoTT Require Import Basics Types.Paths.

(** The source of transport and the target path type may live in independent universes. No extensionality hypothesis is present. *)
Section NaturalityUniverses.
  Universe u v.
  Context {A : Type@{u}} {B : Type@{v}}.

  Check (@equiv_naturality_transport2@{u v} A B).
  Check (@transport_translation_comparison@{u v} A B).
  Check (@transport_naturality_square@{u v} A B).
  Check (@transport_naturality_square_beta@{u v} A B).
End NaturalityUniverses.

(** Turns allow independent source, intermediate, and target universes. *)
Section TurnUniverses.
  Universe u v w.
  Context {A : Type@{u}} {B : Type@{v}} {C : Type@{w}}.
  Context (f : A -> B) (g : B -> C).

  Check (@turn_filler@{u v} A B f).
  Check (@turn_filler_beta@{u v} A B f).
  Check (@turn_filler_map@{u v w} A B C f g).

  Example turn_unit (x : A)
    : turn_filler f (idpath x) 1 1 1
        (p':=1) (q':=1) (r':=1) (s':=1) 1 1 1 1 1 = 1
    := idpath.
End TurnUniverses.
