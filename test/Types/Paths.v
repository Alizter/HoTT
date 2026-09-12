From HoTT Require Import Basics Types.Paths.

(** The source of transport and the target path type may live in independent universes. No extensionality hypothesis is present. *)
Section NaturalityUniverses.
  Universe u v.
  Context {A : Type@{u}} {B : Type@{v}}.

  Check (@equiv_naturality_transport2@{u v} A B).
  Check (@transport_translation_comparison@{u v} A B).
End NaturalityUniverses.
