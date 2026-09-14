From HoTT Require Import Basics Types.Paths.

Local Open Scope path_scope.

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

Section InverseCube.
  Universe u.
  Context {A : Type@{u}}.

  Check (@concat_pV_cube_unit_inverse@{u} A).
  Example inverse_cube_refl (x : A)
    : concat_pV_cube_unit_inverse (idpath x) 1 1 1 1 = 1 := idpath.
End InverseCube.

Section DependentNaturality.
  Universes u v.
  Context {A : Type@{u}} {B : A -> Type@{v}} (f g : forall x, B x).

  Example dependent_naturality_square {x y : A} (p : x = y)
    (h : f x = g x) (k : f y = g y)
    : (ap (transport B p) h @ apD g p = apD f p @ k)
      <~> (transport (fun z => f z = g z) p h = k)
    := dpath_path_FlFr_D@{u v} f g p h k.
  Example dependent_naturality_refl (x : A)
    : dpath_path_FlFr_D f f (idpath x) 1 1 1 = 1 := idpath.
End DependentNaturality.

Section PastingComparison.
  Universe u.
  Context {T : Type@{u}} {x0 x1 y0 y1 z0 z1 v0 v1 : T}
    (p : x0 = y0) (q : x1 = y1) (r : x0 = z0) (s : x1 = z1)
    (a : y0 = v0) (b : y1 = v0) (c : z0 = v1) (d : z1 = v1).

  Example different_centers
    : ((p @ a) @ (q @ b)^ = (r @ c) @ (s @ d)^)
      <~> ((p^ @ r) @ c = a @ ((b^ @ (q^ @ s)) @ d))
    := equiv_pasting_zigzags@{u} p q r s a b c d.
  Example pasting_roundtrip
    (h : (p @ a) @ (q @ b)^ = (r @ c) @ (s @ d)^)
    : different_centers^-1 (different_centers h) = h
    := eissect different_centers h.
End PastingComparison.
