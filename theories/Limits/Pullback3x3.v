Require Import Basics.
Require Import Types.
Require Import Limits.Pullback.

(** 3x3 lemma for pullbacks *)

Section Pullback3x3.

  Context
    (A00 A02 A04 A20 A22 A24 A40 A42 A44 : Type)
    (f01 : A00 -> A02) (f03 : A04 -> A02)
    (f10 : A00 -> A20) (f12 : A02 -> A22) (f14 : A04 -> A24)
    (f21 : A20 -> A22) (f23 : A24 -> A22)
    (f30 : A40 -> A20) (f32 : A42 -> A22) (f34 : A44 -> A24)
    (f41 : A40 -> A42) (f43 : A44 -> A42)
    (H11 : f12 o f01 == f21 o f10) (H13 : f12 o f03 == f23 o f14)
    (H31 : f32 o f41 == f21 o f30) (H33 : f32 o f43 == f23 o f34).

  Local Definition AX0 := Pullback f10 f30.
  Local Definition AX2 := Pullback f12 f32.
  Local Definition AX4 := Pullback f14 f34.

  Local Definition fX1
    := functor_pullback f10 f30 f12 f32 f21 f01 f41 H11 H31.

  Local Definition fX3
    := functor_pullback f14 f34 f12 f32 f23 f03 f43 H13 H33.

  Local Definition AXO := Pullback fX1 fX3.

  Local Definition A0X := Pullback f01 f03.
  Local Definition A2X := Pullback f21 f23.
  Local Definition A4X := Pullback f41 f43.

  Local Definition f1X
    := functor_pullback f01 f03 f21 f23 f12 f10 f14
      (symmetry _ _ H11) (symmetry _ _ H13).

  Local Definition f3X
    := functor_pullback f41 f43 f21 f23 f32 f30 f34
      (symmetry _ _ H31) (symmetry _ _ H33).

  Local Definition AOX := Pullback f1X f3X.

  Theorem pullback3x3 : AXO <~> AOX.
  Proof.
    (** Pullbacks commute with sigmas. *)
    (** Pullbacks commute with paths. *)
  Admitted.

End Pullback3x3.



