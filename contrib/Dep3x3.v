Require Import Basics.

  (*--------------------------
   |       f0i       f0j      |
   |  A00 <---- A01 ----> A02 |
   |   ^         ^         ^  |
   |fi0|      fi1|      fi2|  |
   |   |   f1i   |   f1j   |  |
   |  A10 <---- A11 ----> A12 |
   |   |         |         |  |
   |fj0|      fj1|      fj2|  |
   |   V   f2i   V   f2j   V  |
   |  A20 <---- A21 ----> A22 |
    --------------------------*)

Record Old3x3 := {
  A00 : Type; A01 : Type; A02 : Type;
  A10 : Type; A11 : Type; A12 : Type;
  A20 : Type; A21 : Type; A22 : Type;
  f0i : A01 -> A00; f0j : A01 -> A02;
  fi0 : A10 -> A00; fi1 : A11 -> A01; fi2 : A12 -> A02;
  f1i : A11 -> A10; f1j : A11 -> A12;
  fj0 : A10 -> A20; fj1 : A11 -> A21; fj2 : A12 -> A22;
  f2i : A21 -> A20; f2j : A21 -> A22;
}.

Record Dep3x3 := {
  B00 : Type; B01 : Type;
  B10 : Type; B11 : Type;
  B0x : B00 -> B01 -> Type;
  B1x : B10 -> B11 -> Type;
  Bx0 : B00 -> B10 -> Type;
  Bx1 : B01 -> B11 -> Type;
  Bxx : forall b00 b11 b01 b10, B0x b00 b01 ->
    B1x b10 b11 -> Bx0 b00 b10 -> Bx1 b01 b11 -> Type;
}.

Definition Dep3x3_to_Old3x3 : Dep3x3 -> Old3x3.
Proof.
  intro D.
  serapply (Build_Old3x3 _ _ _ _ _ _). (* Don't have a big enough serapply *)
  + exact (B00 D).
  + exact {b00 : B00 D & {b01 : B01 D & B0x D b00 b01}}.
  + exact (B01 D).
  + exact {b00 : B00 D & {b10 : B10 D & Bx0 D b00 b10}}.
  + exact {b00 : B00 D & 
          {b11 : B11 D & 
          {b01 : B01 D & 
          {b10 : B10 D &
          {b0x : B0x D b00 b01 & 
          {b1x : B1x D b10 b11 & 
          {bx0 : Bx0 D b00 b10 & 
          {bx1 : Bx1 D b01 b11 &
           Bxx D b00 b11 b01 b10 b0x b1x bx0 bx1
          }}}}}}}}.
  + exact {b01 : B01 D & {b11 : B11 D & Bx1 D b01 b11}}.
  + exact (B10 D).
  + exact {b10 : B10 D & {b11 : B11 D & B1x D b10 b11}}.
  + exact (B11 D).
  + intro X; exact X.1.
  + intro X; exact X.2.1.
  + intro X; exact X.1.
  + intro X; exact (X.1 ; X.2.2.1 ; X.2.2.2.2.1).
  + intro X; exact X.1.
  + intro X; exact (X.1 ; X.2.2.2.1 ; X.2.2.2.2.2.2.1).
  + intro X; exact (X.2.2.1 ; X.2.1 ; X.2.2.2.2.2.2.2.1).
  + intro X; exact X.2.1.
  + intro X; exact (X.2.2.2.1 ; X.2.1 ; X.2.2.2.2.2.1).
  + intro X; exact X.2.1.
  + intro X; exact X.1.
  + intro X; exact X.2.1.
Defined.

Definition Old3x3_to_Dep3x3 : Old3x3 -> Dep3x3.
Proof.
  intro E.
  serapply (Build_Dep3x3 (A00 E) (A02 E) (A20 E) (A22 E)).
  + intros a00 a02;
    exact {x : A01 E & (f0i E x = a00) * (f0j E x = a02)}.
  + intros a20 a22;
    exact {x : A21 E & (f2i E x = a20) * (f2j E x = a22)}.
  + intros a00 a20;
    exact {x : A10 E & (fi0 E x = a00) * (fj0 E x = a20)}.
  + intros a02 a22;
    exact {x : A12 E & (fi2 E x = a02) * (fj2 E x = a22)}.
  + intros b00 b11 b01 b10 [a01 _] [a21 _] [a10 _] [a12 _].
    exact {x : A11 E &
      (fi1 E x = a01) * (fj1 E x = a21) * (f1i E x = a10) * (f1j E x = a12)}.
Defined.

Require Import HIT.Pushout.

Definition pushout_rows_coloumns : Old3x3 -> Type.
Proof.
  intros [
    A00 A01 A02
    A10 A11 A12
    A20 A21 A22
    f0i f0j
    fi0 fi1 fi2 f1i
    f1j fj0 fj1
    fj2 f2i f2j].
  set (R0 := pushout f0i f0j).
  set (R1 := pushout f1i f1j).
  set (R2 := pushout f2i f2j).
  serapply (@pushout R1 R0 R2).
  { serapply pushout_rec.
    + apply (pushl o fi0).
    + apply (pushr o fi2).
    + intro; cbn.
      apply pp.
  





