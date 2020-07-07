Require Import Basics Types.
Require Import Cubical.
Require Import HFiber.


(** TODO: move these? *)
Definition sig2 {A B : Type} (C : A -> B -> Type) : Type
  := {a : A & {b : B & C a b}}.

(** We define the total space of this 3x3 family as a record for performance reasons. *)
Record sig44 {A B C D : Type}
  {E : A -> B -> Type} {F : C -> D -> Type}
  {G : A -> C -> Type} {H : B -> D -> Type}
  (I : forall a b c d, E a b -> F c d -> G a c -> H b d -> Type)
  : Type := 
{
  a : A ; b : B ; c : C ; d : D ;
  e : E a b ; f : F c d ; g : G a c ; h : H b d ;
  i : I a b c d e f g h ;
}.

Definition hfiber2 {A B C : Type} (f : A -> B) (g : A -> C)
  : B -> C -> Type
  := fun x y => {z : _ & {_ : f z = x & g z = y}}.

Definition equiv_fibrant_replacement2 {A B C : Type} (f : A -> B) (g : A -> C)
  : A <~> sig2 (hfiber2 f g).
Proof.
  snrapply Build_Equiv.
  { intro a.
    exact (f a; g a; a; idpath; idpath). }
  snrapply Build_IsEquiv.
  { intros [b [c [a [p q]]]].
    exact a. }
  { intros [b [c [a [p q]]]].
    destruct p, q.
    reflexivity. }
  1: hnf; reflexivity.
  reflexivity.
Defined.

Record hfiber44
  {A00 A02 A04 A20 A22 A24 A40 A42 A44 : Type}
  {f01 : A02 -> A00} {f03 : A02 -> A04}
  {f10 : A20 -> A00} {f12 : A22 -> A02} {f14 : A24 -> A04}
  {f21 : A22 -> A20} {f23 : A22 -> A24}
  {f30 : A20 -> A40} {f32 : A22 -> A42} {f34 : A24 -> A44}
  {f41 : A42 -> A40} {f43 : A42 -> A44}
  (H11 : f01 o f12 == f10 o f21) (H13 : f03 o f12 == f14 o f23)
  (H31 : f41 o f32 == f30 o f21) (H33 : f43 o f32 == f34 o f23)
  b00 b04 b40 b44
  (h0103 : hfiber2 f01 f03 b00 b04)
  (h4143 : hfiber2 f41 f43 b40 b44)
  (h1030 : hfiber2 f10 f30 b00 b40)
  (h1434 : hfiber2 f14 f34 b04 b44) : Type :=
{
  a22 : A22 ;
  p12 : f12 a22 = h0103.1 ;
  p32 : f32 a22 = h4143.1 ;
  p21 : f21 a22 = h1030.1 ;
  p23 : f23 a22 = h1434.1 ;
  s11 : PathSquare (H11 a22) (h0103.2.1 @ h1030.2.1^) (ap _ p12) (ap _ p21) ;
  s13 : PathSquare (H13 a22) (h0103.2.2 @ h1434.2.1^) (ap _ p12) (ap _ p23) ;
  s31 : PathSquare (H31 a22) (h4143.2.1 @ h1030.2.2^) (ap _ p32) (ap _ p21) ;
  s33 : PathSquare (H33 a22) (h4143.2.2 @ h1434.2.2^) (ap _ p32) (ap _ p23) ;
}.

Definition equiv_fibrant_replacement44
  {A00 A02 A04 A20 A22 A24 A40 A42 A44 : Type}
  {f01 : A02 -> A00} {f03 : A02 -> A04}
  {f10 : A20 -> A00} {f12 : A22 -> A02} {f14 : A24 -> A04}
  {f21 : A22 -> A20} {f23 : A22 -> A24}
  {f30 : A20 -> A40} {f32 : A22 -> A42} {f34 : A24 -> A44}
  {f41 : A42 -> A40} {f43 : A42 -> A44}
  (H11 : f01 o f12 == f10 o f21) (H13 : f03 o f12 == f14 o f23)
  (H31 : f41 o f32 == f30 o f21) (H33 : f43 o f32 == f34 o f23)
  : A22 <~> sig44 (hfiber44 H11 H13 H31 H33).
Proof.
  snrapply Build_Equiv.
  { intro x.
    snrapply Build_sig44.
    1: exact (f10 (f21 x)).
    1: exact (f14 (f23 x)).
    1: exact (f30 (f21 x)).
    1: exact (f34 (f23 x)).
    1-4: (repeat snrapply (_;_)); hnf; trivial.
    unshelve econstructor; trivial.
    all: apply sq_path.
    all: simpl.
    all: symmetry; apply concat_1p. }
  snrapply Build_IsEquiv.
  { intro x.
    rapply a22.
    rapply i.
    exact x. }
  { intro x; cbn.
    destruct x as [a00 a04 a40 a44 [a02 [p01 p03]] h2 h3 h4 []]; simpl.
    
  intros [a00 [a04 [a40 [a44
      [[a02 [p01 p03]] [[a42 [p41 p43]]
      [[a20 [p10 p30]] [[a24 [p14 p34]]
      [a22 [p12 [p32 [p21 [p23 [[[s11 s13] s31] s33]]]]]]]]]]]]]].
    cbv zeta.
    destruct p10, p21.
    srapply path_sigma; [reflexivity | unfold transport, pr2].
    destruct p14, p23.
    srapply path_sigma; [reflexivity | unfold transport, pr2].
    
    destruct p23, p32, p21, p12.
    destruct p34, p14, p30, p10.
    
    destruct p23, p32, p21, p12; cbn in * |-.
    rewrite <- (eisretr sq_G1 s11).
    rewrite <- (eisretr sq_G1 s13).
    rewrite <- (eisretr sq_G1 s31).
    rewrite <- (eisretr sq_G1 s33).
    set (sq_G1^-1 s11) as t11.
    set (sq_G1^-1 s31) as t31.
    set (sq_G1^-1 s13) as t13.
    set (sq_G1^-1 s33) as t33.
    clearbody t11 t31 t13 t33.
    clear s11 s31 s13 s33.
    rewrite <- (inv_V t11),  <- (inv_V t31),  <- (inv_V t13),  <- (inv_V t33).
    set t11^ as u11.
    set t13^ as u13.
    set t31^ as u31.
    set t33^ as u33.
    clearbody u11 u13 u31 u33.
    clear t11 t13 t31 t33.
    destruct u11.
    
    ., u13, u31, u33.
    
    destruct p23, p32, p21, p12.
    destruct p34, p14, p30, p10.
    
    destruct s11.
    assumption. }
  1
    



Section Replacement.

  Context
    {A00 A02 A04 A20 A22 A24 A40 A42 A44 : Type}
    {f01 : A02 -> A00} {f03 : A02 -> A04}
    {f10 : A20 -> A00} {f12 : A22 -> A02} {f14 : A24 -> A04}
    {f21 : A22 -> A20} {f23 : A22 -> A24}
    {f30 : A20 -> A40} {f32 : A22 -> A42} {f34 : A24 -> A44}
    {f41 : A42 -> A40} {f43 : A42 -> A44}
    {H11 : f01 o f12 == f10 o f21} {H13 : f03 o f12 == f14 o f23}
    {H31 : f41 o f32 == f30 o f21} {H33 : f43 o f32 == f34 o f23}.

  (** A/f is the original diagram.
      B/g is the conversion to dependent families.
      C/h is the total space of B which is equivalent to A *)

  Local Definition B00 : Type := A00.
  Local Definition B04 : Type := A04.
  Local Definition B40 : Type := A40.
  Local Definition B44 : Type := A44.
  Local Definition B02 : B00 -> B04 -> Type := hfiber2 f01 f03.
  Local Definition B42 : B40 -> B44 -> Type := hfiber2 f41 f43.
  Local Definition B20 : B00 -> B40 -> Type := hfiber2 f10 f30.
  Local Definition B24 : B04 -> B44 -> Type := hfiber2 f14 f34.

  Local Definition B22 : forall b00 b44 b04 b40,
    B02 b00 b04 ->
    B42 b40 b44 ->
    B20 b00 b40 ->
    B24 b04 b44 -> Type.
  Proof.
    intros a00 a44 a04 a40
     [a02 [p01 p03]] [a42 [p41 p43]] [a20 [p10 p30]] [a24 [p14 p34]].
    refine {x : A22 & _}.
    refine {p12 : f12 x = a02 & _}.
    refine {p32 : f32 x = a42 & _}.
    refine {p21 : f21 x = a20 & _}.
    refine {p23 : f23 x = a24 & _}.
    refine (_ * _ * _ * _).
    - refine (PathSquare (H11 x) (p01 @ p10^) (ap _ p12) (ap _ p21)).
    - refine (PathSquare (H13 x) (p03 @ p14^) (ap _ p12) (ap _ p23)).
    - refine (PathSquare (H31 x) (p41 @ p30^) (ap _ p32) (ap _ p21)).
    - refine (PathSquare (H33 x) (p43 @ p34^) (ap _ p32) (ap _ p23)).
  Defined.

  Goal Type.
  pose B22.
  unfold B22 in T.

  Local Definition C00 : Type := B00.
  Local Definition C02 : Type := sig2 B02.
  Local Definition C04 : Type := B04.
  Local Definition C20 : Type := sig2 B20.
  Local Definition C22 : Type := sig44 B22.
  Local Definition C24 : Type := sig2 B24.
  Local Definition C40 : Type := B40.
  Local Definition C42 : Type := sig2 B42.
  Local Definition C44 : Type := B44.

  Local Definition h01 : C02 -> C00 := fun x => x.1.
  Local Definition h03 : C02 -> C04 := fun x => x.2.1.
  Local Definition h10 : C20 -> C00 := fun x => x.1.
  Local Definition h12 : C22 -> C02 := fun x => (x.1 ; x.2.2.1 ; x.2.2.2.2.1).
  Local Definition h14 : C24 -> C04 := fun x => x.1.
  Local Definition h21 : C22 -> C20 := fun x => (x.1 ; x.2.2.2.1 ; x.2.2.2.2.2.2.1).
  Local Definition h23 : C22 -> C24 := fun x => (x.2.2.1 ; x.2.1 ; x.2.2.2.2.2.2.2.1).
  Local Definition h30 : C20 -> C40 := fun x => x.2.1.
  Local Definition h32 : C22 -> C42 := fun x => (x.2.2.2.1 ; x.2.1 ; x.2.2.2.2.2.1).
  Local Definition h34 : C24 -> C44 := fun x => x.2.1.
  Local Definition h41 : C42 -> C40 := fun x => x.1.
  Local Definition h43 : C42 -> C44 := fun x => x.2.1.


  Local Definition equiv_A02_C02 : A02 <~> C02 := equiv_fibrant_replacement2 _ _.
  Local Definition equiv_A20_C20 : A20 <~> C20 := equiv_fibrant_replacement2 _ _.
  Local Definition C22 : Type := sig44 B22.
  Local Definition equiv_A24_C24 : A24 <~> C24 := := equiv_fibrant_replacement2 _ _.
  Local Definition equiv_A42_C42 : A42 <~> C42 := := equiv_fibrant_replacement2 _ _.


Record Diagram3x3 : Type := {
  A00 : Type; A02 : Type; A04 : Type;
  A20 : Type; A22 : Type; A24 : Type;
  A40 : Type; A42 : Type; A44 : Type;
  f01 : A02 -> A00; f03 : A02 -> A04;
  f10 : A20 -> A00; f12 : A22 -> A02; f14 : A24 -> A04;
  f21 : A22 -> A20; f23 : A22 -> A24;
  f30 : A20 -> A40; f32 : A22 -> A42; f34 : A24 -> A44;
  f41 : A42 -> A40; f43 : A42 -> A44;
  H11 : f01 o f12 == f10 o f21; H13 : f03 o f12 == f14 o f23;
  H31 : f41 o f32 == f30 o f21; H33 : f43 o f32 == f34 o f23;
}.



Record DepDiagram3x3 := {
  B00 : Type; B04 : Type;
  B40 : Type; B44 : Type;
  B02 : B00 -> B04 -> Type;
  B42 : B40 -> B44 -> Type;
  B20 : B00 -> B40 -> Type;
  B24 : B04 -> B44 -> Type;
  B22 : forall b00 b44 b04 b40,
    B02 b00 b04 ->
    B42 b40 b44 ->
    B20 b00 b40 ->
    B24 b04 b44 -> Type;
}.



(* Here is how to convert between a dependent 3x3 diagram and a regular 3x3 diagram. Note that stepping through this proof is very slow and it may be better to check the whole thing at once. *)
Definition Dep3x3_to_Diagram3x3 : DepDiagram3x3 -> Diagram3x3.
Proof.
  intros [B00 B04 B40 B44 B02 B42 B20 B24 B22].
  (* We need to manually supply 25 bits of data. We start with the types and which we define as total spaces of the families. *)
  srapply (Build_Diagram3x3
        B00    (sig2 B02)     B04
    (sig2 B20) (sig42 B22) (sig2 B24)
        B40    (sig2 B42)     B44 _); cbn.
  (* Now we need to define the maps. We introduce the variable in order to quickly select the components. *)
  1,2,3,4,5,6,7,8,9,10,11,12: intro x.
  (* f01 *)
  1: exact x.1.
  (* f03 *)
  1: exact x.2.1.
  (* f10 *)
  1: exact x.1.
  (* f12 *)
  1: exact (x.1 ; x.2.2.1 ; x.2.2.2.2.1).
  (* f14 *)
  1: exact x.1.
  (* f21 *)
  1: exact (x.1 ; x.2.2.2.1 ; x.2.2.2.2.2.2.1).
  (* f23 *)
  1: exact (x.2.2.1 ; x.2.1 ; x.2.2.2.2.2.2.2.1).
  (* f30 *)
  1: exact x.2.1.
  (* f32 *)
  1: exact (x.2.2.2.1 ; x.2.1 ; x.2.2.2.2.2.1).
  (* f34 *)
  1: exact x.2.1.
  (* f41 *)
  1: exact x.1.
  (* f42 *)
  1: exact x.2.1.
  (* Finally all our homotopies commute by definition. *)
  all: reflexivity.
Defined.

(* Now what about the other way? *)
Definition Diagram3x3_to_Dep3x3 : Diagram3x3 -> DepDiagram3x3.
Proof.
  intros [A00 A02 A04 A20 A22 A24 A40 A42 A44
    f01 f03 f10 f12 f14 f21 f23 f30 f32 f34 f41 f43
    H11 H13 H31 H33].
  srapply (Build_DepDiagram3x3 A00 A04 A40 A44).
  + intros a00 a04.
    exact {x : _ & (f01 x = a00) * (f03 x = a04)}.
  + intros a40 a44.
    exact {x : _ & (f41 x = a40) * (f43 x = a44)}.
  + intros a00 a40.
    exact {x : _ & (f10 x = a00) * (f30 x = a40)}.
  + intros a04 a44.
    exact {x : _ & (f14 x = a04) * (f34 x = a44)}.
  + cbn.
    intros a00 a44 a04 a40
     [a02 [p01 p03]] [a42 [p41 p43]] [a20 [p10 p30]] [a24 [p14 p34]].
    refine {x : A22 & _}.
    refine {p12 : f12 x = a02 & _}.
    refine {p32 : f32 x = a42 & _}.
    refine {p21 : f21 x = a20 & _}.
    refine {p23 : f23 x = a24 & _}.
    refine (_ * _ * _ * _).
    - refine (PathSquare (H11 x) (p01 @ p10^) (ap _ p12) (ap _ p21)).
    - refine (PathSquare (H13 x) (p03 @ p14^) (ap _ p12) (ap _ p23)).
    - refine (PathSquare (H31 x) (p41 @ p30^) (ap _ p32) (ap _ p21)).
    - refine (PathSquare (H33 x) (p43 @ p34^) (ap _ p32) (ap _ p23)).
Defined.

Definition Pushout_RC : Diagram3x3 -> Type :=
  fun X =>
    


