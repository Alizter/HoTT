Require Import Basics.
Require Import Yoneda.
Require Import Limits.Pullback.
Require Import Colimits.Pushout.

(* 3x3 Diagram -- We can't use the Diagrams.Diagram since our diagrams commute up to homotopy. Therefore we would need a diagram over a graph with composition. Such as the one defined in Execuse 7.15.

The diagram looks like the following:

    A00 <--- A02 ---> A04
     ^     // ^ \\     ^
     |    //  |  \\    |
     |   VV   |   VV   |
    A20 <--- A22 ---> A24
     |   ^^   |   ^^   |
     |    \\  |  //    |
     V     \\ V //     V
    A40 <--- A42 ---> A44

The labels look like this:

    A00 f01 A02 f03 A04
    f10 H11 f12 H13 f14
    A20 f21 A22 f23 A24
    f30 H31 f32 H33 f34
    A40 f41 A42 f43 A44 *)

Section Pushout3x3.

  Context `{Funext}
    (B00 B04 B40 B44 : Type) 
    (B02 : B00 -> B04 -> Type) 
    (B42 : B40 -> B44 -> Type) 
    (B20 : B00 -> B40 -> Type) 
    (B24 : B04 -> B44 -> Type) 
    (B22 : forall b00 b44 b04 b40, 
      B02 b00 b04 -> B42 b40 b44 -> 
      B20 b00 b40 -> B24 b04 b44 -> Type ). 
 
  Local Definition A00 := B00. 
  Local Definition A04 := B04. 
  Local Definition A40 := B40. 
  Local Definition A44 := B44. 
 
  Local Notation sig2 A := {x : _ & {y : _ & A x y}}. 
 
  Local Definition A02 := sig2 B02. 
  Local Definition A42 := sig2 B42. 
  Local Definition A20 := sig2 B20. 
  Local Definition A24 := sig2 B24. 
 
  Local Definition A22 := 
    {a00 : _ & {a44 : _ & {a04 : _ & {a40 : _ & 
    {a02 : _ & {a42 : _ & {a20 : _ & {a24 : _ & 
      B22 a00 a44 a04 a40 a02 a42 a20 a24}}}}}}}}. 
 
  Local Definition f01 : A02 -> A00 := fun x => x.1. 
  Local Definition f03 : A02 -> A04 := fun x => x.2.1. 
 
  Local Definition f10 : A20 -> A00 := fun x => x.1. 
  Local Definition f12 : A22 -> A02 := fun x => (x.1 ; x.2.2.1 ; x.2.2.2.2.1). 
  Local Definition f14 : A24 -> A04 := fun x => x.1. 
 
  Local Definition f21 : A22 -> A20 
    := fun x => (x.1 ; x.2.2.2.1 ; x.2.2.2.2.2.2.1). 
  Local Definition f23 : A22 -> A24 
    := fun x : A22 => (x.2.2.1 ; x.2.1 ; x.2.2.2.2.2.2.2.1). 
 
  Local Definition f30 : A20 -> A40 := fun x => x.2.1. 
  Local Definition f32 : A22 -> A42 
    := fun x => (x.2.2.2.1 ; x.2.1 ; x.2.2.2.2.2.1). 
  Local Definition f34 : A24 -> A44 := fun x => x.2.1. 
 
  Local Definition f41 : A42 -> A40 := fun x => x.1. 
  Local Definition f43 : A42 -> A44 := fun x => x.2.1. 
 
  Local Definition AX0 := Pushout f10 f30. 
  Local Definition AX2 := Pushout f12 f32. 
  Local Definition AX4 := Pushout f14 f34. 
 
  Local Definition fX1 : AX2 -> AX0 
    := Pushout_rec _ (pushl o f01) (pushr o f41) (pglue o f21). 
  Local Definition fX3 : AX2 -> AX4 
    := Pushout_rec _ (pushl o f03) (pushr o f43) (pglue o f23). 
 
  Local Definition AXO := Pushout fX1 fX3. 
 
  Local Definition A0X := Pushout f01 f03. 
  Local Definition A2X := Pushout f21 f23. 
  Local Definition A4X := Pushout f41 f43. 
 
  Local Definition f1X : A2X -> A0X 
    := Pushout_rec _ (pushl o f10) (pushr o f14) (pglue o f12). 
  Local Definition f3X : A2X -> A4X 
    := Pushout_rec _ (pushl o f30) (pushr o f34) (pglue o f32). 
 
  Local Definition AOX := Pushout f1X f3X.

  Theorem ThreeByThree : AXO <~> AOX.
  Proof.
    
  
    serapply yoneda.
    { intro X.
      refine (equiv_pullback_pushout^-1 oE _ oE equiv_pullback_pushout).
      
      
      
      
      serapply equiv_pullback.
      1,2,3: refine (equiv_pullback_pushout^-1 oE _ oE equiv_pullback_pushout).
      { serapply equiv_pullback.
        1: reflexivity.
        all: simpl.
      
      
      serapply equiv_adjointify.
      { intros [a [b p]].
        rewrite <- (eissect equiv_pullback_pushout a) in p.
        rewrite <- (eissect equiv_pullback_pushout b) in p.
        set (a' := equiv_pullback_pushout a) in *.
        set (b' := equiv_pullback_pushout b) in *.
        clearbody a' b'; clear a b.
        simpl in a', b', p.
        unfold Pullback in *.
        srefine (_;_).
        { apply equiv_pullback_pushout^-1.
          unfold Pullback.
          exists a'.1.
          exists b'.1.
          apply path_forall.
          intro.
          apply apD10 in p.
          
        
        
        unfold AX0 in a.
        apply equiv_pullback_pushout a in a.
        unfold Pullback.












 