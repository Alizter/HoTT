Require Import HoTT.Basics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.


Section Util.
  
  
  (** Used for "inspect idiom" in proofs below **)
  Inductive Graph {X : Type} {Y : X -> Type} 
    (f : forall x, Y x) (x : X) (y : Y x) : Type :=
    | ingraph : f x = y -> Graph f x y.
  
  Definition inspect {X : Type} {Y : X -> Type} 
    (f : forall x, Y x) (x : X) : Graph f x (f x).
  Proof. 
    rapply (@ingraph); refine idpath.
  Defined.
  
  
End Util.