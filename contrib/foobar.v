Require Import Basics.
Require Import Types.
Require Import Spaces.Finite.
Require Import HIT.Pushout.
Require Import HIT.Colimits.

Section foo.

Context
  (A00 A10 A01 A11 : Type)
  (A0x : A00 -> A01 -> Type)
  (A1x : A10 -> A11 -> Type)
  (Ax0 : A00 -> A10 -> Type)
  (Ax1 : A01 -> A11 -> Type)
  (Axx : forall a00 a01 a10 a11,
    A0x a00 a01 ->
    A1x a10 a11 ->
    Ax0 a00 a10 ->
    Ax1 a01 a11 -> Type).

  Definition B00 := A00.
  Definition B10 := A10.
  Definition B01 := A01.
  Definition B11 := A11.

  Definition B0x := {a00 : A00 & {a01 : A01 & A0x a00 a01}}.
  Definition B1x := {a10 : A10 & {a11 : A11 & A1x a10 a11}}.
  Definition Bx0 := {a00 : A00 & {a10 : A10 & Ax0 a00 a10}}.
  Definition Bx1 := {a01 : A01 & {a11 : A11 & Ax1 a01 a11}}.

  Definition Bxx := {a00 : A00 & {a01 : A01 & {a10 : A10 & {a11 : A11 &
             {a0x : A0x a00 a01 & {a1x : A1x a10 a11 &
             {ax0 : Ax0 a00 a10 & {ax1 : Ax1 a01 a11 &
              Axx a00 a01 a10 a11 a0x a1x ax0 ax1}}}}}}}}.

  Definition fi0 : Bx0 -> B00 := pr1.
  Definition fj0 : Bx0 -> B10 := fun x => pr1 (pr2 x).

  Definition f'ix : Bxx -> B0x := fun a => (a.1; a.2.1; a.2.2.2.2.1).
  Definition fjx : Bxx -> B1x := fun a => (a.2.2.1; a.2.2.2.1; a.2.2.2.2.2.1).

  Definition fi1 : Bx1 -> B01 := pr1.
  Definition fj1 : Bx1 -> B11 := fun x => pr1 (pr2 x).
  
  Definition f0i : B0x -> B00 := pr1.
  Definition f0j : B0x -> B01 := fun x => pr1 (pr2 x).
  
  Definition fxi : Bxx -> Bx0 := fun a => (a.1; a.2.2.1; a.2.2.2.2.2.2.1).
  Definition fxj : Bxx -> Bx1 := fun a => (a.2.1; a.2.2.2.1; a.2.2.2.2.2.2.2.1).

  Definition f1i : B1x -> B10 := pr1.
  Definition f1j : B1x -> B11 := fun x => pr1 (pr2 x).

(* Inductive nine := 
  | nine1 | nine2 | nine3
  | nine4 | nine5 | nine6
  | nine7 nine8 | nine9
}.
 *)
Definition three : graph.
Proof.
  serapply Build_graph.
  + exact (Fin 9).
  + FinInd.
    1,3,7,9: intros; exact Empty.
    { FinInd.
      2,4,5,6,7,8,9: exact Empty.
      1,2: exact Unit. }
    { FinInd.
      2,3,4,5,6,8,9: exact Empty.
      1,2: exact Unit. }
    { FinInd.
      1,3,5,7,9: exact Empty.
      1,2,3,4: exact Unit. }
    { FinInd.
      1,2,4,5,6,7,8: exact Empty.
      1,2: exact Unit. }
    { FinInd.
      1,2,3,4,5,6,8: exact Empty.
      1,2: exact Unit. }
Defined.

Definition threeDia : diagram three.
Proof.
  serapply Build_diagram.
  + change (Fin 9 -> Type).
    FinInd.
    1: exact B00.
    1: exact Bx0.
    1: exact B10.
    1: exact B0x.
    1: exact Bxx.
    1: exact B1x.
    1: exact B01.
    1: exact Bx1.
    1: exact B11.
  + change (graph0 three) with (Fin 9).
    FinInd.
    1,3,7,9: intro; contradiction.
    { FinInd.
      2,4,5,6,7,8,9: intro; contradiction.
      1: intro; exact fi0.
      intro; exact fj0. }
    { FinInd.
      2,3,4,5,6,8,9: intro; contradiction.
      1: intro; exact f0i.
      intro; exact f0j. }
    { FinInd.
      1,3,5,7,9: intro; contradiction.
      + intro; exact fxi.
      + intro; exact f'ix.
      + intro; exact fjx.
      + intro; exact fxj. }
    { FinInd.
      1,2,4,5,6,7,8: intro; contradiction.
      1: intro; exact f1i.
      intro; exact f1j. }
    { FinInd.
      1,2,3,4,5,6,8: intro; contradiction.
      1: intro; exact fi1.
      intro; exact fj1. }
  Defined.


  Definition R0 := pushout fi0 fj0.
  Definition RX := pushout f'ix fjx.
  Definition R1 := pushout fi1 fj1.

  Definition fi : RX -> R0.
  Proof.
    serapply pushout_rec.
    1: exact (pushl o f0i).
    1: exact (pushr o f1i).
    exact (fun a => @pp _ _ _ fi0 fj0 (a.1; a.2.2.1; a.2.2.2.2.2.2.1)).
  Defined.

  Definition fj : RX -> R1.
  Proof.
    serapply pushout_rec.
    1: exact (pushl o f0j).
    1: exact (pushr o f1j).
    exact (fun a => @pp _ _ _ fi1 fj1 (a.2.1; a.2.2.2.1; a.2.2.2.2.2.2.2.1)).
  Defined.

  Definition R := pushout fi fj.

  Definition C0 := pushout f0i f0j.
  Definition CX := pushout fxi fxj.
  Definition C1 := pushout f1i f1j.

  Definition f'i: CX -> C0.
  Proof.
    serapply pushout_rec.
    1: exact (pushl o fi0).
    1: exact (pushr o fi1).
    exact (fun a => @pp _ _ _ f0i f0j (a.1; a.2.1; a.2.2.2.2.1)).
  Defined.

  Definition f'j : CX -> C1.
  Proof.
    serapply pushout_rec.
    1: exact (pushl o fj0).
    1: exact (pushr o fj1).
    exact (fun a => @pp _ _ _ f1i f1j (a.2.2.1; a.2.2.2.1; a.2.2.2.2.2.1)).
  Defined.

  Definition C := pushout f'i f'j.

Optimize Proof.
Optimize Heap.

Definition foo := colimit threeDia.

 Definition fzero {n : nat} : Fin n.+1.
  Proof.
    induction n.
    + exact (inr tt).
    + exact (inl IHn).
  Defined.

  Definition fsucc {n : nat} : Fin n.+1 -> Fin n.+1.
  Proof.
    induction n.
    + intro; exact fzero.
    + intros [[x|]|].
      - exact (inl (IHn (inl x))).
      - exact (inr tt).
      - exact fzero.
Defined.

Fixpoint iter {A} (f : A -> A) (n : nat)
  := match n with
      | O => idmap
      | S n' => f o iter f n'
end.

  Definition fmod {n : nat} : nat -> Fin n.+1
:= fun m => iter fsucc m fzero.

Theorem bar E : cocone threeDia E <~> (R -> E).
Proof.
  serapply equiv_adjointify.
  { intros [].
    unfold C.
    serapply pushout_rec.
    { serapply pushout_rec.
      + exact (q (fmod 0)).
      + exact (q (fmod 2)).
      + intro a.
        cbn.
        set (qq (fmod 2) (fmod 0)).
        
        cbn in p.
        cbn.
        symmetry.
        apply p.
        intros [b00 [b01 b0x]].
        
      intro.
      apply q.




