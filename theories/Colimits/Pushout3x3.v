Require Import Basics Types.
Require Import Cubical.
Require Import Colimits.Pushout.
Require Import Colimits.SymmetricDoublePushout.

(** In this file we show that double pushouts contstructed in two ways satisfy the universal property of symmetric double pushouts and are hence equivalent. This is known as the 3x3 lemma for pushouts. *)

(** First we show that pushing out coloumns then rows is a symmetric double pushout. *)
Module ColoumnsRows <: SymmetricDoublePushoutSpec.

  Section ColoumnsRows.

    Universe U.

    Context {A00 A10 A01 A11 : Type@{U}}
      {A0X : A00 -> A01 -> Type@{U}} {A1X : A10 -> A11 -> Type@{U}}
      {AX0 : A00 -> A10 -> Type@{U}} {AX1 : A01 -> A11 -> Type@{U}}
      {AXX : forall a00 a01 a10 a11, A0X a00 a01 -> A1X a10 a11 -> AX0 a00 a10 -> AX1 a01 a11 -> Type@{U}}.

    Local Definition B00 := A00.
    Local Definition B10 := A10.
    Local Definition B01 := A01.
    Local Definition B11 := A11.

    Local Definition B0X := sig2 A0X.
    Local Definition B1X := sig2 A1X.
    Local Definition BX0 := sig2 AX0.
    Local Definition BX1 := sig2 AX1.

    Local Definition BXX := sig44 AXX.

    Local Definition fi0 := (pr1 : BX0 -> B00).
    Local Definition fj0 := ((fun x => pr1 (pr2 x)) : BX0 -> B10).

    Local Definition fiX := ((fun a => (a.1; a.2.1; a.2.2.2.2.1)) : BXX -> B0X).
    Local Definition fjX := ((fun a => (a.2.2.1; a.2.2.2.1; a.2.2.2.2.2.1)) : BXX -> B1X).

    Local Definition fi1 := (pr1 : BX1 -> B01).
    Local Definition fj1 := ((fun x => pr1 (pr2 x)) : BX1 -> B11).

    Local Definition f0i := (pr1 : B0X -> B00).
    Local Definition f0j := ((fun x => pr1 (pr2 x)) : B0X -> B01).

    Local Definition fXi := ((fun a => (a.1; a.2.2.1; a.2.2.2.2.2.2.1)) : BXX -> BX0).
    Local Definition fXj := ((fun a => (a.2.1; a.2.2.2.1; a.2.2.2.2.2.2.2.1))
      : BXX -> BX1).

    Local Definition f1i := (pr1 : B1X -> B10).
    Local Definition f1j := ((fun x => pr1 (pr2 x)) : B1X -> B11).

    Local Definition C0 := Pushout f0i f0j.
    Local Definition CX := Pushout fXi fXj.
    Local Definition C1 := Pushout f1i f1j.

    Local Definition f'i: CX -> C0
      := Pushout_rec _ (pushl o fi0) (pushr o fi1) (pglue o fiX).
    Local Definition f'j : CX -> C1
      := Pushout_rec _ (pushl o fj0) (pushr o fj1) (pglue o fjX).

    Definition SymP : Type@{U} := Pushout f'i f'j.

    Definition a : B00 -> SymP := pushl o pushl.
    Definition b : B10 -> SymP := pushr o pushl.
    Definition c : B01 -> SymP := pushl o pushr.
    Definition d : B11 -> SymP := pushr o pushr.

    Definition H1 : a o f0i == c o f0j := fun x => ap pushl (pglue x).
    Definition H2 : a o fi0 == b o fj0 := fun x => pglue (pushl x).
    Definition H3 : c o fi1 == d o fj1 := fun x => pglue (pushr x).
    Definition H4 : b o f1i == d o f1j := fun x => ap pushr (pglue x).

    Definition sq@{} : forall x, PathSquare@{U} (H1 (fiX x)) (H4 (fjX x)) (H2 (fXi x)) (H3 (fXj x)).
    Proof.
      intro x.
      pose (s := ap_nat@{U U} (pglue@{U U U U} (f:=f'i) (g:=f'j)) (pglue@{U U U U} (f:=fXi) (g:=fXj) x)).
      refine (sq_GGcc@{U} _ _ s).
      1,2: refine (ap_compose _ _ _ @ ap@{U U} _ _).
      1,2: rapply Pushout_rec_beta_pglue.
    Defined.

    Section Induction.

      Context (P : SymP -> Type@{U})
        (xa : forall x, P (a x)) (xb : forall x, P (b x))
        (xc : forall x, P (c x)) (xd : forall x, P (d x))
        (Q1 : forall x, DPath P (H1 x) (xa (f0i x)) (xc (f0j x)))
        (Q2 : forall x, DPath P (H2 x) (xa (fi0 x)) (xb (fj0 x)))
        (Q3 : forall x, DPath P (H3 x) (xc (fi1 x)) (xd (fj1 x)))
        (Q4 : forall x, DPath P (H4 x) (xb (f1i x)) (xd (f1j x)))
        (xsq : forall x, DPathSquare P (sq x) (Q1 (fiX x)) (Q4 (fjX x))
          (Q2 (fXi x)) (Q3 (fXj x))).

      (** Auxillary computation rules for defining ind *)
      Section AuxComp.

        Context (x : BXX).

        Lemma part1 : DPath P (ap pushl (ap f'i (pglue x))) (xa x.1) (xc (f0j (fiX x))).
        Proof.
          rapply dp_G.
          1: apply ap; apply inverse; rapply Pushout_rec_beta_pglue.
          rapply Q1.
        Defined.

        Lemma part2@{} : DPath (fun x0 => DPath P x0 (xa x.1) (xc (f0j (fiX x))))
          (ap_compose f'i pushl (pglue x))
          (dp_compose (fun a0 : Pushout fXi fXj => pushl (f'i a0)) P (pglue x)
            (dp_apD (fun a0 => Pushout_ind_dp f0i f0j (fun w => P (pushl w)) xa xc
            (fun x0 => (dp_compose pushl P (pglue x0))^-1 (Q1 x0)) (f'i a0)) (pglue x)))
          part1.
        Proof.
        Admitted.

        Lemma part3 : DPath (fun p => DPath P p (xa (f0i (fiX x))) (xc (f0j (fiX x))))
          (ap (ap pushl) (Pushout_rec_beta_pglue (f:=fXi) (g:=fXj) C0
            (pushl o fi0) (pushr o fi1) (pglue o fiX) x))
          part1 (Q1 (fiX x)).
        Proof.
        Admitted.

        Lemma part4 : DPath P (ap pushr (ap f'j (pglue x))) (xb ((x.2).2).1) (xd (f1j (fjX x))).
        Proof.
        Admitted.

        Lemma part5 : DPath (fun p => DPath P p (xb (f1i (fjX x))) (xd (f1j (fjX x))))
          (ap_compose f'j pushr (pglue x))
          (dp_compose (pushr o f'j) P (pglue x)
            (dp_apD (fun y => Pushout_ind_dp f1i f1j (P o pushr) xb xd
            (fun z => (dp_compose pushr P (pglue z))^-1 (Q4 z)) (f'j y)) (pglue x))) 
          part4.
        Proof.
        Admitted.

        Lemma part6 : DPath (fun p => DPath P p (xb (f1i (fjX x))) (xd (f1j (fjX x))))
          (ap (ap pushr) (Pushout_rec_beta_pglue (f:=fXi) (g:=fXj)
            C1 (pushl o fj0) (pushr o fj1) (pglue o fjX) x))
          part4 (Q4 (fjX x)).
        Proof.
        Admitted.

      End AuxComp.

      (** Induction principle *)
      Definition SymP_ind@{} : forall (s : SymP), P s.
      Proof.
        snrapply Pushout_ind_dp.
        1,2: snrapply Pushout_ind_dp.
        1,2,4,5: assumption.
        1,2: intro x; apply dp_compose; revert x.
        1,2: assumption.
        snrapply Pushout_ind_dp.
        1,2: assumption.
        simpl.
        intro x.
        apply equiv_ds_nat_dp_dp.
        refine ((ds_GGcc _ _)^-1 (xsq x)).
        + srapply dp_concat; [apply part1 | apply part2 | apply part3].
        + srapply dp_concat; [apply part4 | apply part5 | apply part6].
     Defined.

    End Induction.

    (** Computation rules *)
    Section ComputationRules.

      Context (P : SymP -> Type)
        (xa : forall x, P (a x)) (xb : forall x, P (b x))
        (xc : forall x, P (c x)) (xd : forall x, P (d x))
        (Q1 : forall x, DPath P (H1 x) (xa (f0i x)) (xc (f0j x)))
        (Q2 : forall x, DPath P (H2 x) (xa (fi0 x)) (xb (fj0 x)))
        (Q3 : forall x, DPath P (H3 x) (xc (fi1 x)) (xd (fj1 x)))
        (Q4 : forall x, DPath P (H4 x) (xb (f1i x)) (xd (f1j x)))
        (xsq : forall x, DPathSquare P (sq x) (Q1 (fiX x)) (Q4 (fjX x)) (Q2 (fXi x)) (Q3 (fXj x))).

      (** Point computation rules *)
      Definition SymP_ind_beta_a@{} : forall x, SymP_ind P xa xb xc xd Q1 Q2 Q3 Q4 xsq (a x) = (xa x).
      Proof.
        reflexivity.
      Defined.

      Definition SymP_ind_beta_b@{} : forall x, SymP_ind P xa xb xc xd Q1 Q2 Q3 Q4 xsq (b x) = (xb x).
      Proof.
        reflexivity.
      Defined.

      Definition SymP_ind_beta_c@{} : forall x, SymP_ind P xa xb xc xd Q1 Q2 Q3 Q4 xsq (c x) = (xc x).
      Proof.
        reflexivity.
      Defined.

      Definition SymP_ind_beta_d@{} : forall x, SymP_ind P xa xb xc xd Q1 Q2 Q3 Q4 xsq (d x) = (xd x).
      Proof.
        reflexivity.
      Defined.

      (** Path computation rules *)
      Definition SymP_ind_beta_H1@{} : forall x,
        DPathSquare P (sq_refl_h (H1 x)) (dp_apD (SymP_ind P xa xb xc xd Q1 Q2 Q3 Q4 xsq) (H1 x)) (Q1 x)
          (SymP_ind_beta_a (f0i x)) (SymP_ind_beta_c (f0j x)).
      Proof.
        intro x.
        apply ds_G1; cbn.
      Admitted.

      Definition SymP_ind_beta_H2@{} : forall x,
        DPathSquare P (sq_refl_h (H2 x)) (dp_apD (SymP_ind P xa xb xc xd Q1 Q2 Q3 Q4 xsq) (H2 x)) (Q2 x)
          (SymP_ind_beta_a (fi0 x)) (SymP_ind_beta_b (fj0 x)).
      Proof.
      Admitted.

      Definition SymP_ind_beta_H3@{} : forall x,
        DPathSquare P (sq_refl_h (H3 x)) (dp_apD (SymP_ind P xa xb xc xd Q1 Q2 Q3 Q4 xsq) (H3 x)) (Q3 x)
          (SymP_ind_beta_c (fi1 x)) (SymP_ind_beta_d (fj1 x)).
      Proof.
      Admitted.
      
      Definition SymP_ind_beta_H4@{} : forall x,
        DPathSquare P (sq_refl_h (H4 x)) (dp_apD (SymP_ind P xa xb xc xd Q1 Q2 Q3 Q4 xsq) (H4 x)) (Q4 x)
          (SymP_ind_beta_b (f1i x)) (SymP_ind_beta_d (f1j x)).
      Proof.
      Admitted.
      
      (** Square compuation rules *)
      Definition SymP_ind_beta_sq@{} : forall x,
        DPathCube P (cu_refl_lr (sq x))
          (ds_apD (SymP_ind P xa xb xc xd Q1 Q2 Q3 Q4 xsq) (sq x)) (xsq x)
          (SymP_ind_beta_H1 (fiX x)) (SymP_ind_beta_H4 (fjX x))
          (SymP_ind_beta_H2 (fXi x)) (SymP_ind_beta_H3 (fXj x)).
      Proof.
        intro x.
      Admitted.

    End ComputationRules.
  End ColoumnsRows.
End ColoumnsRows.

(** Now we show that pushing out rows then coloumns is a symmetric double pushout. *)
Module RowsColoumns <: SymmetricDoublePushoutSpec.

  Section RowsColoumns.

    Universe U.

    Context {A00 A10 A01 A11 : Type@{U}}
      {A0X : A00 -> A01 -> Type@{U}} {A1X : A10 -> A11 -> Type@{U}}
      {AX0 : A00 -> A10 -> Type@{U}} {AX1 : A01 -> A11 -> Type@{U}}
      {AXX : forall a00 a01 a10 a11, A0X a00 a01 -> A1X a10 a11 -> AX0 a00 a10 -> AX1 a01 a11 -> Type@{U}}.

    Local Definition B00 := A00.
    Local Definition B10 := A10.
    Local Definition B01 := A01.
    Local Definition B11 := A11.

    Local Definition B0X := sig2 A0X.
    Local Definition B1X := sig2 A1X.
    Local Definition BX0 := sig2 AX0.
    Local Definition BX1 := sig2 AX1.

    Local Definition BXX := sig44 AXX.

    Local Definition fi0 := (pr1 : BX0 -> B00).
    Local Definition fj0 := ((fun x => pr1 (pr2 x)) : BX0 -> B10).

    Local Definition fiX := ((fun a => (a.1; a.2.1; a.2.2.2.2.1)) : BXX -> B0X).
    Local Definition fjX := ((fun a => (a.2.2.1; a.2.2.2.1; a.2.2.2.2.2.1)) : BXX -> B1X).

    Local Definition fi1 := (pr1 : BX1 -> B01).
    Local Definition fj1 := ((fun x => pr1 (pr2 x)) : BX1 -> B11).

    Local Definition f0i := (pr1 : B0X -> B00).
    Local Definition f0j := ((fun x => pr1 (pr2 x)) : B0X -> B01).

    Local Definition fXi := ((fun a => (a.1; a.2.2.1; a.2.2.2.2.2.2.1)) : BXX -> BX0).
    Local Definition fXj := ((fun a => (a.2.1; a.2.2.2.1; a.2.2.2.2.2.2.2.1))
      : BXX -> BX1).

    Local Definition f1i := (pr1 : B1X -> B10).
    Local Definition f1j := ((fun x => pr1 (pr2 x)) : B1X -> B11).

    Definition R0 := Pushout fi0 fj0.
    Definition RX := Pushout fiX fjX.
    Definition R1 := Pushout fi1 fj1.

    Definition fi : RX -> R0
      := Pushout_rec _ (pushl o f0i) (pushr o f1i) (pglue o fXi).
    Definition fj : RX -> R1
      := Pushout_rec _ (pushl o f0j) (pushr o f1j) (pglue o fXj).
    Definition R := Pushout fi fj.

    Definition SymP : Type@{U} := Pushout fi fj.

    Definition a : B00 -> SymP.
    Proof.
    Admitted.
    
    Definition b : B10 -> SymP.
    Proof.
    Admitted.
    
    Definition c : B01 -> SymP.
    Proof.
    Admitted.
    
    Definition d : B11 -> SymP.
    Proof.
    Admitted.
    
    Definition H1 : a o f0i == c o f0j.
    Proof.
    Admitted.
    
    Definition H2 : a o fi0 == b o fj0.
    Proof.
    Admitted.
    
    Definition H3 : c o fi1 == d o fj1.
    Proof.
    Admitted.
    
    Definition H4 : b o f1i == d o f1j.
    Proof.
    Admitted.
    
    Definition sq : forall x, PathSquare (H1 (fiX x)) (H4 (fjX x)) (H2 (fXi x)) (H3 (fXj x)).
    Proof.
    Admitted.


    (** Induction principle *)
    Definition SymP_ind@{} : forall (P : SymP -> Type@{U})
      (xa : forall x, P (a x)) (xb : forall x, P (b x))
      (xc : forall x, P (c x)) (xd : forall x, P (d x))
      (Q1 : forall x, DPath P (H1 x) (xa (f0i x)) (xc (f0j x)))
      (Q2 : forall x, DPath P (H2 x) (xa (fi0 x)) (xb (fj0 x)))
      (Q3 : forall x, DPath P (H3 x) (xc (fi1 x)) (xd (fj1 x)))
      (Q4 : forall x, DPath P (H4 x) (xb (f1i x)) (xd (f1j x)))
      (xsq : forall x, DPathSquare P (sq x) (Q1 (fiX x)) (Q4 (fjX x)) (Q2 (fXi x)) (Q3 (fXj x)))
      (s : SymP), P s.
    Proof.
    Admitted.

    (** Computation rules *)
    Section ComputationRules.

      Context (P : SymP -> Type)
        (xa : forall x, P (a x)) (xb : forall x, P (b x))
        (xc : forall x, P (c x)) (xd : forall x, P (d x))
        (Q1 : forall x, DPath P (H1 x) (xa (f0i x)) (xc (f0j x)))
        (Q2 : forall x, DPath P (H2 x) (xa (fi0 x)) (xb (fj0 x)))
        (Q3 : forall x, DPath P (H3 x) (xc (fi1 x)) (xd (fj1 x)))
        (Q4 : forall x, DPath P (H4 x) (xb (f1i x)) (xd (f1j x)))
        (xsq : forall x, DPathSquare P (sq x) (Q1 (fiX x)) (Q4 (fjX x)) (Q2 (fXi x)) (Q3 (fXj x))).

      (** Point computation rules *)
      Definition SymP_ind_beta_a : forall x, SymP_ind P xa xb xc xd Q1 Q2 Q3 Q4 xsq (a x) = (xa x).
      Proof.
      Admitted.
      
      Definition SymP_ind_beta_b : forall x, SymP_ind P xa xb xc xd Q1 Q2 Q3 Q4 xsq (b x) = (xb x).
      Proof.
      Admitted.
      
      Definition SymP_ind_beta_c : forall x, SymP_ind P xa xb xc xd Q1 Q2 Q3 Q4 xsq (c x) = (xc x).
      Proof.
      Admitted.
      
      Definition SymP_ind_beta_d : forall x, SymP_ind P xa xb xc xd Q1 Q2 Q3 Q4 xsq (d x) = (xd x).
      Proof.
      Admitted.
      
      (** Path computation rules *)
      Definition SymP_ind_beta_H1 : forall x,
        DPathSquare P (sq_refl_h (H1 x)) (dp_apD (SymP_ind P xa xb xc xd Q1 Q2 Q3 Q4 xsq) (H1 x)) (Q1 x)
          (SymP_ind_beta_a (f0i x)) (SymP_ind_beta_c (f0j x)).
      Proof.
      Admitted.
      
      Definition SymP_ind_beta_H2 : forall x,
        DPathSquare P (sq_refl_h (H2 x)) (dp_apD (SymP_ind P xa xb xc xd Q1 Q2 Q3 Q4 xsq) (H2 x)) (Q2 x)
          (SymP_ind_beta_a (fi0 x)) (SymP_ind_beta_b (fj0 x)).
      Proof.
      Admitted.
      
      Definition SymP_ind_beta_H3 : forall x,
        DPathSquare P (sq_refl_h (H3 x)) (dp_apD (SymP_ind P xa xb xc xd Q1 Q2 Q3 Q4 xsq) (H3 x)) (Q3 x)
          (SymP_ind_beta_c (fi1 x)) (SymP_ind_beta_d (fj1 x)).
      Proof.
      Admitted.
      
      Definition SymP_ind_beta_H4 : forall x,
        DPathSquare P (sq_refl_h (H4 x)) (dp_apD (SymP_ind P xa xb xc xd Q1 Q2 Q3 Q4 xsq) (H4 x)) (Q4 x)
          (SymP_ind_beta_b (f1i x)) (SymP_ind_beta_d (f1j x)).
      Proof.
      Admitted.
      
      (** Square compuation rules *)
      Definition SymP_ind_beta_sq : forall x,
        DPathCube P (cu_refl_lr (sq x))
          (ds_apD (SymP_ind P xa xb xc xd Q1 Q2 Q3 Q4 xsq) (sq x)) (xsq x)
          (SymP_ind_beta_H1 (fiX x)) (SymP_ind_beta_H4 (fjX x))
          (SymP_ind_beta_H2 (fXi x)) (SymP_ind_beta_H3 (fXj x)).
      Proof.
      Admitted.

    End ComputationRules.
  End RowsColoumns.
End RowsColoumns.

Module Eq := SymmetricDoublePushoutEquiv ColoumnsRows RowsColoumns.

Section Pushout3x3.

 Context {A00 A10 A01 A11 : Type}
    {A0X : A00 -> A01 -> Type} {A1X : A10 -> A11 -> Type}
    {AX0 : A00 -> A10 -> Type} {AX1 : A01 -> A11 -> Type}
    {AXX : forall a00 a01 a10 a11, A0X a00 a01 -> A1X a10 a11 -> AX0 a00 a10 -> AX1 a01 a11 -> Type}.

  Local Definition B00 := A00.
  Local Definition B10 := A10.
  Local Definition B01 := A01.
  Local Definition B11 := A11.

  Local Definition B0X := sig2 A0X.
  Local Definition B1X := sig2 A1X.
  Local Definition BX0 := sig2 AX0.
  Local Definition BX1 := sig2 AX1.

  Local Definition BXX := sig44 AXX.

  Local Definition fi0 := (pr1 : BX0 -> B00).
  Local Definition fj0 := ((fun x => pr1 (pr2 x)) : BX0 -> B10).

  Local Definition fiX := ((fun a => (a.1; a.2.1; a.2.2.2.2.1)) : BXX -> B0X).
  Local Definition fjX := ((fun a => (a.2.2.1; a.2.2.2.1; a.2.2.2.2.2.1)) : BXX -> B1X).

  Local Definition fi1 := (pr1 : BX1 -> B01).
  Local Definition fj1 := ((fun x => pr1 (pr2 x)) : BX1 -> B11).

  Local Definition f0i := (pr1 : B0X -> B00).
  Local Definition f0j := ((fun x => pr1 (pr2 x)) : B0X -> B01).

  Local Definition fXi := ((fun a => (a.1; a.2.2.1; a.2.2.2.2.2.2.1)) : BXX -> BX0).
  Local Definition fXj := ((fun a => (a.2.1; a.2.2.2.1; a.2.2.2.2.2.2.2.1))
    : BXX -> BX1).

  Local Definition f1i := (pr1 : B1X -> B10).
  Local Definition f1j := ((fun x => pr1 (pr2 x)) : B1X -> B11).

  Definition R0 := Pushout fi0 fj0.
  Definition RX := Pushout fiX fjX.
  Definition R1 := Pushout fi1 fj1.

  Definition fi : RX -> R0
    := Pushout_rec _ (pushl o f0i) (pushr o f1i) (pglue o fXi).
  Definition fj : RX -> R1
    := Pushout_rec _ (pushl o f0j) (pushr o f1j) (pglue o fXj).
  Definition R := Pushout fi fj.

  Definition C0 := Pushout f0i f0j.
  Definition CX := Pushout fXi fXj.
  Definition C1 := Pushout f1i f1j.

  Definition f'i: CX -> C0
    := Pushout_rec _ (pushl o fi0) (pushr o fi1) (pglue o fiX).
  Definition f'j : CX -> C1
    := Pushout_rec _ (pushl o fj0) (pushr o fj1) (pglue o fjX).
  Definition C := Pushout f'i f'j.

  (** This is the pushout 3x3 lemma for fibrantly replaced diagrams. *)
  Definition pushout3x3' : C <~> R
    := Eq.equiv_symmetric_double_pushout (AXX:=AXX).

End Pushout3x3.
