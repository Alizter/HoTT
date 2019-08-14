Require Import Basics.
Require Import Cubical.

Module Export SymP.

  Section Push.
    Context
      {A00 A10 A01 A11 : Type}
      {A0X : A00 -> A01 -> Type}
      {A1X : A10 -> A11 -> Type}
      {AX0 : A00 -> A10 -> Type}
      {AX1 : A01 -> A11 -> Type}
      {AXX : forall a00 a01 a10 a11,
        A0X a00 a01 ->
        A1X a10 a11 ->
        AX0 a00 a10 ->
        AX1 a01 a11 -> Type}.

    Local Definition B00 := A00.
    Local Definition B10 := A10.
    Local Definition B01 := A01.
    Local Definition B11 := A11.

    Local Definition B0X := {a00 : A00 & {a01 : A01 & A0X a00 a01}}.
    Local Definition B1X := {a10 : A10 & {a11 : A11 & A1X a10 a11}}.
    Local Definition BX0 := {a00 : A00 & {a10 : A10 & AX0 a00 a10}}.
    Local Definition BX1 := {a01 : A01 & {a11 : A11 & AX1 a01 a11}}.

    Local Definition BXX := {a00 : A00 & {a01 : A01 & {a10 : A10 & {a11 : A11 &
               {a0X : A0X a00 a01 & {a1X : A1X a10 a11 &
               {aX0 : AX0 a00 a10 & {aX1 : AX1 a01 a11 &
                AXX a00 a01 a10 a11 a0X a1X aX0 aX1}}}}}}}}.

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

    Private Inductive SymP :=
      | a : B00 -> SymP
      | b : B10 -> SymP
      | c : B01 -> SymP
      | d : B11 -> SymP.

    Axiom H1 : a o f0i == c o f0j.
    Axiom H2 : a o fi0 == b o fj0.
    Axiom H3 : c o fi1 == d o fj1.
    Axiom H4 : b o f1i == d o f1j.

    Axiom sq 
      : forall x,
        Square (H1 (fiX x)) (H4 (fjX x)) (H2 (fXi x)) (H3 (fXj x)).

    Section ind.

      Definition SymP_ind (P : SymP -> Type)
        {xa : forall x, P (a x)}
        {xb : forall x, P (b x)}
        {xc : forall x, P (c x)}
        {xd : forall x, P (d x)}
        (Q1 : forall x, DPath P (H1 x) (xa (f0i x)) (xc (f0j x)))
        (Q2 : forall x, DPath P (H2 x) (xa (fi0 x)) (xb (fj0 x)))
        (Q3 : forall x, DPath P (H3 x) (xc (fi1 x)) (xd (fj1 x)))
        (Q4 : forall x, DPath P (H4 x) (xb (f1i x)) (xd (f1j x)))
        (xsq : forall x, DSquare P (sq x)
          (Q1 (fiX x)) (Q4 (fjX x)) (Q2 (fXi x)) (Q3 (fXj x))) (s : SymP) : P s.
      Proof.
        destruct s; (apply xa || apply xb || apply xc || apply xd).
      Defined.

      Context
        (P : SymP -> Type)
        {xa : forall x, P (a x)}
        {xb : forall x, P (b x)}
        {xc : forall x, P (c x)}
        {xd : forall x, P (d x)}
        (Q1 : forall x, DPath P (H1 x) (xa (f0i x)) (xc (f0j x)))
        (Q2 : forall x, DPath P (H2 x) (xa (fi0 x)) (xb (fj0 x)))
        (Q3 : forall x, DPath P (H3 x) (xc (fi1 x)) (xd (fj1 x)))
        (Q4 : forall x, DPath P (H4 x) (xb (f1i x)) (xd (f1j x)))
        (xsq : forall x, DSquare P (sq x)
          (Q1 (fiX x)) (Q4 (fjX x)) (Q2 (fXi x)) (Q3 (fXj x))).

      Axiom SymP_ind_beta_H1 : forall x, dp_apD (SymP_ind P Q1 Q2 Q3 Q4 xsq)
        (H1 x) = Q1 x.
      Axiom SymP_ind_beta_H2 : forall x, dp_apD (SymP_ind P Q1 Q2 Q3 Q4 xsq)
        (H2 x) = Q2 x.
      Axiom SymP_ind_beta_H3 : forall x, dp_apD (SymP_ind P Q1 Q2 Q3 Q4 xsq)
        (H3 x) = Q3 x.
      Axiom SymP_ind_beta_H4 : forall x, dp_apD (SymP_ind P Q1 Q2 Q3 Q4 xsq)
        (H4 x) = Q4 x.

    End ind.

    Section rec.

       Lemma SymP_rec (P : Type)
        {xa : B00 -> P} {xb : B10 -> P} {xc : B01 -> P} {xd : B11 -> P}
        (xH1 : xa o f0i == xc o f0j) (xH2 : xa o fi0 == xb o fj0)
        (xH3 : xc o fi1 == xd o fj1) (xH4 : xb o f1i == xd o f1j)
        (xsq : forall x, Square (xH1 (fiX x)) (xH4 (fjX x))
          (xH2 (fXi x)) (xH3 (fXj x))) : SymP -> P.
      Proof.
        serapply SymP_ind.
        all: try assumption.
        all: try (intro x; apply dp_const; revert x; assumption).
        intro.
        apply ds_const.
        apply xsq.
      Defined.

      Context
        (P : Type)
        (xa : B00 -> P)
        (xb : B10 -> P)
        (xc : B01 -> P)
        (xd : B11 -> P)
        (xH1 : xa o f0i == xc o f0j)
        (xH2 : xa o fi0 == xb o fj0)
        (xH3 : xc o fi1 == xd o fj1)
        (xH4 : xb o f1i == xd o f1j)
        (xsq : forall x, Square (xH1 (fiX x)) (xH4 (fjX x))
          (xH2 (fXi x)) (xH3 (fXj x))).

        Lemma SymP_rec_beta_H1 : forall x, ap (SymP_rec P xH1 xH2 xH3 xH4 xsq)
          (H1 x) = xH1 x.
        Proof.
          intro.
          refine ((moveR_equiv_V _ _ (dp_apD_const _ _))^ @ _).
          apply moveR_equiv_V.
          apply SymP_ind_beta_H1.
        Defined.

        Lemma SymP_rec_beta_H2 : forall x, ap (SymP_rec P xH1 xH2 xH3 xH4 xsq)
          (H2 x) = xH2 x.
        Proof.
          intro.
          refine ((moveR_equiv_V _ _ (dp_apD_const _ _))^ @ _).
          apply moveR_equiv_V.
          apply SymP_ind_beta_H2.
        Defined.

        Lemma SymP_rec_beta_H3 : forall x, ap (SymP_rec P xH1 xH2 xH3 xH4 xsq)
          (H3 x) = xH3 x.
        Proof.
          intro.
          refine ((moveR_equiv_V _ _ (dp_apD_const _ _))^ @ _).
          apply moveR_equiv_V.
          apply SymP_ind_beta_H3.
        Defined.

        Lemma SymP_rec_beta_H4 : forall x, ap (SymP_rec P xH1 xH2 xH3 xH4 xsq)
          (H4 x) = xH4 x.
        Proof.
          intro.
          refine ((moveR_equiv_V _ _ (dp_apD_const _ _))^ @ _).
          apply moveR_equiv_V.
          apply SymP_ind_beta_H4.
        Defined.

        Axiom SymP_rec_beta_sq : forall x,
          Cube (sq_ap (SymP_rec P xH1 xH2 xH3 xH4 xsq) (sq x)) (xsq x)
            (sq_G1 (SymP_rec_beta_H1 (fiX x)))
            (sq_G1 (SymP_rec_beta_H4 (fjX x)))
            (sq_G1 (SymP_rec_beta_H2 (fXi x)))
            (sq_G1 (SymP_rec_beta_H3 (fXj x))).

    End rec.

  End Push.

End SymP.

    Arguments SymP_ind {_ _ _ _ _ _ _ _} _.
    Arguments SymP_rec {_ _ _ _ _ _ _ _} _.
    Arguments a {_ _ _ _}.
    Arguments b {_ _ _ _}.
    Arguments c {_ _ _ _}.
    Arguments d {_ _ _ _}.
    Arguments H1 {_ _ _ _ _}.
    Arguments H2 {_ _ _ _ _}.
    Arguments H3 {_ _ _ _ _}.
    Arguments H4 {_ _ _ _ _}.
    Arguments sq {_ _ _ _ _ _ _ _ _} _.

Require Import HIT.Pushout.
Require Import Types.

Definition pushout_ind_dp {A B C} (f : A -> B) (g : A -> C)
  (P : pushout f g -> Type)
  (pushb : forall b : B, P (pushl b))
  (pushc : forall c : C, P (pushr c))
  (pp' : forall a : A, DPath P (pp a) (pushb (f a)) (pushc (g a)))
  : forall (w : pushout f g), P w.
Proof.
  refine (pushout_ind _ _ _ _ _ _).
  intro a.
  apply dp_path_transport^-1.
  revert a.
  exact pp'.
Defined.

Definition pushout_ind_dp_beta_pp {A B C f g}
  (P : @pushout A B C f g -> Type)
  (pushb : forall b : B, P (push (inl b)))
  (pushc : forall c : C, P (push (inr c)))
  (pp' : forall a : A, DPath P (pp a) (pushb (f a)) (pushc (g a))) (a : A)
  : dp_apD (pushout_ind_dp f g P pushb pushc pp') (pp a) = pp' a.
Proof.
  apply dp_apD_path_transport.
  rewrite pushout_ind_beta_pp.
  reflexivity.
Defined.

Local Open Scope square_scope.


Definition sq_ap_GGGG {A B : Type} {a00 a10 a01 a11 : A} (f : A -> B)
  {px0 px0' : a00 = a10} {px1 px1' : a01 = a11}
  {p0x p0x' : a00 = a01} {p1x p1x' : a10 = a11}
  {qx0 : px0 = px0'} {qx1 : px1 = px1'}
  {q0x : p0x = p0x'} {q1x : p1x = p1x'}
  (s : Square px0 px1 p0x p1x)
  : sq_ap f (sq_GGGG qx0 qx1 q0x q1x s) = sq_GGGG (ap (ap f) qx0)
      (ap (ap f) qx1) (ap (ap f) q0x) (ap (ap f) q1x) (sq_ap f s).
Proof.
  by destruct qx0, qx1, q0x, q1x.
Defined.

Section three.

      Context
      {A00 A10 A01 A11 : Type}
      {A0X : A00 -> A01 -> Type}
      {A1X : A10 -> A11 -> Type}
      {AX0 : A00 -> A10 -> Type}
      {AX1 : A01 -> A11 -> Type}
      (AXX : forall a00 a01 a10 a11,
        A0X a00 a01 ->
        A1X a10 a11 ->
        AX0 a00 a10 ->
        AX1 a01 a11 -> Type).

    Local Definition B00 := A00.
    Local Definition B10 := A10.
    Local Definition B01 := A01.
    Local Definition B11 := A11.

    Local Definition B0X := {a00 : A00 & {a01 : A01 & A0X a00 a01}}.
    Local Definition B1X := {a10 : A10 & {a11 : A11 & A1X a10 a11}}.
    Local Definition BX0 := {a00 : A00 & {a10 : A10 & AX0 a00 a10}}.
    Local Definition BX1 := {a01 : A01 & {a11 : A11 & AX1 a01 a11}}.

    Local Definition BXX := {a00 : A00 & {a01 : A01 & {a10 : A10 & {a11 : A11 &
               {a0X : A0X a00 a01 & {a1X : A1X a10 a11 &
               {aX0 : AX0 a00 a10 & {aX1 : AX1 a01 a11 &
                AXX a00 a01 a10 a11 a0X a1X aX0 aX1}}}}}}}}.

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

  Definition R0 := pushout fi0 fj0.
  Definition RX := pushout fiX fjX.
  Definition R1 := pushout fi1 fj1.

  Definition fi : RX -> R0
    := pushout_rec _ (pushl o f0i) (pushr o f1i) (pp o fXi).
  Definition fj : RX -> R1
    := pushout_rec _ (pushl o f0j) (pushr o f1j) (pp o fXj).
  Definition R := pushout fi fj.

  Definition C0 := pushout f0i f0j.
  Definition CX := pushout fXi fXj.
  Definition C1 := pushout f1i f1j.

  Definition f'i: CX -> C0
    := pushout_rec _ (pushl o fi0) (pushr o fi1) (pp o fiX).
  Definition f'j : CX -> C1
    := pushout_rec _ (pushl o fj0) (pushr o fj1) (pp o fjX).
  Definition C := pushout f'i f'j.

  Definition M := @SymP B00 B10 B01 B11.

  Lemma to : R -> M.
  Proof.
    serapply pushout_rec.
    1: exact (pushout_rec _ a b H2).
    1: exact (pushout_rec _ c d H3).
    erapply pushout_ind_dp.
    intro x.
    apply sq_dp^-1.
    
    shelve.
    Unshelve.
    1,2: intro x.
    1: refine (1 @ (1 @ (1 @ (?[X] @ 1 @ 1 @ 1)))).
    2: refine (1 @ (1 @ (1 @ (?[Y] @ 1 @ 1 @ 1)))).
    1,2: revert x; shelve.
    simpl.
    refine (
      (sq_tr (ap_compose_sq fi _ _))
      @v (sq_concat_v (sq_ap _ (sq_1G _))
      (sq_concat_v (sq_1G _)
        (((_ @v (sq_flip_v (sq_1G _)))
          @v (sq_flip_v (sq_ap _ (sq_1G _))))
          @v (sq_flip_v (sq_tr (ap_compose_sq fj _ _)))))
        (py0 := 1 @ (?X (fiX x) @ 1 @ 1 @ 1))
        (py1 := 1 @ (?Y (fjX x) @ 1 @ 1 @ 1)))).
    all: do 2 try serapply pushout_rec_beta_pp.
    apply sq.
  Defined.

 (* OLD:   serapply pushout_rec.
    1: exact (pushout_rec _ a b H2).
    1: exact (pushout_rec _ c d H3).
    apply (pushout_ind_dp _ _ _ H1 H4).
    intro x.
    apply sq_dp^-1.
    refine (sq_ccGG _^ _^ _).
    1,2: refine (ap_compose _ _ _ @ _).
    1,2: refine (ap _ _ @ _).
    1,3: serapply pushout_rec_beta_pp.
    1,2: serapply pushout_rec_beta_pp.
    exact (sq x). *)

  Lemma from : M -> R.
  Proof.
    serapply (SymP_rec AXX); cbn.
    1: apply (pushl o pushl).
    1: apply (pushl o pushr).
    1: apply (pushr o pushl).
    1: apply (pushr o pushr).
    all: intro x.
    1: exact (pp (pushl x)).
    1,2: apply ap.
    1,2: serapply pp.
    1: exact (pp (pushr x)).
    simpl.
    change (Square
      (pp (f:=fi) (g:=fj) (pushl (fiX x)))
      (pp (f:=fi) (g:=fj) (pushr (fjX x)))
      (ap pushl (pp (f:=fi0) (g:=fj0) (fXi x)))
      (ap pushr (pp (f:=fi1) (g:=fj1) (fXj x)))).
    refine (sq_ccGG _ _ _).
    1,2: refine (ap_compose _ _ _ @ ap _ _).
    1,2: serapply pushout_rec_beta_pp.
    exact (ap_nat' pp (pp x)).
  Defined.
(*
Definition foo (x : BXX)
  : Square (ap to (pp (pushl (fiX x)))) (ap to (pp (pushr (fjX x))))
      (ap to (ap (fun a : pushout fiX fjX => pushl (fi a)) (pp x)))
      (ap to (ap (fun a : pushout fiX fjX => pushr (fj a)) (pp x)))
  <~> Square (H1 (SymP.fiX x)) (H4 (SymP.fjX x)) (H2 (SymP.fXi x))
         (H3 (SymP.fXj x)).
Proof.
  serapply equiv_adjointify.
  { intro; exact (sq x). }
  { intro; exact (


  rewrite ?pushout_rec_beta_pp.
  simpl.
  rewrite (ap_compose fi).
  rewrite (ap_compose fj).
  rewrite <- 2 (ap_compose _ to).
  simpl.
  rewrite ?pushout_rec_beta_pp.
  hott_simpl.
  change (
  Square (H1 (fiX x)) (H4 (fjX x))
  (ap (pushout_rec SymP a b H2) (pp (fXi x)))
  (ap (pushout_rec SymP c d H3) (pp (fXj x))) <~>
Square (H1 (SymP.fiX x)) (H4 (SymP.fjX x)) (H2 (SymP.fXi x)) (H3 (SymP.fXj x))).
  rewrite ?pushout_rec_beta_pp.
  reflexivity.
Defined.

Definition bar {x} : (foo x (sq_ap to (ap_nat' pp (pp x)))) = sq x.
Proof.
  unfold foo.
  simpl.
  cbn.
*)

  Definition sq_GGGG_cu {A : Type} {a00 a10 a01 a11 : A}
    {px0 px0' : a00 = a10} {px1 px1' : a01 = a11}
    {p0x p0x' : a00 = a01} {p1x p1x' : a10 = a11}
    {qx0 : px0 = px0'} {qx1 : px1 = px1'}
    {q0x : p0x = p0x'} {q1x : p1x = p1x'}
    (s : Square px0 px1 p0x p1x)
    : Cube s (sq_GGGG qx0 qx1 q0x q1x s)
      (sq_G1 qx0) (sq_G1 qx1) (sq_G1 q0x) (sq_G1 q1x).
  Proof.
    destruct qx0, qx1, q0x, q1x.
    by destruct s.
  Defined.

  Definition fromto : Sect from to.
  Proof.
    serapply (SymP_ind AXX).
    1,2,3,4: reflexivity.
    1,2,3,4: shelve.
    intro x.
    apply cu_ds^-1.
    
    shelve.
    Unshelve.
    
    1,2,3,4: intro x.
    1,2,3,4: apply sq_dp^-1.
    1,2,3,4: revert x; shelve.
    
    erapply cu_GGGGcc.
    1,2,3,4: symmetry.
    1,2,3,4: apply eisretr.
    
    apply cu_rot_tb_fb.

    shelve.
    Unshelve.
    
    1,2,3,4: intro x.
    1,2,3,4: apply sq_tr^-1.
    1,2,3,4: revert x; shelve.
    
    erapply cu_ccGGGG.
    1,2,3,4: symmetry.
    1,2,3,4: apply eisretr.

    shelve.
    Unshelve.
    
    1,2,3,4: intro x.
    1,2,3,4: refine (sq_concat_h (ap_compose_sq from to _) _ (p0y:=1) (p1y:=1)).
    1,2,3,4: revert x.
    
(*     1,2,3,4: shelve. *)
    1: refine ?[W]; shelve.
    1: refine ?[X]; shelve.
    1: refine ?[Y]; shelve.
    1: refine ?[Z]; shelve.
    
    simpl.
    
    refine (cu_concat_lr (sq_ap_compose from to (sq x)) _
      (sji0:=?W (fiX x)) (sji1:=?Z (fjX x))
      (sj0i:=?X (fXi x)) (sj1i:=?Y (fXj x)) (pj11:=1)).

    shelve.
    Unshelve.
    
    1,2,3,4: intro x.
    1,2,3,4: refine (sq_concat_h (sq_ap to (sq_G1 _)) _ (p0y:=1) (p1y:=1)).
    1: serapply SymP_rec_beta_H1.
    2: serapply SymP_rec_beta_H2.
    3: serapply SymP_rec_beta_H3.
    4: serapply SymP_rec_beta_H4.
    
    1,2,3,4: revert x.
    1: refine ?[W]; shelve.
    1: refine ?[X]; shelve.
    1: refine ?[Y]; shelve.
    1: refine ?[Z]; shelve.
    simpl.
    
    refine (cu_concat_lr (cu_ap to (SymP_rec_beta_sq R (pushl o pushl)
      (pushl o pushr) (pushr o pushl) (pushr o pushr)
      (fun x : SymP.B0X => pp (pushl x)) (fun x : SymP.BX0 => ap pushl (pp x))
      (fun x : SymP.BX1 => ap pushr (pp x)) (fun x : SymP.B1X => pp (pushr x))
      _ _)) _ (sji0:=?W (fiX x)) (sji1:=?Z (fjX x)) (sj0i:=?X (fXi x))
      (sj1i:=?Y (fXj x)) (pj11:=1)).
    simpl.
    
    rewrite sq_ap_GGGG.
    
    shelve.
    Unshelve.
    
    1,2,3,4: intro x.
    
    1: refine (sq_concat_h (sq_flip_h (sq_G1 1)) ?[W1](p0y:=1)(p1y:=1)).
    2: refine (sq_concat_h (sq_flip_h (sq_G1 1)) ?[X1](p0y:=1)(p1y:=1)).
    3: refine (sq_concat_h (sq_flip_h (sq_G1 ?[y])) ?[Y1](p0y:=1)(p1y:=1)).
    5: refine (sq_concat_h (sq_flip_h (sq_G1 ?[z])) ?[Z1](p0y:=1)(p1y:=1)).
    
    1,2,3,4,5,6: revert x; shelve.
    cbv beta.
    
    set (L := (@ap
        (@pushl RX R0 R1 fi fj (@pushl BX0 (@SymP.B00 A00) B10 fi0 fj0 x.1) =
         @pushl RX R0 R1 fi fj
           (@pushr BX0 B00 (@SymP.B10 A10) fi0 fj0 ((x.2).2).1))
        (to (@pushl RX R0 R1 fi fj (@pushl BX0 (@SymP.B00 A00) B10 fi0 fj0 x.1)) =
         to
           (@pushl RX R0 R1 fi fj
              (@pushr BX0 B00 (@SymP.B10 A10) fi0 fj0 ((x.2).2).1)))
        (@ap R M to
           (@pushl RX R0 R1 fi fj (@pushl BX0 (@SymP.B00 A00) B10 fi0 fj0 x.1))
           (@pushl RX R0 R1 fi fj
              (@pushr BX0 B00 (@SymP.B10 A10) fi0 fj0 ((x.2).2).1)))
        (@ap (@pushout BXX B0X B1X fiX fjX) (@pushout RX R0 R1 fi fj)
           (fun x0 : @pushout BXX B0X B1X fiX fjX => @pushl RX R0 R1 fi fj (fi x0))
           (@pushl BXX B0X B1X fiX fjX (fiX x))
           (@pushr BXX B0X B1X fiX fjX (fjX x)) (@pp BXX B0X B1X fiX fjX x))
        (@ap (@pushout BX0 B00 B10 fi0 fj0)
           (@pushout RX (@pushout BX0 B00 B10 fi0 fj0) R1 fi fj)
           (@pushl RX (@pushout BX0 B00 B10 fi0 fj0) R1 fi fj)
           (@pushl BX0 B00 B10 fi0 fj0 x.1)
           (@pushr BX0 B00 B10 fi0 fj0 (fj0 (fXi x)))
           (@pp BX0 B00 B10 fi0 fj0 (fXi x)))
        (@ap_compose (@pushout BXX B0X B1X fiX fjX) R0 
           (@pushout RX R0 R1 fi fj) fi (@pushl RX R0 R1 fi fj)
           (@pushl BXX B0X B1X fiX fjX (fiX x))
           (@pushr BXX B0X B1X fiX fjX (fjX x)) (@pp BXX B0X B1X fiX fjX x) @
         @ap
           (@pushl BX0 B00 B10 fi0 fj0 x.1 =
            @pushr BX0 B00 B10 fi0 fj0 ((x.2).2).1)
           (@pushl RX R0 R1 fi fj (@pushl BX0 B00 B10 fi0 fj0 x.1) =
            @pushl RX R0 R1 fi fj (@pushr BX0 B00 B10 fi0 fj0 ((x.2).2).1))
           (@ap R0 (@pushout RX R0 R1 fi fj) (@pushl RX R0 R1 fi fj)
              (@pushl BX0 B00 B10 fi0 fj0 x.1)
              (@pushr BX0 B00 B10 fi0 fj0 ((x.2).2).1))
           (@ap (@pushout BXX B0X B1X fiX fjX) R0 fi
              (@pushl BXX B0X B1X fiX fjX (fiX x))
              (@pushr BXX B0X B1X fiX fjX (fjX x)) (@pp BXX B0X B1X fiX fjX x))
           (@pp BX0 B00 B10 fi0 fj0 (fXi x))
           (@pushout_rec_beta_pp BXX B0X B1X fiX fjX R0
              (fun x0 : B0X => @pushl BX0 B00 B10 fi0 fj0 (f0i x0))
              (fun x0 : B1X => @pushr BX0 B00 B10 fi0 fj0 (f1i x0))
              (fun x0 : BXX => @pp BX0 B00 B10 fi0 fj0 (fXi x0)) x)))).
    set (Q := (@ap
        (@pushr RX R0 R1 fi fj
           (@pushl BX1 (@SymP.B01 A01) B11 fi1 fj1
              (@SymP.f0j A00 A01 A0X
                 (@SymP.fiX A00 A10 A01 A11 A0X A1X AX0 AX1 AXX x))) =
         @pushr RX R0 R1 fi fj
           (@pushr BX1 B01 (@SymP.B11 A11) fi1 fj1
              (@SymP.f1j A10 A11 A1X
                 (@SymP.fjX A00 A10 A01 A11 A0X A1X AX0 AX1 AXX x))))
        (to
           (@pushr RX R0 R1 fi fj
              (@pushl BX1 (@SymP.B01 A01) B11 fi1 fj1
                 (@SymP.f0j A00 A01 A0X
                    (@SymP.fiX A00 A10 A01 A11 A0X A1X AX0 AX1 AXX x)))) =
         to
           (@pushr RX R0 R1 fi fj
              (@pushr BX1 B01 (@SymP.B11 A11) fi1 fj1
                 (@SymP.f1j A10 A11 A1X
                    (@SymP.fjX A00 A10 A01 A11 A0X A1X AX0 AX1 AXX x)))))
        (@ap R M to
           (@pushr RX R0 R1 fi fj
              (@pushl BX1 (@SymP.B01 A01) B11 fi1 fj1
                 (@SymP.f0j A00 A01 A0X
                    (@SymP.fiX A00 A10 A01 A11 A0X A1X AX0 AX1 AXX x))))
           (@pushr RX R0 R1 fi fj
              (@pushr BX1 B01 (@SymP.B11 A11) fi1 fj1
                 (@SymP.f1j A10 A11 A1X
                    (@SymP.fjX A00 A10 A01 A11 A0X A1X AX0 AX1 AXX x)))))
        (@ap (@pushout BXX B0X B1X fiX fjX) (@pushout RX R0 R1 fi fj)
           (fun x0 : @pushout BXX B0X B1X fiX fjX => @pushr RX R0 R1 fi fj (fj x0))
           (@pushl BXX B0X B1X fiX fjX (fiX x))
           (@pushr BXX B0X B1X fiX fjX (fjX x)) (@pp BXX B0X B1X fiX fjX x))
        (@ap (@pushout BX1 B01 B11 fi1 fj1)
           (@pushout RX R0 (@pushout BX1 B01 B11 fi1 fj1) fi fj)
           (@pushr RX R0 (@pushout BX1 B01 B11 fi1 fj1) fi fj)
           (@pushl BX1 B01 B11 fi1 fj1 (x.2).1)
           (@pushr BX1 B01 B11 fi1 fj1 (fj1 (fXj x)))
           (@pp BX1 B01 B11 fi1 fj1 (fXj x)))
        (@ap_compose (@pushout BXX B0X B1X fiX fjX) R1 
           (@pushout RX R0 R1 fi fj) fj (@pushr RX R0 R1 fi fj)
           (@pushl BXX B0X B1X fiX fjX (fiX x))
           (@pushr BXX B0X B1X fiX fjX (fjX x)) (@pp BXX B0X B1X fiX fjX x) @
         @ap
           (@pushl BX1 B01 B11 fi1 fj1 (f0j (fiX x)) =
            @pushr BX1 B01 B11 fi1 fj1 (f1j (fjX x)))
           (@pushr RX R0 R1 fi fj (@pushl BX1 B01 B11 fi1 fj1 (f0j (fiX x))) =
            @pushr RX R0 R1 fi fj (@pushr BX1 B01 B11 fi1 fj1 (f1j (fjX x))))
           (@ap R1 (@pushout RX R0 R1 fi fj) (@pushr RX R0 R1 fi fj)
              (@pushl BX1 B01 B11 fi1 fj1 (f0j (fiX x)))
              (@pushr BX1 B01 B11 fi1 fj1 (f1j (fjX x))))
           (@ap (@pushout BXX B0X B1X fiX fjX) R1 fj
              (@pushl BXX B0X B1X fiX fjX (fiX x))
              (@pushr BXX B0X B1X fiX fjX (fjX x)) (@pp BXX B0X B1X fiX fjX x))
           (@pp BX1 B01 B11 fi1 fj1 (fXj x))
           (@pushout_rec_beta_pp BXX B0X B1X fiX fjX R1
              (fun x0 : B0X => @pushl BX1 B01 B11 fi1 fj1 (f0j x0))
              (fun x0 : B1X => @pushr BX1 B01 B11 fi1 fj1 (f1j x0))
              (fun x0 : BXX => @pp BX1 B01 B11 fi1 fj1 (fXj x0)) x)))).
    
    change (Cube
  (sq_GGGG 1 1 L Q
     (sq_ap to (ap_nat' pp (pp x)))) (sq_ap idmap (sq x))
  ((fun x0 : SymP.B0X => (sq_flip_h (sq_G1 1)) @h (?W1 x0)) (fiX x))
  ((fun x0 : SymP.B1X => (sq_flip_h (sq_G1 (?z x0))) @h (?Z1 x0)) (fjX x))
  ((fun x0 : SymP.BX0 => (sq_flip_h (sq_G1 1)) @h (?X1 x0)) (fXi x))
  ((fun x0 : SymP.BX1 => (sq_flip_h (sq_G1 (?y x0))) @h (?Y1 x0)) (fXj x))).
    cbv beta.
    
    (*
    refine (cu_concat_lr
      (cu_flip_lr (sq_GGGG_cu (sq_ap to (ap_nat' pp (pp x)))
      (qx0:=1) (qx1:=1) (q0x:=L) (q1x:=Q))) _
        (sji0 := ?W1 (fiX x)) (sji1 := ?Z1 (fjX x)) (sj0i := ?X1 (fXi x)) (sj1i := ?Y1 (fXj x))).
      
    refine (cu_concat_lr
      (cu_flip_lr (sq_GGGG_cu (sq_ap to (ap_nat' pp (pp x)))
      (qx0:=1) (qx1:=1))) _ (sji0 := ?W1 (fiX x)) (sji1 := ?Z1 (fjX x)) (sj0i := ?X1 (fXi x)) (sj1i := ?Y1 (fXj x))). *)
  Admitted.

  Definition tofrom : Sect to from.
  Proof.
    erapply pushout_ind_dp.
    intro x.
    apply sq_dp^-1.
    apply sq_tr^-1.
    revert x.
    erapply pushout_ind_dp.
    intro x.
    apply cu_dp.
    
    shelve.
    Unshelve.
    
    1,2: serapply pushout_ind_dp.
    1,2,4,5: reflexivity.
    all: simpl.
    1: refine ?[W]; shelve.
    1: refine ?[X]; shelve.
    1: refine ?[Y]; shelve.
    1: refine ?[Z]; shelve.
    
    apply cu_rot_tb_fb.
    
    simpl.
  
    
  
  Admitted.

  Definition foo : R <~> M := equiv_adjointify to from fromto tofrom.

