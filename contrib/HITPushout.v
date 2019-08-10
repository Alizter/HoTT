Require Import Basics.
Require Import Cubical.

Module Export SymP.

  Section Push.
    Context
      {A00 A10 A01 A11 : Type}
      {A0x : A00 -> A01 -> Type}
      {A1x : A10 -> A11 -> Type}
      {Ax0 : A00 -> A10 -> Type}
      {Ax1 : A01 -> A11 -> Type}
      (Axx : forall a00 a01 a10 a11,
        A0x a00 a01 ->
        A1x a10 a11 ->
        Ax0 a00 a10 ->
        Ax1 a01 a11 -> Type).

  Local Definition B00 := A00.
  Local Definition B10 := A10.
  Local Definition B01 := A01.
  Local Definition B11 := A11.

  Local Definition B0x := {a00 : A00 & {a01 : A01 & A0x a00 a01}}.
  Local Definition B1x := {a10 : A10 & {a11 : A11 & A1x a10 a11}}.
  Local Definition Bx0 := {a00 : A00 & {a10 : A10 & Ax0 a00 a10}}.
  Local Definition Bx1 := {a01 : A01 & {a11 : A11 & Ax1 a01 a11}}.

  Local Definition Bxx := {a00 : A00 & {a01 : A01 & {a10 : A10 & {a11 : A11 &
             {a0x : A0x a00 a01 & {a1x : A1x a10 a11 &
             {ax0 : Ax0 a00 a10 & {ax1 : Ax1 a01 a11 &
              Axx a00 a01 a10 a11 a0x a1x ax0 ax1}}}}}}}}.

  Local Definition fi0 : Bx0 -> B00 := pr1.
  Local Definition fj0 : Bx0 -> B10 := fun x => pr1 (pr2 x).

  Local Definition f'ix : Bxx -> B0x := fun a => (a.1; a.2.1; a.2.2.2.2.1).
  Local Definition fjx : Bxx -> B1x := fun a => (a.2.2.1; a.2.2.2.1; a.2.2.2.2.2.1).

  Local Definition fi1 : Bx1 -> B01 := pr1.
  Local Definition fj1 : Bx1 -> B11 := fun x => pr1 (pr2 x).
  
  Local Definition f0i : B0x -> B00 := pr1.
  Local Definition f0j : B0x -> B01 := fun x => pr1 (pr2 x).
  
  Local Definition fxi : Bxx -> Bx0 := fun a => (a.1; a.2.2.1; a.2.2.2.2.2.2.1).
  Local Definition fxj : Bxx -> Bx1 := fun a => (a.2.1; a.2.2.2.1; a.2.2.2.2.2.2.2.1).

  Local Definition f1i : B1x -> B10 := pr1.
  Local Definition f1j : B1x -> B11 := fun x => pr1 (pr2 x).

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
        Square (H1 (f'ix x)) (H4 (fjx x)) (H2 (fxi x)) (H3 (fxj x)).

    Section ind.

      Definition SymP_ind (P : SymP -> Type)
        {xa : forall x, P (a x)}
        {xb : forall x, P (b x)}
        {xc : forall x, P (c x)}
        {xd : forall x, P (d x)}
        (Q1 : forall x, dpath P (H1 x) (xa (f0i x)) (xc (f0j x)))
        (Q2 : forall x, dpath P (H2 x) (xa (fi0 x)) (xb (fj0 x)))
        (Q3 : forall x, dpath P (H3 x) (xc (fi1 x)) (xd (fj1 x)))
        (Q4 : forall x, dpath P (H4 x) (xb (f1i x)) (xd (f1j x)))
        (xsq : forall x, SquareOver P (sq x)
          (Q1 (f'ix x)) (Q4 (fjx x)) (Q2 (fxi x)) (Q3 (fxj x))) (s : SymP) : P s.
      Proof.
        destruct s; (apply xa || apply xb || apply xc || apply xd).
      Defined.

      Context
        (P : SymP -> Type)
        {xa : forall x, P (a x)}
        {xb : forall x, P (b x)}
        {xc : forall x, P (c x)}
        {xd : forall x, P (d x)}
        (Q1 : forall x, dpath P (H1 x) (xa (f0i x)) (xc (f0j x)))
        (Q2 : forall x, dpath P (H2 x) (xa (fi0 x)) (xb (fj0 x)))
        (Q3 : forall x, dpath P (H3 x) (xc (fi1 x)) (xd (fj1 x)))
        (Q4 : forall x, dpath P (H4 x) (xb (f1i x)) (xd (f1j x)))
        (xsq : forall x, SquareOver P (sq x)
          (Q1 (f'ix x)) (Q4 (fjx x)) (Q2 (fxi x)) (Q3 (fxj x))).

      Axiom SymP_ind_beta_H1 : forall x, apD (SymP_ind P Q1 Q2 Q3 Q4 xsq)
        (H1 x) = Q1 x.
      Axiom SymP_ind_beta_H2 : forall x, apD (SymP_ind P Q1 Q2 Q3 Q4 xsq)
        (H2 x) = Q2 x.
      Axiom SymP_ind_beta_H3 : forall x, apD (SymP_ind P Q1 Q2 Q3 Q4 xsq)
        (H3 x) = Q3 x.
      Axiom SymP_ind_beta_H4 : forall x, apD (SymP_ind P Q1 Q2 Q3 Q4 xsq)
        (H4 x) = Q4 x.

      Axiom SymP_ind_beta_sq : forall x, path_SquareOver
        (SymP_ind_beta_H1 (f'ix x))
        (SymP_ind_beta_H4 (fjx x))
        (SymP_ind_beta_H2 (fxi x))
        (SymP_ind_beta_H3 (fxj x))
        (sq_apD (SymP_ind P Q1 Q2 Q3 Q4 xsq) (sq x)) (xsq x).

    End ind.

    Section rec.

       Lemma SymP_rec (P : Type)
        {xa : B00 -> P}
        {xb : B10 -> P}
        {xc : B01 -> P}
        {xd : B11 -> P}
        (xH1 : xa o f0i == xc o f0j)
        (xH2 : xa o fi0 == xb o fj0)
        (xH3 : xc o fi1 == xd o fj1)
        (xH4 : xb o f1i == xd o f1j)
        (xsq : forall x, Square (xH1 (f'ix x)) (xH4 (fjx x))
          (xH2 (fxi x)) (xH3 (fxj x)))
          : SymP -> P.
      Proof.
        srefine (SymP_ind (fun _ => P) _ _ _ _ _); cbn; try assumption;
        try (unfold dpath; intro; refine (transport_const _ _ @ _);
        (apply xH1 || apply xH2 || apply xH3 || apply xH4)).
        intro.
        apply SquareOver_const.
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
        (xsq : forall x, Square (xH1 (f'ix x)) (xH4 (fjx x))
          (xH2 (fxi x)) (xH3 (fxj x))).


        Lemma SymP_rec_beta_H1 : forall x, ap (SymP_rec P xH1 xH2 xH3 xH4 xsq)
          (H1 x) = xH1 x.
        Proof.
          intro.
          rewrite <- (moveR_Vp _ _ _ (apD_const _ _)).
          rewrite SymP_ind_beta_H1.
          by apply moveR_Vp.
        Defined.

        Lemma SymP_rec_beta_H2 : forall x, ap (SymP_rec P xH1 xH2 xH3 xH4 xsq)
          (H2 x) = xH2 x.
        Proof.
          intro.
          rewrite <- (moveR_Vp _ _ _ (apD_const _ _)).
          rewrite SymP_ind_beta_H2.
          by apply moveR_Vp.
        Defined.

        Lemma SymP_rec_beta_H3 : forall x, ap (SymP_rec P xH1 xH2 xH3 xH4 xsq)
          (H3 x) = xH3 x.
        Proof.
          intro.
          rewrite <- (moveR_Vp _ _ _ (apD_const _ _)).
          rewrite SymP_ind_beta_H3.
          by apply moveR_Vp.
        Defined.

        Lemma SymP_rec_beta_H4 : forall x, ap (SymP_rec P xH1 xH2 xH3 xH4 xsq)
          (H4 x) = xH4 x.
        Proof.
          intro.
          rewrite <- (moveR_Vp _ _ _ (apD_const _ _)).
          rewrite SymP_ind_beta_H4.
          by apply moveR_Vp.
        Defined.
(* 
        Context {x:Bxx}.
        Lemma SymP_rec_beta_sq x : 
       Square (ap (SymP_rec P xH1 xH2 xH3 xH4 xsq) (H1 (f'ix x))) 
         (xH1 (f'ix x)) ?pi00 ?pi10 ->
       Square (ap (SymP_rec P xH1 xH2 xH3 xH4 xsq) (H4 (fjx x))) 
         (xH4 (fjx x)) ?pi01 ?pi11 ->
       Square (ap (SymP_rec P xH1 xH2 xH3 xH4 xsq) (H2 (fxi x))) 
         (xH2 (fxi x)) ?pi00 ?pi01 ->
       Square (ap (SymP_rec P xH1 xH2 xH3 xH4 xsq) (H3 (fxj x))) 
         (xH3 (fxj x)) ?pi10 ?pi11 ->
          Cube (sq_ap (SymP_rec P xH1 xH2 xH3 xH4 xsq) (sq x)) (xsq x).
           *)

    End rec.

  End Push.

End SymP.

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

Section three.

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

     Local Definition B00 := A00.
  Local Definition B10 := A10.
  Local Definition B01 := A01.
  Local Definition B11 := A11.

  Local Definition B0x := {a00 : A00 & {a01 : A01 & A0x a00 a01}}.
  Local Definition B1x := {a10 : A10 & {a11 : A11 & A1x a10 a11}}.
  Local Definition Bx0 := {a00 : A00 & {a10 : A10 & Ax0 a00 a10}}.
  Local Definition Bx1 := {a01 : A01 & {a11 : A11 & Ax1 a01 a11}}.

  Local Definition Bxx := {a00 : A00 & {a01 : A01 & {a10 : A10 & {a11 : A11 &
             {a0x : A0x a00 a01 & {a1x : A1x a10 a11 &
             {ax0 : Ax0 a00 a10 & {ax1 : Ax1 a01 a11 &
              Axx a00 a01 a10 a11 a0x a1x ax0 ax1}}}}}}}}.

  Local Definition fi0 : Bx0 -> B00 := pr1.
  Local Definition fj0 : Bx0 -> B10 := fun x => pr1 (pr2 x).

  Local Definition f'ix : Bxx -> B0x := fun a => (a.1; a.2.1; a.2.2.2.2.1).
  Local Definition fjx : Bxx -> B1x := fun a => (a.2.2.1; a.2.2.2.1; a.2.2.2.2.2.1).

  Local Definition fi1 : Bx1 -> B01 := pr1.
  Local Definition fj1 : Bx1 -> B11 := fun x => pr1 (pr2 x).
  
  Local Definition f0i : B0x -> B00 := pr1.
  Local Definition f0j : B0x -> B01 := fun x => pr1 (pr2 x).
  
  Local Definition fxi : Bxx -> Bx0 := fun a => (a.1; a.2.2.1; a.2.2.2.2.2.2.1).
  Local Definition fxj : Bxx -> Bx1 := fun a => (a.2.1; a.2.2.2.1; a.2.2.2.2.2.2.2.1).

  Local Definition f1i : B1x -> B10 := pr1.
  Local Definition f1j : B1x -> B11 := fun x => pr1 (pr2 x).

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

  Definition M := @SymP B00 B10 B01 B11.

(* Here is a special case of pushout_ind where we have path family *)
Definition pushout_ind_sq {A B C D} (f : A -> B) (g : A -> C)
  (h : pushout f g -> D) (i : pushout f g -> D)
  (pushb : forall b : B, h (pushl b) = i (pushl b))
  (pushc : forall c : C, h (pushr c) = i (pushr c))
  (pp' : forall a : A,
    Square (pushb (f a)) (pushc (g a)) (ap h (pp a)) (ap i (pp a)))
  : h == i.
Proof.
  serapply (pushout_ind _ _ _ pushb pushc).
  intro a.
  refine (transport (fun x => x = _) (transport_paths_FlFr (pp a) _)^ _).
  refine (transport (fun x => x = _) (concat_pp_p _ _ _)^ _).
  apply moveR_Mp.
  refine (transport (fun x => _ = x @ _) (inv_V _)^ _).
  exact (sq_to_concat (pp' a)).
Defined.

Definition pushout_ind_sq_beta_pp {A B C D f g}
  {h : pushout f g -> D} {i : pushout f g -> D}
  (pushb : forall b : B, h (pushl b) = i (pushl b))
  (pushc : forall c : C, h (pushr c) = i (pushr c))
  (pp' : forall a : A, Square (pushb (f a)) (pushc (g a)) (ap h (pp a)) (ap i (pp a)))
  (a : A)
  : sq_apd' (pushout_ind_sq f g h i pushb pushc pp') (pp a) = (pp' a).
Proof.
  unfold sq_apd'.
  
  unfold sq_apd'.
  cbn.
  unfold pushout_ind_sq.
  unfold pushout_ind_sq.
  simpl. (* Going to need some helper lemmas with sq_apd' before we can finish *)
Admitted.

  Optimize Proof.
  Optimize Heap.

  Lemma to : R -> M.
  Proof.
    serapply pushout_rec.
    1: exact (pushout_rec _ a b H2).
    1: exact (pushout_rec _ c d H3).
    apply (pushout_ind_sq _ _ _ _ H1 H4).
    intro x.
    refine (transport (fun x => Square _ _ x _) _ _).
    1: symmetry; apply ap_compose.
    refine (transport (fun x => Square _ _ _ x) _ _).
    1: symmetry; apply ap_compose.
    refine (transport (fun x => Square _ _ (ap _ x) _) _ _).
    1: symmetry; apply pushout_rec_beta_pp.
    refine (transport (fun x => Square _ _ _ (ap _ x)) _ _).
    1: symmetry; apply pushout_rec_beta_pp.
    refine (transport (fun x => Square _ _ x _) _ _).
    1: symmetry; apply (pushout_rec_beta_pp SymP a b H2 (fxi x)).
    refine (transport (fun x => Square _ _ _ x) _ _).
    1: symmetry; apply (pushout_rec_beta_pp SymP c d H3 (fxj x)).
    apply sq.
  Defined.

(* Lemma foo A {a b c d : A} {p : a = b} {q : c = d} {r : a = c} {s : b = d}
  {pq : p = q} {rs : r = s} : Square p q r s.  *)
  
(*   Definition foobar {A B} {f f' : A -> B} (h h' : f == f') (hh' : h = h') {x y : A} (p q : x = y) (pq : p = q)
  : Square (h x) (h' y) (ap f p) (ap f' q).
Proof.
  destruct pq, p.
  apply sq_G1, (apD10 hh').
Defined.
 *)
  Lemma from : M -> R.
  Proof.
    serapply (SymP_rec Axx); cbn.
    1: apply (pushl o pushl).
    1: apply (pushl o pushr).
    1: apply (pushr o pushl).
    1: apply (pushr o pushr).
    + intro x; exact (pp (pushl x)).
    + intro x; apply ap, pp.
    + intro x; apply ap, pp.
    + intro x; exact (pp (pushr x)).
    + intro.
      cbn.
      unfold SymP.fxi.
      
      sq_apd
      apply concat_to_sq.
      
(*       pushout_ind_sq_beta_pp *)
(*       apply foobar. *)
(*       apply sq_apd'. *)
(*       unfold Square. *)
  Admitted.

  Lemma foo : R <~> M.
  Proof.
    serapply equiv_adjointify.
    + apply to.
    + apply from.
    + admit.
(*       serapply (SymP_ind Axx). *)
    + serapply pushout_ind_sq.
      { serapply pushout_ind_sq.
        { intro.
          admit. }
       intro.
      unfold to.

