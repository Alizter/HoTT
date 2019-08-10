Require Import Basics.

Section Dep.

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

Require Import HIT.Pushout.
Require Import Types.
Require Import Cubical.

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
  unfold pushout_ind_sq.
  unfold sq_apd'.
  simpl. (* Going to need some helper lemmas with sq_apd' before we can finish *)
Admitted.

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

  Theorem pushout3x3 : R <~> C.
  Proof.
    serapply equiv_adjointify.
    { serapply pushout_rec.
      { serapply pushout_rec.
        1: exact (pushl o pushl).
        1: exact (pushr o pushl).
        exact (pp o pushl). }
      { serapply pushout_rec.
        1: exact (pushl o pushr).
        1: exact (pushr o pushr).
        exact (pp o pushr). }
      { serapply pushout_ind_sq.
        1: exact (fun a => ap pushl (pp a)).
        1: exact (fun a => ap pushr (pp a)).
        intros [a00 [a01 [a10 [a11 [a0x [a1x [ax0 [ax1 axx]]]]]]]].
        (* Reduce aps *)
        cbn.
        rewrite (ap_compose fi).
        rewrite pushout_rec_beta_pp.
        
        rewrite (ap_compose fj).
        rewrite (pushout_rec_beta_pp _ _ _ _ a).
        optimize_heap.
        rewrite (pushout_rec_beta_pp _ _ _ _ a).
        
        destruct a as [a00 [a01 [a10 [a11 [a0x [a1x [ax0 [ax1 axx]]]]]]]].
        optimize_heap.
        rewrite (pushout_rec_beta_pp _ _ _ _ (a00; a10; ax0)).  
        rewrite (pushout_rec_beta_pp _ _ _ _ (pushl x)).
        rewrite (pushout_rec_beta_pp _ _ _ _ a).
        rewrite pushout_rec_beta_pp.
        
        
      refine (transport (fun x => Square _ _ x _) (ap_compose f'ix _ _)^ _).
      refine (transport (fun x => Square _ _ _ x) (ap_compose fjX _ _)^ _).
      (* beta reduce recursion, this gives us Kan fillers *)
      refine (transport (fun x => Square _ _ (ap _ x) _) (pushout_rec_beta_pp _
        (fun x => pushl (fi0 x)) (fun x => pushr (fi2 x)) _ _)^ _).
      refine (transport (fun x => Square _ _ _ (ap _ x)) (pushout_rec_beta_pp _
        (fun x => pushl (fj0 x)) (fun x => pushr (fj2 x)) _ _)^ _).
      (* We move aps into the Kans *)
      refine (transport (fun x => Square _ _ x _) (ap_kan _)^ _).
      refine (transport (fun x => Square _ _ _ x) (ap_kan _)^ _).
      (* Reduce some terms *)
      refine (transport (fun x => Square _ _ (Kan x _ _) _) (pushout_rec_beta_pp _
        (fun x => pushl (pushl x)) (fun x => pushr (pushl x)) _ _)^ _).
      refine (transport (fun x => Square _ _ _ (Kan x _ _)) (pushout_rec_beta_pp _
        (fun x => pushl (pushr x)) (fun x => pushr (pushr x)) _ _)^ _).
      (* We apply a coherance lemma so we can give a different filler *)
      refine (transport idmap sq_ppkan'^ _).
      (* Now we must tidy up the aps *)
      refine (transport (fun x => Square (Kan _ x^ _) _ _ _) (ap_compose _ _ _) _).
      refine (transport (fun x => Square (Kan _ _ x^) _ _ _) (ap_compose _ _ _) _).
      refine (transport (fun x => Square _ (Kan _ x^ _) _ _) (ap_compose _ _ _) _).
      refine (transport (fun x => Square _ (Kan _ _ x^) _ _) (ap_compose _ _ _) _).
      simpl.
      (* Tidy up kans *)
      refine (transport (fun x => Square (Kan _ x^ _) _ _ _)
        (ap_compose pushl _ _)^ _).
      refine (transport (fun x => Square (Kan _ _ x^) _ _ _)
        (ap_compose pushr _ _)^ _).
      refine (transport (fun x => Square _ (Kan _ x^ _) _ _)
        (ap_compose pushl _ _)^ _).
      refine (transport (fun x => Square _ (Kan _ _ x^) _ _)
        (ap_compose pushr _ _)^ _).
      (* Move inverses out *)
      refine (transport (fun x => Square (Kan _ x _) _ _ _) (ap_V _ _) _).
      refine (transport (fun x => Square (Kan _ _ x) _ _ _) (ap_V _ _) _).
      refine (transport (fun x => Square _ (Kan _ x _) _ _) (ap_V _ _) _).
      refine (transport (fun x => Square _ (Kan _ _ x) _ _) (ap_V _ _) _).
      (* Move aps out of kans *)
      refine (transport (fun x => Square x _ _ _) (ap_kan _) _).
      refine (transport (fun x => Square _ x _ _) (ap_kan _) _).
     (* Unreducing fiX and fjX *)
     refine (transport (fun x => Square (ap pushl x) _ _ _)
      (pushout_rec_beta_pp _ (pushl o f0i)
        (pushr o f2i) (fun a => Kan (pp (f1i a))
          (ap pushl (H00 a))^ (ap pushr (H20 a))^) a) _).
     refine (transport (fun x => Square _ (ap pushr x) _ _)
      (pushout_rec_beta_pp _ (pushl o f0j)
        (pushr o f2j) (fun a => Kan (pp (f1j a))
          (ap pushl (H02 a))^ (ap pushr (H22 a))^) a) _).
      (* Recomposing the aps *)
      refine (transport (fun x => Square x _ _ _) (ap_compose fXi _ (pp a)) _).
      refine (transport (fun x => Square _ x _ _) (ap_compose fXj _ (pp a)) _).
      (* We can finally apply our filler *)
      exact (sq_apd _ (pp a)).




