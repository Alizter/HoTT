Require Import Basics.
Require Import Types.
Require Import HIT.Pushout.
Require Import Cubical.Square.


Section Pushout3x3.
  (* 3x3 lemma in G. Brunerie's thesis: *)

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

(** 
   The pushout of the pushouts of the coloumns
   is equivalent to
   the pushout of the pushouts of the rows.
*)

  Context

  (* Types *)
  { A00 A01 A02
    A10 A11 A12
    A20 A21 A22 : Type }

  (* Maps *)
  { f0i : A01 -> A00 } { fi0 : A10 -> A00 }
  { f0j : A01 -> A02 } { fj0 : A10 -> A20 }
  { f1i : A11 -> A10 } { fi1 : A11 -> A01 }
  { f1j : A11 -> A12 } { fj1 : A11 -> A21 }
  { f2i : A21 -> A20 } { fi2 : A12 -> A02 }
  { f2j : A21 -> A22 } { fj2 : A12 -> A22 }

  (* Fillers (Labelled by outer corners) *)
  { H00 : (f0i o fi1) == (fi0 o f1i) }
  { H02 : (f0j o fi1) == (fi2 o f1j) }
  { H20 : (f2i o fj1) == (fj0 o f1i) }
  { H22 : (f2j o fj1) == (fj2 o f1j) }.


(* Pushing out the rows *)
Definition fiX : pushout f1i f1j -> pushout f0i f0j.
Proof.
  serapply pushout_rec.
  + exact (pushl o fi0).
  + exact (pushr o fi2).
  + intro a.
    exact (Kan (pp _)
            (ap pushl (H00 a))
            (ap pushr (H02 a))).
Defined.

Definition fjX : pushout f1i f1j -> pushout f2i f2j.
Proof.
  serapply pushout_rec.
  + exact (pushl o fj0).
  + exact (pushr o fj2).
  + intro a.
    exact (Kan (pp _)
            (ap pushl (H20 a))
            (ap pushr (H22 a))).
Defined.

(* Pushing out the coloumns *)
Definition fXi : pushout fi1 fj1 -> pushout fi0 fj0.
Proof.
  serapply pushout_rec.
  + exact (pushl o f0i).
  + exact (pushr o f2i).
  + intro a.
    exact (Kan (pp _)
            (ap pushl (H00 a))^
            (ap pushr (H20 a))^).
Defined.

Definition fXj : pushout fi1 fj1 -> pushout fi2 fj2.
Proof.
  serapply pushout_rec.
  + exact (pushl o f0j).
  + exact (pushr o f2j).
  + intro a.
    exact (Kan (pp _)
            (ap pushl (H02 a))^
            (ap pushr (H22 a))^).
Defined.

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

Lemma ap_V_square : Type.
Admitted.

Definition to : pushout fXi fXj -> pushout fiX fjX.
Proof.
  serapply pushout_rec.
  + serapply pushout_rec.
    * exact (pushl o pushl).
    * exact (pushr o pushl).
    * exact (pp o pushl).
  + serapply pushout_rec.
    * exact (pushl o pushr).
    * exact (pushr o pushr).
    * exact (pp o pushr).
  + serapply pushout_ind_sq.
    * exact (fun a => ap pushl (pp a)).
    * exact (fun a => ap pushr (pp a)).
    * intro a.
      (* Decompose aps *)
      refine (transport (fun x => Square _ _ x _) (ap_compose fXi _ _)^ _).
      refine (transport (fun x => Square _ _ _ x) (ap_compose fXj _ _)^ _).
      (* beta reduce recursion, this gives us Kan fillers *)
      refine (transport (fun x => Square _ _ (ap _ x) _) (pushout_rec_beta_pp _
        (fun x => pushl (f0i x)) (fun x => pushr (f2i x)) _ _)^ _).
      refine (transport (fun x => Square _ _ _ (ap _ x)) (pushout_rec_beta_pp _
        (fun x => pushl (f0j x)) (fun x => pushr (f2j x)) _ _)^ _).
      (* We move aps into the Kans *)
      refine (transport (fun x => Square _ _ x _) (ap_kan _)^ _).
      refine (transport (fun x => Square _ _ _ x) (ap_kan _)^ _).
      (* Beta reduce first arguments of kans *)
      refine (transport (fun x => Square _ _ (Kan x _ _) _) (pushout_rec_beta_pp _
        (fun x => pushl (pushl x)) (fun x => pushr (pushl x)) _ _)^ _).
      refine (transport (fun x => Square _ _ _ (Kan x _ _)) (pushout_rec_beta_pp _
        (fun x => pushl (pushr x)) (fun x => pushr (pushr x)) _ _)^ _).
      (* Take inverses out of aps *)
      refine (transport (fun x => Square _ _ (Kan _ x _) _) (ap_V _ _)^ _).
      refine (transport (fun x => Square _ _ (Kan _ _ x) _) (ap_V _ _)^ _).
      refine (transport (fun x => Square _ _ _ (Kan _ x _)) (ap_V _ _)^ _).
      refine (transport (fun x => Square _ _ _ (Kan _ _ x)) (ap_V _ _)^ _).
      (* We apply a coherance lemma so we can give a different filler *)
      refine (transport idmap sq_ppkan _).
      (* Now we must tidy up the aps *)
      refine (transport (fun x => Square (Kan _ x _) _ _ _) (ap_compose _ _ _) _).
      refine (transport (fun x => Square (Kan _ _ x) _ _ _) (ap_compose _ _ _) _).
      refine (transport (fun x => Square _ (Kan _ x _) _ _) (ap_compose _ _ _) _).
      refine (transport (fun x => Square _ (Kan _ _ x) _ _) (ap_compose _ _ _) _).
      simpl.
      (* Tidy up kans *)
      refine (transport (fun x => Square (Kan _ x _) _ _ _)
        (ap_compose pushl _ _)^ _).
      refine (transport (fun x => Square (Kan _ _ x) _ _ _)
        (ap_compose pushr _ _)^ _).
      refine (transport (fun x => Square _ (Kan _ x _) _ _)
        (ap_compose pushl _ _)^ _).
      refine (transport (fun x => Square _ (Kan _ _ x) _ _)
        (ap_compose pushr _ _)^ _).
      refine (transport (fun x => Square x _ _ _) (ap_kan _) _).
      refine (transport (fun x => Square _ x _ _) (ap_kan _) _).
     (* Unreducing fiX and fjX *)
     refine (transport (fun x => Square (ap pushl x) _ _ _)
      (pushout_rec_beta_pp _ (pushl o fi0) (pushr o fi2) (fun a => Kan (pp (fi1 a))
          (ap pushl (H00 a)) (ap pushr (H02 a))) a) _).
     refine (transport (fun x => Square _ (ap pushr x) _ _)
      (pushout_rec_beta_pp _ (pushl o fj0) (pushr o fj2) (fun a => Kan (pp (fj1 a))
          (ap pushl (H20 a)) (ap pushr (H22 a))) a) _).
      (* Recomposing the aps *)
      refine (transport (fun x => Square x _ _ _) (ap_compose fiX _ (pp a)) _).
      refine (transport (fun x => Square _ x _ _) (ap_compose fjX _ (pp a)) _).
      (* We can finally apply our filler *)
      exact (sq_apd _ (pp a)).
Defined.

Definition from : pushout fiX fjX -> pushout fXi fXj.
Proof.
  serapply pushout_rec.
  + serapply pushout_rec.
    * exact (pushl o pushl).
    * exact (pushr o pushl).
    * exact (pp o pushl).
  + serapply pushout_rec.
    * exact (pushl o pushr).
    * exact (pushr o pushr).
    * exact (pp o pushr).
  + serapply pushout_ind_sq.
    - exact (fun a => ap pushl (pp a)).
    - exact (fun a => ap pushr (pp a)).
    - intro a.
      (* Reduce aps *)
      refine (transport (fun x => Square _ _ x _) (ap_compose fiX _ _)^ _).
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
Defined.

(* This is very slow at the moment since coq tries to unfold 'to' all the time
   which isn't great since 'to' consists of so much stuff.
   The solution: Make 'to' more modular, but this will require time *)
Definition fromto : Sect from to.
Proof.
  unfold Sect.
  serapply pushout_ind.
  + serapply pushout_ind_sq.
    * intro a00; reflexivity.
    * intro a02; reflexivity.
    * intro a01.
      rewrite ap_compose.
      rewrite pushout_rec_beta_pp.
      rewrite (pushout_rec_beta_pp _ _ _ _ (pushl a01)).
      simpl.
      exact (sq_1G 1). (* Slow but works! *)
  + serapply pushout_ind_sq.
    * intro a20; reflexivity.
    * intro a22; reflexivity.
    * intro a21.
      rewrite ap_compose.
      rewrite pushout_rec_beta_pp.
      rewrite (pushout_rec_beta_pp _ _ _ _ (pushr a21)).
      simpl.
      exact (sq_1G 1).
      (* Too slow *)
  (* + serapply pushout_ind.
    * intro a10. simpl. *)
Admitted.

(* Going to be very similar to fromto *)
Definition tofrom : Sect to from.
Proof.
Admitted.

Lemma Pushout3x3 : pushout fXi fXj <~> pushout fiX fjX.
Proof.
  serapply equiv_adjointify.
  + exact to.
  + exact from.
  + exact fromto.
  + exact tofrom.
Defined.

End Pushout3x3.





