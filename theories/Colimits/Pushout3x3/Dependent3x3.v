Require Import Basics.
Require Import Types.
Require Import Cubical.
Require Import Pushout.

Section CubicalPushout.

(* Here is the induction principle for Pushouts using the cubical library *)

  Context {A B C : Type} {f : A -> B} {g : A -> C} (P : Pushout f g -> Type)
          (pushb : forall b : B, P (pushl b))
          (pushc : forall c : C, P (pushr c))
          (pusha : forall a : A, DPath _ (pglue a)  (pushb (f a)) (pushc (g a))).

  Definition Pushout_ind : forall (w : Pushout f g), P w.
  Proof.
    serapply (Pushout_ind _ pushb pushc).
    intro a.
    apply dp_path_transport^-1.
    apply pusha.
  Defined.

  Definition Pushout_ind_beta_pglue (a : A)
    : dp_apD Pushout_ind (pglue a) = pusha a.
  Proof.
    apply dp_apD_path_transport.
    exact (Pushout_ind_beta_pglue _ _ _ _ _).
  Defined.

End CubicalPushout.


Section PushoutLemma.

  Context
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

  Definition to : AXO -> AOX.
  Proof.
    serapply Pushout_rec.
    { serapply (Pushout_rec _).
      + exact (pushl o pushl).
      + exact (pushr o pushl).
      + exact (pglue o pushl). }
    { serapply (Pushout_rec _).
      + exact (pushl o pushr).
      + exact (pushr o pushr).
      + exact (pglue o pushr). }
    serapply Pushout_ind; intro x; cbn.
    + apply (ap pushl), pglue.
    + apply (ap pushr), pglue.
    + apply sq_dp^-1.
      refine (sq_ccGG _^ _^ _).
      1,2: apply ap_compose.
      refine (sq_ccGG _^ _^ _).
      1,2: apply ap, Pushout_rec_beta_pglue.
      refine (sq_ccGG _^ _^ _).
      1,2: serapply Pushout_rec_beta_pglue.
      set (s := ap_nat (pglue (f:=f1X) (g:=f3X)) (pglue (f:=f21) (g:=f23) x)).
      apply (sq_GGcc (ap_compose _ pushl _) (ap_compose _ pushr _)) in s.
      rewrite !Pushout_rec_beta_pglue in s.
      assumption.
  Defined.

  Definition from : AOX -> AXO.
  Proof.
    serapply Pushout_rec.
    { serapply (Pushout_rec _).
      + exact (pushl o pushl).
      + exact (pushr o pushl).
      + exact (pglue o pushl). }
    { serapply (Pushout_rec _).
      + exact (pushl o pushr).
      + exact (pushr o pushr).
      + exact (pglue o pushr). }
    serapply Pushout_ind; intro x; cbn.
    + apply (ap pushl), pglue.
    + apply (ap pushr), pglue.
    + apply sq_dp^-1.
      refine (sq_ccGG _^ _^ _).
      1,2: apply ap_compose.
      refine (sq_ccGG _^ _^ _).
      1,2: apply ap, Pushout_rec_beta_pglue.
      refine (sq_ccGG _^ _^ _).
      1,2: serapply Pushout_rec_beta_pglue.
      set (s := ap_nat (pglue (f:=fX1) (g:=fX3)) (pglue (f:=f12) (g:=f32) x)).
      apply (sq_GGcc (ap_compose _ pushl _) (ap_compose _ pushr _)) in s.
      rewrite !Pushout_rec_beta_pglue in s.
      assumption.
  Defined.

  Lemma dp_apD_compose {A B : Type} {P : B -> Type}
    (f : forall a, P a) (g : A -> B) {a0 a1 : A}
    (p : a0 = a1) : dp_apD (f o g) p = dp_compose _ _ _ _ _ (dp_apD f (ap g p)).
  Proof.
    by destruct p.
  Defined.

  Local Open Scope dpath_scope.

  Definition tofrom : Sect to from.
  Proof.
    do 2 serapply Pushout_ind.
    1,2,3,4,5,6,7,8: shelve.
    intro.
    cbn.
    
  
    serapply Pushout_ind.
    3: intro x; cbn; apply sq_dp^-1, sq_tr^-1; revert x.
    3: serapply Pushout_ind.
    1,2,3,4: shelve.
    intro x; cbn.
    apply cu_dp^-1.
    do 2 apply cu_rot_tb_fb.
    apply cu_rot2.
    erapply cu_GGGGcc.
    1,2,3,4: symmetry; serapply (eissect sq_tr).
    dp_apD_compose
  Admitted.

  Definition fromto : Sect from to.
  Proof.
    serapply Pushout_ind.
    3: intro x; cbn; apply sq_dp^-1, sq_tr^-1; revert x.
    3: serapply Pushout_ind.
    1,2,3,4: shelve.
    intro x; cbn.
    apply cu_dp^-1.
    do 2 apply cu_rot_tb_fb.
    apply cu_rot2.
    erapply cu_GGGGcc.
    1,2,3,4: symmetry; serapply (eissect sq_tr).
  
  Admitted.

End PushoutLemma.