Require Import Basics Types.
Require Import Cubical.

(** TODO: move these? *)
Definition sig2 {A B : Type} (C : A -> B -> Type) : Type
  := {a : A & {b : B & C a b}}.

Definition sig44 {A B C D : Type}
  {E : A -> B -> Type} {F : C -> D -> Type}
  {G : A -> C -> Type} {H : B -> D -> Type}
  (I : forall a b c d, E a b -> F c d -> G a c -> H b d -> Type)
  : Type
  := {a : A & {b : B & {c : C & {d : D &
     {e : E a b & {f : F c d & {g : G a c & {h : H b d
     & I a b c d e f g h}}}}}}}}.

(** Specification of symmetric double pushout *)

(** The following module specifies what it means for a type to be a "symmetric double pushout". It outlines the induction principle it should have and the computation rules that should be provable. Later we will show that any implmentation of this specification are necessarily equivalent types. If given a (definitionally commuting) diagram, we can push rows then coloumns out or coloumns then rows. Both of these can be proven to be an implmentation of the symmetric double pushout, hence are equivalent. *)

Module Type SymmetricDoublePushoutSpec.

  Section Diagram.

    Universe U.

    Parameter SymP
      : forall
      {A00 A10 A01 A11 : Type@{U}}
      {A0X : A00 -> A01 -> Type@{U}} {A1X : A10 -> A11 -> Type@{U}}
      {AX0 : A00 -> A10 -> Type@{U}} {AX1 : A01 -> A11 -> Type@{U}}
      (AXX : forall a00 a01 a10 a11, A0X a00 a01 -> A1X a10 a11 -> AX0 a00 a10 -> AX1 a01 a11 -> Type@{U})
      , Type@{U}.

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

    Parameter a : B00 -> SymP AXX.
    Parameter b : B10 -> SymP AXX.
    Parameter c : B01 -> SymP AXX.
    Parameter d : B11 -> SymP AXX.
    Parameter H1 : a o f0i == c o f0j.
    Parameter H2 : a o fi0 == b o fj0.
    Parameter H3 : c o fi1 == d o fj1.
    Parameter H4 : b o f1i == d o f1j.
    Parameter sq : forall x, PathSquare (H1 (fiX x)) (H4 (fjX x)) (H2 (fXi x)) (H3 (fXj x)).  

    (** Induction principle *)
    Parameter SymP_ind : forall (P : SymP AXX -> Type)
      (xa : forall x, P (a x)) (xb : forall x, P (b x))
      (xc : forall x, P (c x)) (xd : forall x, P (d x))
      (Q1 : forall x, DPath P (H1 x) (xa (f0i x)) (xc (f0j x)))
      (Q2 : forall x, DPath P (H2 x) (xa (fi0 x)) (xb (fj0 x)))
      (Q3 : forall x, DPath P (H3 x) (xc (fi1 x)) (xd (fj1 x)))
      (Q4 : forall x, DPath P (H4 x) (xb (f1i x)) (xd (f1j x)))
      (xsq : forall x, DPathSquare P (sq x) (Q1 (fiX x)) (Q4 (fjX x)) (Q2 (fXi x)) (Q3 (fXj x)))
      (s : SymP AXX), P s.

    (** Computation rules *)
    Section ComputationRules.

      Context (P : SymP AXX -> Type)
        (xa : forall x, P (a x)) (xb : forall x, P (b x))
        (xc : forall x, P (c x)) (xd : forall x, P (d x))
        (Q1 : forall x, DPath P (H1 x) (xa (f0i x)) (xc (f0j x)))
        (Q2 : forall x, DPath P (H2 x) (xa (fi0 x)) (xb (fj0 x)))
        (Q3 : forall x, DPath P (H3 x) (xc (fi1 x)) (xd (fj1 x)))
        (Q4 : forall x, DPath P (H4 x) (xb (f1i x)) (xd (f1j x)))
        (xsq : forall x, DPathSquare P (sq x) (Q1 (fiX x)) (Q4 (fjX x)) (Q2 (fXi x)) (Q3 (fXj x))).

      (** Point computation rules *)
      Parameter SymP_ind_beta_a : forall x, SymP_ind P xa xb xc xd Q1 Q2 Q3 Q4 xsq (a x) = (xa x).
      Parameter SymP_ind_beta_b : forall x, SymP_ind P xa xb xc xd Q1 Q2 Q3 Q4 xsq (b x) = (xb x).
      Parameter SymP_ind_beta_c : forall x, SymP_ind P xa xb xc xd Q1 Q2 Q3 Q4 xsq (c x) = (xc x).
      Parameter SymP_ind_beta_d : forall x, SymP_ind P xa xb xc xd Q1 Q2 Q3 Q4 xsq (d x) = (xd x).

      (** Path computation rules *)
      Parameter SymP_ind_beta_H1 : forall x,
        DPathSquare P (sq_refl_h (H1 x)) (dp_apD (SymP_ind P xa xb xc xd Q1 Q2 Q3 Q4 xsq) (H1 x)) (Q1 x)
          (SymP_ind_beta_a (f0i x)) (SymP_ind_beta_c (f0j x)).
      Parameter SymP_ind_beta_H2 : forall x,
        DPathSquare P (sq_refl_h (H2 x)) (dp_apD (SymP_ind P xa xb xc xd Q1 Q2 Q3 Q4 xsq) (H2 x)) (Q2 x)
          (SymP_ind_beta_a (fi0 x)) (SymP_ind_beta_b (fj0 x)).
      Parameter SymP_ind_beta_H3 : forall x,
        DPathSquare P (sq_refl_h (H3 x)) (dp_apD (SymP_ind P xa xb xc xd Q1 Q2 Q3 Q4 xsq) (H3 x)) (Q3 x)
          (SymP_ind_beta_c (fi1 x)) (SymP_ind_beta_d (fj1 x)).
      Parameter SymP_ind_beta_H4 : forall x,
        DPathSquare P (sq_refl_h (H4 x)) (dp_apD (SymP_ind P xa xb xc xd Q1 Q2 Q3 Q4 xsq) (H4 x)) (Q4 x)
          (SymP_ind_beta_b (f1i x)) (SymP_ind_beta_d (f1j x)).

      (** Square compuation rules *)
      Parameter SymP_ind_beta_sq : forall x,
        DPathCube P (cu_refl_lr (sq x))
          (ds_apD (SymP_ind P xa xb xc xd Q1 Q2 Q3 Q4 xsq) (sq x)) (xsq x)
          (SymP_ind_beta_H1 (fiX x)) (SymP_ind_beta_H4 (fjX x))
          (SymP_ind_beta_H2 (fXi x)) (SymP_ind_beta_H3 (fXj x)).

    End ComputationRules.
  End Diagram.
End SymmetricDoublePushoutSpec.

(** Recursion principles for spec *)
(** Since we can't put definitions inside module types we have to seperate these out into a seperate "theories" module. This unfortunately makes us have to prefix the local definitions declared earlier with "L." and give some of the type families. *)
Module SymmetricDoublePushoutSpecRec (L : SymmetricDoublePushoutSpec).
  Import L.

  Section Diagram.

    Universe U.

    Context {A00 A10 A01 A11 : Type@{U}}
      {A0X : A00 -> A01 -> Type@{U}} {A1X : A10 -> A11 -> Type@{U}}
      {AX0 : A00 -> A10 -> Type@{U}} {AX1 : A01 -> A11 -> Type@{U}}
      {AXX : forall a00 a01 a10 a11, A0X a00 a01 -> A1X a10 a11 -> AX0 a00 a10 -> AX1 a01 a11 -> Type@{U}}.

    (** Recursion *)
    Definition SymP_rec (P : Type)
      (xa : @L.B00 A00 -> P) (xb : @L.B10 A10 -> P) (xc : @L.B01 A01 -> P) (xd : @L.B11 A11 -> P)
      (Q1 : xa o @L.f0i A00 A01 A0X == xc o @L.f0j A00 A01 A0X)
      (Q2 : xa o @L.fi0 A00 A10 AX0 == xb o @L.fj0 A00 A10 AX0)
      (Q3 : xc o @L.fi1 A01 A11 AX1 == xd o @L.fj1 A01 A11 AX1)
      (Q4 : xb o @L.f1i A10 A11 A1X == xd o @L.f1j A10 A11 A1X)
      (xsq : forall x, PathSquare (Q1 (L.fiX x)) (Q4 (L.fjX x))
        (Q2 (L.fXi x)) (Q3 (L.fXj (AXX:=AXX) x))) : SymP AXX -> P.
    Proof.
      srapply SymP_ind.
      1-4: assumption.
      1-4: intro x; apply dp_const; revert x; assumption.
      intro x. cbn.
      apply ds_const.
      apply xsq.
    Defined.

    Section ComputationRules.

      Context  (P : Type)
        (xa : @L.B00 A00 -> P) (xb : @L.B10 A10 -> P) (xc : @L.B01 A01 -> P) (xd : @L.B11 A11 -> P)
        (Q1 : xa o @L.f0i A00 A01 A0X == xc o @L.f0j A00 A01 A0X)
        (Q2 : xa o @L.fi0 A00 A10 AX0 == xb o @L.fj0 A00 A10 AX0)
        (Q3 : xc o @L.fi1 A01 A11 AX1 == xd o @L.fj1 A01 A11 AX1)
        (Q4 : xb o @L.f1i A10 A11 A1X == xd o @L.f1j A10 A11 A1X)
        (xsq : forall x, PathSquare (Q1 (L.fiX x)) (Q4 (L.fjX x))
          (Q2 (L.fXi x)) (Q3 (L.fXj (AXX:=AXX) x))).

      Definition SymP_rec_beta_a : forall x, SymP_rec P xa xb xc xd Q1 Q2 Q3 Q4 xsq (a x) = (xa x).
      Proof.
        intro x.
        refine (1 @ _).
        rapply SymP_ind_beta_a.
      Defined.

      Definition SymP_rec_beta_b : forall x, SymP_rec P xa xb xc xd Q1 Q2 Q3 Q4 xsq (b x) = (xb x).
      Proof.
        intro x.
        refine (1 @ _).
        rapply SymP_ind_beta_b.
      Defined.

      Definition SymP_rec_beta_c : forall x, SymP_rec P xa xb xc xd Q1 Q2 Q3 Q4 xsq (c x) = (xc x).
      Proof.
        intro x.
        refine (1 @ _).
        rapply SymP_ind_beta_c.
      Defined.

      Definition SymP_rec_beta_d : forall x, SymP_rec P xa xb xc xd Q1 Q2 Q3 Q4 xsq (d x) = (xd x).
      Proof.
        intro x.
        refine (1 @ _).
        rapply SymP_ind_beta_d.
      Defined.

      Definition SymP_rec_beta_H1 : forall x,
        PathSquare (ap (SymP_rec P xa xb xc xd Q1 Q2 Q3 Q4 xsq) (H1 x)) (Q1 x)
          (SymP_rec_beta_a (L.f0i x)) (SymP_rec_beta_c (L.f0j x)).
      Proof.
        intro x.
        rapply ds_const^-1.
        refine (ds_concat_h (dp_apD_const_ds _ (H1 x))
          (SymP_ind_beta_H1 _ _ _ _ _ _ _ _ _ _ x)).
      Defined.

      Definition SymP_rec_beta_H2 : forall x,
        PathSquare (ap (SymP_rec P xa xb xc xd Q1 Q2 Q3 Q4 xsq) (H2 x)) (Q2 x)
          (SymP_rec_beta_a (L.fi0 x)) (SymP_rec_beta_b (L.fj0 x)).
      Proof.
        intro x.
        rapply ds_const^-1.
        refine (ds_concat_h (dp_apD_const_ds _ (H2 x))
          (SymP_ind_beta_H2 _ _ _ _ _ _ _ _ _ _ x)).
      Defined.

      Definition SymP_rec_beta_H3 : forall x,
        PathSquare (ap (SymP_rec P xa xb xc xd Q1 Q2 Q3 Q4 xsq) (H3 x)) (Q3 x)
          (SymP_rec_beta_c (L.fi1 x)) (SymP_rec_beta_d (L.fj1 x)).
      Proof.
        intro x.
        rapply ds_const^-1.
        refine (ds_concat_h (dp_apD_const_ds _ (H3 x))
          (SymP_ind_beta_H3 _ _ _ _ _ _ _ _ _ _ x)).
      Defined.

      Definition SymP_rec_beta_H4 : forall x,
        PathSquare (ap (SymP_rec P xa xb xc xd Q1 Q2 Q3 Q4 xsq) (H4 x)) (Q4 x)
          (SymP_rec_beta_b (L.f1i x)) (SymP_rec_beta_d (L.f1j x)).
      Proof.
        intro x.
        rapply ds_const^-1.
        refine (ds_concat_h (dp_apD_const_ds _ (H4 x))
          (SymP_ind_beta_H4 _ _ _ _ _ _ _ _ _ _ x)).
      Defined.

      Definition SymP_rec_beta_sq : forall x,
        PathCube (sq_ap (SymP_rec P xa xb xc xd Q1 Q2 Q3 Q4 xsq) (sq x)) (xsq x)
          (SymP_rec_beta_H1 (L.fiX x)) (SymP_rec_beta_H4 (L.fjX x))
          (SymP_rec_beta_H2 (L.fXi x)) (SymP_rec_beta_H3 (L.fXj x)).
      Proof.
        intro x.
        rapply dc_const^-1.
        (** First rewrite last four faces with eisretr *)
        refine (dc_ccGGGG _^ _^ _^ _^ _).
        1-4: rapply (eisretr ds_const).
        refine (dc_concat_lr (ds_apD_const_dc _ (sq x))
          (SymP_ind_beta_sq _ _ _ _ _ _ _ _ _ _ x)).
      Defined.

    End ComputationRules.
  End Diagram.
End SymmetricDoublePushoutSpecRec.

(** The equivalence of two symmetric double pushout implementations. *)
Module SymmetricDoublePushoutEquiv (L R : SymmetricDoublePushoutSpec).
  Module LRec := SymmetricDoublePushoutSpecRec L.
  Module RRec := SymmetricDoublePushoutSpecRec R.
  Export LRec RRec.

  Section Diagram.

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

    Local Definition to : L.SymP AXX -> R.SymP AXX
      := LRec.SymP_rec (R.SymP AXX) R.a R.b R.c R.d R.H1 R.H2 R.H3 R.H4 R.sq.

    Local Definition from : R.SymP AXX -> L.SymP AXX
      := RRec.SymP_rec (L.SymP AXX) L.a L.b L.c L.d L.H1 L.H2 L.H3 L.H4 L.sq.

    Local Definition tofrom : Sect from to.
    Proof.
      (** In theory, we should be able to manipulate the final goal given by R.SymP_ind as the faces of that cube are determined by the earlier goals. However coq's unification algorithm struggles. Therefore we have to guide the earlier goals. *)
      snrapply R.SymP_ind.
      1-4: hnf; intro x.
      (** For example, steps like this might seem useless but they are needed for manipulations of the cube. *)
      1-4: refine (1 @ _).
      
      1-4: refine (ap to _ @ _).
      1: apply RRec.SymP_rec_beta_a.
      2: apply RRec.SymP_rec_beta_b.
      3: apply RRec.SymP_rec_beta_c.
      4: apply RRec.SymP_rec_beta_d.
      
      1-4: refine (_ @ 1).
      
      1-4: revert x.
      
      1: refine ?[pa]; shelve.
      1: refine ?[pb]; shelve.
      1: refine ?[pc]; shelve.
      1: refine ?[pd]; shelve.
      
      1-4: intro x; apply sq_dp, sq_tr^-1%equiv.
      1-4: refine (sq_concat_h (ap_compose_sq from to (_ x)) _).
      
      1: refine (sq_concat_h (sq_ap to (RRec.SymP_rec_beta_H1 _ _ _ _ _ _ _ _ _ _ x)) _).
      2: refine (sq_concat_h (sq_ap to (RRec.SymP_rec_beta_H2 _ _ _ _ _ _ _ _ _ _ x)) _).
      3: refine (sq_concat_h (sq_ap to (RRec.SymP_rec_beta_H3 _ _ _ _ _ _ _ _ _ _ x)) _).
      4: refine (sq_concat_h (sq_ap to (RRec.SymP_rec_beta_H4 _ _ _ _ _ _ _ _ _ _ x)) _).
      
      1: refine (sq_concat_h (LRec.SymP_rec_beta_H1 _ _ _ _ _ _ _ _ _ _ x) _).
      2: refine (sq_concat_h (LRec.SymP_rec_beta_H2 _ _ _ _ _ _ _ _ _ _ x) _).
      3: refine (sq_concat_h (LRec.SymP_rec_beta_H3 _ _ _ _ _ _ _ _ _ _ x) _).
      4: refine (sq_concat_h (LRec.SymP_rec_beta_H4 _ _ _ _ _ _ _ _ _ _ x) _).
      
      1-4: apply sq_flip_h^-1%equiv.
      
      1: apply (ap_idmap_sq (R.H1 x)).
      1: apply (ap_idmap_sq (R.H2 x)).
      1: apply (ap_idmap_sq (R.H3 x)).
      1: apply (ap_idmap_sq (R.H4 x)).
      
      cbv zeta; hnf.
      intro x.
      apply cu_ds.
      refine (cu_GGGGcc _ _ _ _ _).
      1-4: symmetry; rapply eisretr.
      apply cu_rot_tb_fb.
      refine (cu_ccGGGG _^ _^ _^ _^ _).
      1-4: rapply (eisretr sq_tr _).
      refine (cu_concat_lr (sq_ap_compose from to (R.sq x)) _).
      refine (cu_concat_lr (cu_ap to (RRec.SymP_rec_beta_sq _ _ _ _ _ _ _ _ _ _ x)) _).
      refine (cu_concat_lr (LRec.SymP_rec_beta_sq _ _ _ _ _ _ _ _ _ _ x) _).
      apply cu_flip_lr.
      refine (cu_ccGGGG _^ _^ _^ _^ _).
      1-4: rapply (eisretr sq_flip_h).
      rapply (sq_ap_idmap (R.sq x)).
    Defined. (** Takes a long time *)

    (** Exact same proof but [to] is swapped with [from] and [L] is swapped with [R] *)
    Local Definition fromto : Sect to from.
    Proof.
      snrapply L.SymP_ind.
      1-4: hnf; intro x.
      1-4: refine (1 @ _).
      1-4: refine (ap from _ @ _).
      1: apply LRec.SymP_rec_beta_a.
      2: apply LRec.SymP_rec_beta_b.
      3: apply LRec.SymP_rec_beta_c.
      4: apply LRec.SymP_rec_beta_d.
      1-4: refine (_ @ 1).
      1-4: revert x.
      1: refine ?[pa]; shelve.
      1: refine ?[pb]; shelve.
      1: refine ?[pc]; shelve.
      1: refine ?[pd]; shelve.
      1-4: intro x; apply sq_dp, sq_tr^-1%equiv.
      1-4: refine (sq_concat_h (ap_compose_sq to from (_ x)) _).
      1: refine (sq_concat_h (sq_ap from (LRec.SymP_rec_beta_H1 _ _ _ _ _ _ _ _ _ _ x)) _).
      2: refine (sq_concat_h (sq_ap from (LRec.SymP_rec_beta_H2 _ _ _ _ _ _ _ _ _ _ x)) _).
      3: refine (sq_concat_h (sq_ap from (LRec.SymP_rec_beta_H3 _ _ _ _ _ _ _ _ _ _ x)) _).
      4: refine (sq_concat_h (sq_ap from (LRec.SymP_rec_beta_H4 _ _ _ _ _ _ _ _ _ _ x)) _).
      1: refine (sq_concat_h (RRec.SymP_rec_beta_H1 _ _ _ _ _ _ _ _ _ _ x) _).
      2: refine (sq_concat_h (RRec.SymP_rec_beta_H2 _ _ _ _ _ _ _ _ _ _ x) _).
      3: refine (sq_concat_h (RRec.SymP_rec_beta_H3 _ _ _ _ _ _ _ _ _ _ x) _).
      4: refine (sq_concat_h (RRec.SymP_rec_beta_H4 _ _ _ _ _ _ _ _ _ _ x) _).
      1-4: apply sq_flip_h^-1%equiv.
      1: apply (ap_idmap_sq (L.H1 x)).
      1: apply (ap_idmap_sq (L.H2 x)).
      1: apply (ap_idmap_sq (L.H3 x)).
      1: apply (ap_idmap_sq (L.H4 x)).
      cbv zeta; hnf.
      intro x.
      apply cu_ds.
      refine (cu_GGGGcc _ _ _ _ _).
      1-4: symmetry; rapply eisretr.
      apply cu_rot_tb_fb.
      refine (cu_ccGGGG _^ _^ _^ _^ _).
      1-4: rapply (eisretr sq_tr _).
      refine (cu_concat_lr (sq_ap_compose to from (L.sq x)) _).
      refine (cu_concat_lr (cu_ap from (LRec.SymP_rec_beta_sq _ _ _ _ _ _ _ _ _ _ x)) _).
      refine (cu_concat_lr (RRec.SymP_rec_beta_sq _ _ _ _ _ _ _ _ _ _ x) _).
      apply cu_flip_lr.
      refine (cu_ccGGGG _^ _^ _^ _^ _).
      1-4: rapply (eisretr sq_flip_h).
      rapply (sq_ap_idmap (L.sq x)).
    Defined. (** Takes a long time *)

    (** TODO: It might be possible to seperate the above proof into its seperate module and reuse it. This could speed up the compile time. *)

    Definition equiv_symmetric_double_pushout
      : L.SymP AXX <~> R.SymP AXX
      := equiv_adjointify to from tofrom fromto.

  End Diagram.

End SymmetricDoublePushoutEquiv.

