Require Import Basics.
Require Import Types.
Require Import Cubical.

Lemma pointwise_paths_prewhisker
  {A B C : Type} {f g : B -> C} (h : A -> B)
  : f == g -> f o h == g o h.
Proof.
  intros p x; apply p.
Defined.

Lemma pointwise_paths_postwhisker
  {A B C : Type} {f g : A -> B} (h : B -> C)
  : f == g -> h o f == h o g.
Proof.
  intros p x; apply ap, p.
Defined.

Lemma inverse_nat {A B : Type}
  {e : forall X, (A -> X) <~> (B -> X)}
  (n : forall X Y (f : X -> Y),
    (fun g => f o g) o e X == e Y o (fun h => f o h))
  {X Y : Type} {f : X -> Y}
  : (fun g => f o g) o (e X)^-1 == (e Y)^-1 o (fun g => f o g).
Proof.
  symmetry.
  transitivity ((e Y)^-1 o (fun g : B -> X => f o g) o (e X) o (e X)^-1).
  { symmetry.
    refine (pointwise_paths_postwhisker
      (_ o (fun g : B -> X => f o g)) (eisretr _)). }
  transitivity ((e Y)^-1 o (e Y) o (fun g : A -> X => f o g) o (e X)^-1).
  { refine (pointwise_paths_prewhisker _ _).
    refine (pointwise_paths_postwhisker _ _).
    apply n. }
  refine (pointwise_paths_prewhisker _ (eissect _)).
Defined.

Lemma yoneda {A B : Type}
  {e : forall X, (A -> X) <~> (B -> X)}
  {n : forall X Y (f : X -> Y),
    (fun g => f o g) o e X == e Y o (fun h => f o h)}
  : A <~> B.
Proof.
  serapply equiv_adjointify.
  + exact ((e B)^-1 idmap).
  + exact (e A idmap).
  + intro x.
    refine (_ @ ap10 (eisretr (e B) idmap) x).
    revert x.
    apply ap10.
    exact (n A B ((e B)^-1 idmap) idmap).
  + intro x.
    cbv in n.
    refine (_ @ ap10 (eissect (e A) idmap) x).
    revert x.
    apply ap10.
    apply (inverse_nat n).
Defined.

Definition yoneda_uncurried {A B : Type} : _ -> A <~> B
  := sig_ind _ _ _ (@yoneda A B).

Definition ap_apply_lD
  {A}
  {B : A -> Type}
  {f g : forall x, B x}
  (p : f = g) (z : A)
  : ap (fun f => f z) p = apD10 p z
:= 1.

Definition ap_apply_lD2
  {A}
  {B : A -> Type}
  {C : forall x, B x -> Type}
  {f g : forall x y, C x y}
  (p : f = g) (z1 : A) (z2 : B z1)
  : ap (fun f => f z1 z2) p = apD10 (apD10 p z1) z2.
Proof.
    by path_induction.
Defined.

Definition ap_apply_lD3
  {A}
  {B : A -> Type}
  {C : forall x, B x -> Type}
  {D : forall x y, C x y -> Type}
  {f g : forall x y z, D x y z}
  (p : f = g) (z1 : A) (z2 : B z1) (z3 : C z1 z2)
  : ap (fun f => f z1 z2 z3) p = apD10 (apD10 (apD10 p z1) z2) z3.
Proof.
    by path_induction.
Defined.

Definition ap_apply_lD4
  {A}
  {B : A -> Type}
  {C : forall x, B x -> Type}
  {D : forall x y, C x y -> Type}
  {E : forall x y z, D x y z -> Type}
  {f g : forall w x y z, E w x y z}
  (p : f = g) (z1 : A) (z2 : B z1) (z3 : C z1 z2) (z4 : D z1 z2 z3)
  : ap (fun f => f z1 z2 z3 z4) p
    = apD10 (apD10 (apD10 (apD10 p z1) z2) z3) z4.
Proof.
    by path_induction.
Defined.

Global Instance isequiv_yoneda_uncurried `{Funext} {A B : Type}
  : IsEquiv (@yoneda_uncurried A B).
Proof.
  serapply isequiv_adjointify.
  { intro e.
    exists (fun X => @equiv_precompose' _ _ _ X e^-1).
    intros X Y f.
    reflexivity. }
  { intro e.
    apply path_equiv.
    reflexivity. }
  intros [a p].
  serapply path_sigma_dp.
  { funext x.
    apply path_equiv.
    funext g.
    apply p. }
  serapply dp_forall_domain; intro X.
  serapply dp_forall_domain; intro Y.
  serapply dp_forall_domain; intro g.
  serapply dp_forall_domain; intro e.
  simpl.
  apply sq_dp^-1.
Admitted.



