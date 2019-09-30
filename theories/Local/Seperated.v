Require Import Basics.
Require Import Types.
Require Import Modalities.ReflectiveSubuniverse.
Require Import Extensions.

Require Import Small.
Require Import HIT.Truncations.

(* We will assume the following axiom. It lets us factor a map f : X -> Y between a small X and locally small Y into an epi and a mono. Notably the middle type in X -> T -> Y is also small. The way to prove this is using the join construction which we currently don't have. *)
Record factorData@{i j} {X : Type@{i}} {Y : Type@{j}}
  `{LocallySmall@{i j} Y} (f : X -> Y) := {
  T : Type@{i};
  e : X -> T;
  m : T -> Y;
(*   ee : IsSurjection@{i j j j j} e; *)
  mm : IsEmbedding@{j j j} m;
  comm : f == m o e;
}.

Definition factorAxiom@{i j} {X : Type@{i}} {Y : Type@{j}}
  `{LocallySmall@{i j} Y} (f : X -> Y) : factorData f.
Proof.
Admitted.

Module Seperated_ReflectiveSubuniverses (Ls : ReflectiveSubuniverses)
  <: ReflectiveSubuniverses.

  Import Ls.
  Module Import Ls_Theory := ReflectiveSubuniverses_Theory Ls.

  Record SepData@{u a} := Sep {
    univalence_Sep : Univalence;
    L : ReflectiveSubuniverse@{u a}; }.
  Arguments Sep {_} _.
  (* TODO: Make this global so L' is the seperated RSU of the RSU L *)
  Local Notation "L '" := (Sep L) (at level 5, format "L '").

  Definition ReflectiveSubuniverse@{u a} : Type2@{u a} := SepData@{u a}.

  Definition O_reflector@{u a i}
    : ReflectiveSubuniverse@{u a} -> Type@{i} -> Type@{i}.
  Proof.
    intros [u L] X.
    srefine (T _ (factorAxiom@{i u} _)).
    1: exact (X * X).
    intro xy.
    refine (O_reflector@{u a i} L _).
    exact (fst xy = snd xy).
  Defined.

  Definition In@{u a i} : ReflectiveSubuniverse@{u a} -> Type2le@{i a} -> Type2le@{i a}.
  Proof.
    intros [u L] X.
    refine (forall (x y : X), _).
    exact (In L (x = y)).
  Defined.

  Definition O_inO@{u a i} : forall (L : ReflectiveSubuniverse@{u a}) (X : Type@{i}),
    In@{u a i} L (O_reflector@{u a i} L X).
  Proof.
    intros [u L] X.
    set (s := factorAxiom (fun xy : X * X => L (fst xy = snd xy))). (*
    change (forall x y : T _ s, Ls.In L (x = y)).
    destruct s as [T e m ee (*em*) comm].
    cbn; intros x y.*)
  Admitted.

  Definition to@{u a i} : forall (O : ReflectiveSubuniverse@{u a}) (T : Type@{i}),
    T -> O_reflector@{u a i} O T.
  Proof.
    intros [u L] X.
    set (s := factorAxiom (fun xy : X * X => L (fst xy = snd xy))). (*
    change (X -> T _ s).
    destruct s as [T e m ee (*em*) comm].
    cbn; intro x.
    exact (e (x, x)).
  Defined. *) Admitted.

  Definition inO_equiv_inO@{u a i j k} :
    forall (O : ReflectiveSubuniverse@{u a}) (T : Type@{i}) (U : Type@{j}),
      In@{u a i} O T -> forall f : T -> U, IsEquiv f ->
      let gei := ((fun x => x) : Type@{i} -> Type@{k}) in
      let gej := ((fun x => x) : Type@{j} -> Type@{k}) in
      In@{u a j} O U.
  Proof.
  Admitted.

  Definition hprop_inO@{u a i} `{Funext}
    (O : ReflectiveSubuniverse@{u a}) (T : Type@{i})
    : IsHProp (In@{u a i} O T).
  Proof.
    apply trunc_forall.
  Defined.

  Definition extendable_to_O@{u a i j k}
    (O : ReflectiveSubuniverse@{u a}) {P : Type2le@{i a}}
    {Q : Type2le@{j a}} {Q_inO : In@{u a j} O Q}
    : ooExtendableAlong@{i i j k} (to O P) (fun _ => Q).
  Proof.
  Admitted.
  
  (*   apply ext_localize_ind@{a i j i k}; intros ?.
    apply ooextendable_over_const.
    apply Q_inO.
  Defined. *)

End Seperated_ReflectiveSubuniverses.
