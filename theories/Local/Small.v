Require Import Basics.
Require Import Types.
Require Import Pullback.

(* Essentially small and locally small types *)

Class EssentiallySmall@{i j} (A : Type@{j}) := {
  essentiallysmall_type : Type@{i};
  essentiallysmall_equiv : A <~> essentiallysmall_type;
}.

Definition EssentiallySmallMap@{i j} {A : Type@{i}} {B : Type@{j}} (f : A -> B)
  := forall b, EssentiallySmall@{i j} (hfiber f b).

Definition LocallySmall@{i j} (A : Type@{j})
  := forall (x y : A), EssentiallySmall@{i j} (x = y).

Definition LocallySmallMap@{i j} {A : Type@{i}} {B : Type@{j}} (f : A -> B)
  := EssentiallySmallMap@{i j} (fun a => (a; a; idpath) : Pullback f f).

Definition issig_essentiallysmall (A : Type@{j})
  : {X : Type@{i} & A <~> X} <~> EssentiallySmall@{i j} A.
Proof.
  issig (Build_EssentiallySmall A) (@essentiallysmall_type A)
    (@essentiallysmall_equiv A).
Defined.

Global Instance ishprop_essentiallysmall (A : Type)
  : IsHProp (EssentiallySmall A).
Proof.
  serapply trunc_equiv'.
  2: apply issig_essentiallysmall.
  
  intros [x ex] [y ey].
  serapply BuildContr.
  { serapply path_sigma'.
  
  (* 
    { apply path_universe_uncurried.
      exact (ey oE ex^-1). }
   *)  
Admitted.

Global Instance ishprop_essentiallysmallmap `{Funext} {A B} (f : A -> B)
  : IsHProp (EssentiallySmallMap f) := _.

Global Instance ishprop_locallysmall `{Funext} (A : Type)
  : IsHProp (LocallySmall A) := _.

Global Instance ishprop_locallysmallmap `{Funext} {A B} (f : A -> B)
  : IsHProp (LocallySmallMap f) := _.

Existing Class EssentiallySmallMap.
Existing Class LocallySmall.
Existing Class LocallySmallMap.

(* Any universe is locally small with respect to itself via univalence. *)
Global Instance locallysmall_type@{i j} `{Univalence}
  : LocallySmall@{i j} Type@{i}.
Proof.
  intros X Y.
  exists (X <~> Y).
  apply equiv_equiv_path.
Defined.


