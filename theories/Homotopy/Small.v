Require Import Basics.
Require Import Types.
Require Import Pullback.

(* Essentially small and locally small types *)

Section Small.

  Universe U.

  Class EssentiallySmall (A : Type) := {
    essentiallysmall_type : Type@{U};
    essentiallysmall_equiv : A <~> essentiallysmall_type;
  }.

  Definition EssentiallySmallMap {A B} (f : A -> B)
    := forall b, EssentiallySmall (hfiber f b).

  Definition LocallySmall (A : Type)
    := forall (x y : A), EssentiallySmall (x = y).

  Definition LocallySmallMap {A B} (f : A -> B)
    := EssentiallySmallMap (fun a => (a; a; idpath) : Pullback f f).

  Definition issig_essentiallysmall (A : Type)
    : {X : Type@{U} & A <~> X} <~> EssentiallySmall A.
  Proof.
    issig (Build_EssentiallySmall A) (@essentiallysmall_type A)
      (@essentiallysmall_equiv A).
  Defined.

(*   Context `{Univalence}. *)

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

End Small.

(* Any universe is locally small with respect to itself via univalence. *)
Global Instance locallysmall_type `{Univalence} : LocallySmall@{u i} Type@{u}.
Proof.
  intros X Y.
  exists (X <~> Y).
  apply equiv_equiv_path.
Defined.


