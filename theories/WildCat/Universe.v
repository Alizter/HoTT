Require Import Basics.Overture Basics.Tactics Basics.Equivalences Types.Equiv.
Require Import WildCat.Core.
Require Import WildCat.Equiv.

(** ** The category of types *)

Global Instance isgraph_type@{u v} : IsGraph@{v u} Type@{u}
  := Build_IsGraph Type@{u} (fun a b => a -> b).

Global Instance is01cat_type : Is01Cat Type.
Proof.
  econstructor.
  + intro; exact idmap.
  + exact (fun a b c g f => g o f).
Defined.

Global Instance is2graph_type : Is2Graph Type
  := fun x y => Build_IsGraph _ (fun f g => f == g).

(** Sometimes we need typeclasses to pick up that [A -> B] is a graph, but this cannot be done without first converting it to [A $-> B]. *)
Global Instance isgraph_arrow {A B : Type} : IsGraph (A -> B)
  := isgraph_hom A B.

Global Instance is01cat_arrow {A B : Type} : Is01Cat (A $-> B).
Proof.
  econstructor.
  - exact (fun f a => idpath).
  - exact (fun f g h p q a => q a @ p a).
Defined.

Global Instance is0gpd_arrow {A B : Type}: Is0Gpd (A $-> B).
Proof.
  apply Build_Is0Gpd.
  intros f g p a ; exact (p a)^.
Defined.

Global Instance is0functor_type_postcomp {A B C : Type} (h : B $-> C):
  Is0Functor (cat_postcomp A h).
Proof.
  apply Build_Is0Functor.
  intros f g p a; exact (ap h (p a)).
Defined.

Global Instance is0functor_type_precomp {A B C : Type} (h : A $-> B):
  Is0Functor (cat_precomp C h).
Proof.
  apply Build_Is0Functor.
  intros f g p a; exact (p (h a)).
Defined.

Global Instance is1cat_strong_type : Is1Cat_Strong Type.
Proof.
  srapply Build_Is1Cat_Strong; cbn; intros; reflexivity.
Defined.

Global Instance hasmorext_type `{Funext} : HasMorExt Type.
Proof.
  srapply Build_HasMorExt.
  intros A B f g; cbn in *.
  refine (isequiv_homotopic (@apD10 A (fun _ => B) f g) _).
  intros p.
  destruct p; reflexivity.
Defined.

Global Instance hasequivs_type : HasEquivs Type.
Proof.
  srefine (Build_HasEquivs Type _ _ _ _ Equiv (@IsEquiv) _ _ _ _ _ _ _ _); intros A B.
  all:intros f.
  - exact f.
  - exact _.
  - apply Build_Equiv.
  - intros; reflexivity.
  - intros; exact (f^-1).
  - cbn. intros ?; apply eissect.
  - cbn. intros ?; apply eisretr.
  - intros g r s; refine (isequiv_adjointify f g r s).
Defined.

Global Instance hasmorext_core_type `{Funext}: HasMorExt (core Type).
Proof.
  snrapply Build_HasMorExt.
  intros A B f g; cbn in *.
  snrapply isequiv_homotopic.
  - exact (GpdHom_path o (ap (x:=f) (y:=g) equiv_fun)).
  - nrapply isequiv_compose.
    1: apply isequiv_ap_equiv_fun.
    exact (isequiv_Htpy_path (uncore A) (uncore B) f g).
  - intro p; by induction p.
Defined.

Definition catie_isequiv {A B : Type} {f : A $-> B}
       `{IsEquiv A B f} : CatIsEquiv f.
Proof.
  assumption.
Defined.

#[export]
Hint Immediate catie_isequiv : typeclass_instances.

Global Instance isinitial_zero : IsInitial Empty.
Proof.
  intro A.
  exists (Empty_rec _).
  intros g.
  rapply Empty_ind.
Defined.

Global Instance isterminal_unit : IsTerminal Unit.
Proof.
  intros A.
  exists (fun _ => tt).
  intros f x.
  by destruct (f x).
Defined.
