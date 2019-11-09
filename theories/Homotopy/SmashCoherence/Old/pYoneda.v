Require Import Basics.
Require Import Types.
Require Import Pointed.
(* Require Import Coherence. *)
(* Require Import pMapFunctor. *)
Require Import PointedCategory.Functor.
Require Import PointedCategory.Natural.
Require Import PointedCategory.pMapFunctor.

(* The yoneda lemma for pointed types. *)

Local Open Scope pointed_scope.

Local Notation id := pmap_idmap.

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
    apply (@inverse_nat A B e n B A (e A idmap) idmap).
Defined.




