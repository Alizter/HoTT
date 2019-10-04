Require Import Basics.
Require Import Types.
Require Import Pointed.Core.
Require Import Pointed.pHomotopy.
Require Import Pointed.pMap.
Require Import Pointed.pEquiv.

(* The yoneda lemma for pointed types. *)

Local Open Scope pointed_scope.

(* TODO: move *)
Definition functor_pmap {A B C D : pType} (f : B ->* A) (g : C ->* D)
  : (A ->* C) ->* B ->* D.
Proof.
  serapply Build_pMap.
  { intros i.
    refine (g o* i o* f). }
  by pointed_reduce.
Defined.

(* TODO: Clean up *)
Definition pequiv_functor_pmap `{Funext} {A B C D : pType}
  (f : B <~>* A) (g : C <~>* D)
  : (A ->* C) <~>* (B ->* D).
Proof.
  serapply pequiv_adjointify'.
  1: apply (functor_pmap f g).
  { serapply Build_pMap.
    1: refine (fun h => g^-1* o* h o* f^-1*).
    apply path_pmap.
    serapply Build_pHomotopy.
    1: intro x; apply point_eq.
    cbn; unfold moveR_equiv_V.
    pointed_reduce.
    hott_simpl. }
  { intro.
    serapply path_pmap.
    serapply Build_pHomotopy.
    { intro; cbv.
      refine (eisretr _ _ @ _).
      apply ap, eissect. }
    simpl.
    unfold moveR_equiv_V.
    rewrite (ap_compose x).
    rewrite !concat_p_pp.
    rewrite <- !ap_pp.
    rewrite (ap_compose _ g).
    rewrite <- ap_pp.
    rewrite (ap_compose _ g^-1).
    rewrite concat_p_pp.
    rewrite <- ap_pp.
Admitted.

Local Notation id := pmap_idmap.
Local Notation "f '=>*' g" := (functor_pmap f g) (at level 70).

Lemma pYoneda (A B : pType) (phi : forall (X : pType), (B ->* X) <~>* (A ->* X))
  : (forall X X' (f : X ->* X'), (id =>* f) o* phi X ==* phi X' o* (id =>* f))
  -> A <~>* B.
Proof.
  intro p.
  set (to := phi B id).
  set (fr := (phi A)^-1 id).
  serapply (pequiv_adjointify to fr).
  { cbn. admit. }
  { cbn.
    unfold fr, to.
    set (p _ _ fr).
    destruct p0.
Admitted.