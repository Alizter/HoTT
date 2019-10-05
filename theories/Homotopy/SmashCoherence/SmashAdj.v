Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import Cubical.
Require Import Smash.
Require Import Coherence.
Require Import Bifunctor.

Local Open Scope pointed_scope.
Local Open Scope path_scope.

(* TODO: This should be in smash *)
Notation "X ∧ Y" := (Smash X Y) (at level 20).
(* Local Notation "A '->*' B" := (Build_pType (A ->* B) _). *)

Section SmashAdj.

Global Instance isfunctor_smash_right (B : pType)
  : IsFunctor (fun x => x ∧ B) := _.

Definition functor_smash_right (B : pType) {A C : pType}
  := @F_functor (fun x => x ∧ B) _ A C.

Global Instance isfunctor_pmap (B : pType)
  : IsFunctor (fun y => B ->* y).
Proof.
  serapply Build_IsFunctor.
  { intros X Y f.
    serapply Build_pMap.
    1: exact (fun g => f o* g).
    by pointed_reduce. }
  { intro A.
    serapply Build_pHomotopy.
    1: cbn; intro; by pointed_reduce.
    1: apply concat_p1. }
  intros X Y Z f' f.
  serapply Build_pHomotopy.
  1: cbn; intro; by pointed_reduce.
  by pointed_reduce.
Defined.

Definition functor_pmap (B : pType) {A C : pType}
  := @F_functor (fun y => B ->* y) _ A C.

Context `{Funext}.

Definition pmap_smash_unit {B : pType} (X : pType) : X ->* (B ->* (X ∧ B)).
Proof.
  serapply Build_pMap.
  { intro a.
    serapply Build_pMap.
    1: exact (sm a).
    refine (gluel' a _). }
  serapply path_pmap.
  serapply Build_pHomotopy.
  { intro x; cbn.
    apply gluer'. }
  refine (concat_p1 _ @ (glue_pt_left _ )^ @ glue_pt_right _).
Defined.

Definition pmap_smash_unit_natural {B X Y : pType} (f : X ->* Y)
  : pmap_smash_unit Y o* f
    ==* functor_pmap B (functor_smash_right B f)
    o* pmap_smash_unit X.
Proof.
  serapply Build_pHomotopy.
  { intro x.
    apply path_pmap.
    serapply Build_pHomotopy.
    1: reflexivity.
    cbn; rewrite Smash_rec_beta_gluel'.
    do 2 pointed_reduce.
    hott_simpl. }
Admitted.

Definition pmap_smash_counit {B : pType} (X : pType)
  : ((B ->* X) ∧ B) ->* X.
Proof.
  serapply Build_pMap.
  { serapply Smash_rec.
    1: exact idmap.
    3: intro; apply point_eq.
    2: intro; exact idpath. }
  reflexivity.
Defined.

Definition pmap_smash_counit_natural {B X Y : pType} (f : X ->* Y)
  : f o* pmap_smash_counit X ==* pmap_smash_counit Y
    o* functor_smash_right B (functor_pmap B f).
Proof.
  serapply Build_pHomotopy.
  { serapply Smash_ind.
    1: reflexivity.
    1,2: exact (point_eq _).
    { intro g.
      serapply dp_paths_FlFr.
      cbn.
      rewrite ap_compose.
      rewrite (Smash_rec_beta_gluel _ _ g).
      apply moveR_Mp.
      rewrite ap_compose.
      rewrite (Smash_rec_beta_gluel _ _ g).
      rewrite Smash_rec_beta_gluel.
      by do 2 pointed_reduce. }
    intro b.
    serapply dp_paths_FlFr.
    rewrite concat_p1.
    apply moveR_Vp.
    simpl.
    rewrite ap_compose.
    rewrite (Smash_rec_beta_gluer
      (fun a : B ->* X => gluel ((f o* a) : B ->* Y)) _ b).
    rewrite (ap_compose _ f).
    rewrite (Smash_rec_beta_gluer (fun a : B ->* X => point_eq a) _ b).
    rewrite transport_paths_Fl.
    rewrite ap_pp.
    rewrite Smash_rec_beta_gluer.
    rewrite ap_V.
    by pointed_reduce. }
  simpl.
  by pointed_reduce.
Defined.

Definition pmap_smash_triangle1 {B : pType} (X : pType)
  : functor_pmap B (pmap_smash_counit X) o* pmap_smash_unit (B ->* X)
    ==* pmap_idmap.
Proof.
Admitted.

Definition pmap_smash_triangle2 {B : pType} (X : pType)
  : pmap_smash_counit (X ∧ B) o* functor_smash_right B (pmap_smash_unit X)
    ==* pmap_idmap.
Proof.
  serapply Build_pHomotopy.
  { serapply Smash_ind.
    1: reflexivity.
    1: serapply gluel.
    1: serapply gluer.
    { intro a; hnf.
      apply dp_paths_FlFr.
      rewrite ap_idmap.
      rewrite concat_p1.
      rewrite (ap_compose (functor_smash_right _ _)).
      rewrite Smash_rec_beta_gluel.
      rewrite transport_paths_Fl.
      rewrite ap_pp.
      rewrite !ap_V.
      rewrite inv_V.
      rewrite <- ap_compose.
      rewrite Smash_rec_beta_gluel.
      simpl.
      rewrite concat_1p.
      apply moveR_Vp.
      unfold gluel'.
      rewrite concat_pp_p.
      rewrite concat_Vp.
      symmetry.
      apply concat_p1. }
    intro b; hnf.
    apply dp_paths_FlFr.
    rewrite ap_idmap.
    rewrite concat_p1.
    rewrite (ap_compose (functor_smash_right _ _)).
    rewrite Smash_rec_beta_gluer.
    rewrite transport_paths_Fl.
    rewrite ap_pp.
    rewrite !ap_V.
    rewrite inv_V.
    rewrite Smash_rec_beta_gluer.
    rewrite concat_p1.
    rewrite <- (ap_compose (fun x => sm x (pmap_idmap b)) _).
    simpl.
Admitted.

Theorem smash_adjunction {A B C : pType}
  : (A ∧ B ->* C) <~> (A ->* B ->* C).
Proof.
  serapply (equiv_adjointify
    (fun f => functor_pmap B f o* pmap_smash_unit A)
    (fun g => pmap_smash_counit C o* functor_smash_right B g)).
  { intro g. apply path_pmap.
    refine (pmap_prewhisker _ F_compose @* _).
    refine (pmap_compose_assoc _ _ _ @* _).
    refine (pmap_postwhisker _ (pmap_smash_unit_natural g)^* @* _).
    refine ((pmap_compose_assoc _ _ _)^* @* _).
    refine (pmap_prewhisker g (pmap_smash_triangle1 C) @* _).
    apply pmap_postcompose_idmap. }
  { intros f. apply path_pmap.
    refine (pmap_postwhisker _
      (F_compose (IsFunctor:=isfunctor_smash_right B)) @* _).
    refine ((pmap_compose_assoc _ _ _)^* @* _).
    refine (pmap_prewhisker _ (pmap_smash_counit_natural f)^* @* _).
    refine (pmap_compose_assoc _ _ _ @* _).
    refine (pmap_postwhisker f (pmap_smash_triangle2 A) @* _).
    apply pmap_precompose_idmap. }
Defined.

Theorem pequiv_smash_adj {A B C : pType}
  : (A ∧ B ->* C) <~>* (A ->* B ->* C).
Proof.
  serapply Build_pEquiv'.
  1: apply smash_adjunction.
Admitted.

End SmashAdj.