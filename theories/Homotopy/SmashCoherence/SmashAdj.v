Require Import Basics.
Require Import Types.
Require Import Cubical.
Require Import Pointed.
Require Import PointedCategory.Functor.
Require Import PointedCategory.pFunctor.
Require Import PointedCategory.Bifunctor.
Require Import PointedCategory.Adjunction.
Require Import PointedCategory.pMapFunctor.
Require Import Homotopy.Smash.
Require Import Homotopy.SmashCoherence.Bifunctor.

Local Open Scope pointed_scope.
Local Open Scope path_scope.

(* TODO: This should be in smash *)
Notation "X ∧ Y" := (Smash X Y) (at level 20).
(* Local Notation "A '->*' B" := (Build_pType (A ->* B) _). *)

Section SmashAdj.

Global Instance isfunctor_smash_right (B : pType)
  : IsFunctor (fun x => x ∧ B) := _.

Definition functor_smash_right (B : pType) : Functor
  := @Build_Functor _ (isfunctor_smash_right B).

(* Local Notation "B [∧] f" := (F_functor (F:=functor_smash_right B) f). *)

Definition smash_right_functor (B : pType) {X Y : pType} (f : X ->* Y)
  := F_functor (functor_smash_right B) f.

Definition pmap_functor (B : pType) {X Y : pType} (f : X ->* Y)
  := F_functor (functor_pmap B) f.

Context `{Funext}.

Definition pmap_smash_unit {B : pType} (X : pType) : X ->* (B ->* (X ∧ B)).
Proof.
  serapply Build_pMap.
  { intro x.
    serapply Build_pMap.
    1: exact (sm x).
    exact (gluel' x _). }
  apply path_pmap.
  serapply Build_pHomotopy.
  1: exact (fun x => gluer' x _).
  exact (concat_p1 _ @ (glue_pt_left _)^ @ glue_pt_right _).
Defined.

Definition pmap_smash_unit_natural {B X Y : pType} (f : X ->* Y)
  : pmap_smash_unit Y o* f
  ==* pmap_functor B (smash_right_functor B f)
    o* pmap_smash_unit X.
Proof.
  pointed_reduce.
  serapply Build_pHomotopy.
  { intro x.
    apply path_pmap.
    shelve. }
  simpl.
  rewrite path_pmap_ap.
  rewrite concat_1p, concat_p1.
  rewrite path_pmap_pp.
  apply ap.
  shelve.
  Unshelve.
  { serapply Build_pHomotopy.
    1: reflexivity.
    simpl.
    do 2 refine (concat_1p _ @ _).
    refine (concat_p1 _ @ _).
    refine (Smash_rec_beta_gluel' _ _ _ _ @ _).
    refine (ap2 (fun x y => x @ y^) (concat_1p _) (concat_1p _)). }
  simpl.
  refine ((ap (issig_phomotopy _ _)^-1)^-1 _).
  serapply path_sigma'.
  { apply path_forall.
    simpl.
    intro.
    rewrite concat_1p.
    unfold hap.
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
    o* smash_right_functor B (pmap_functor B f).
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
      rewrite ap_pp.
      rewrite Smash_rec_beta_gluel.
      by cbn; rewrite !concat_1p, concat_p1, inv_V. }
    intro b.
    serapply dp_paths_FlFr.
    rewrite concat_p1.
    apply moveR_Vp.
    simpl.
    rewrite ap_compose.
    refine (_ @ _).
    { apply ap.
      serapply Smash_rec_beta_gluer. }
    rewrite (ap_compose _ f).
    rewrite (Smash_rec_beta_gluer (fun a : B ->* X => point_eq a) _ b).
    simpl.
    rewrite ap_pp.
    rewrite <- (ap_compose (fun x : B ->* Y => sm x b)).
    simpl.
    pointed_reduce.
    serapply Smash_rec_beta_gluer. }
  simpl.
  by pointed_reduce.
Defined.

Definition pmap_smash_triangle1 {B : pType} (X : pType)
  : pmap_functor B (pmap_smash_counit X) o* pmap_smash_unit (B ->* X)
    ==* pmap_idmap.
Proof.
  serapply Build_pHomotopy.
  { intro f.
    serapply path_pmap.
    serapply Build_pHomotopy.
    1: reflexivity.
    simpl.
    apply whiskerL.
    symmetry.
    refine (concat_p1 _ @_).
    refine (Smash_rec_beta_gluel'  _ _ f (point (pMap B X)) @ _).
    apply concat_p1. }
  simpl.
  rewrite !concat_p1.
  rewrite path_pmap_ap.
  apply ap.
  refine ((ap (issig_phomotopy _ _)^-1)^-1 _).
  serapply path_sigma'.
  { funext b.
    unfold hap.
    cbn.
    rewrite concat_1p.
    
Admitted.

Definition pmap_smash_triangle2 {B : pType} (X : pType)
  : pmap_smash_counit (X ∧ B) o* smash_right_functor B (pmap_smash_unit X)
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
      rewrite (ap_compose (smash_right_functor _ _)).
      rewrite Smash_rec_beta_gluel.
      rewrite ap_pp.
      rewrite <- ap_compose.
      rewrite Smash_rec_beta_gluel.
      simpl.
      rewrite concat_1p.
      apply moveR_Vp.
      by apply moveL_pM. }
    intro b; hnf.
    apply dp_paths_FlFr.
    rewrite ap_idmap.
    rewrite concat_p1.
    rewrite (ap_compose (smash_right_functor _ _)).
    rewrite Smash_rec_beta_gluer.
    rewrite ap_pp.
    rewrite Smash_rec_beta_gluer.
    rewrite concat_p1.
    rewrite <- (ap_compose (fun x => sm x (pmap_idmap b)) _).
    
    simpl.
Admitted.

Global Instance adjunction_smash_pmap (B : pType)
  : Adjunction (functor_smash_right B) (functor_pmap B).
Proof.
  serapply Build_Adjunction.
  + exact pmap_smash_unit.
  + exact pmap_smash_counit.
  + intros ??; exact pmap_smash_unit_natural.
  + intros ??; exact pmap_smash_counit_natural.
  + exact pmap_smash_triangle1.
  + exact pmap_smash_triangle2.
Defined.

Definition smash_adjunction (A B C : pType)
  : (A ∧ B ->* C) <~> (A ->* B ->* C)
  := @equiv_adjunction _ _ _ (adjunction_smash_pmap B) _ _.

Theorem pequiv_smash_adj (A B C : pType)
  : (A ∧ B ->* C) <~>* (A ->* B ->* C).
Proof.
  serapply (@pequiv_adjunction _ _ _ (adjunction_smash_pmap B)).
Defined.

Require Import PointedCategory.Natural.
Require Import PointedCategory.Profunctor.

Global Instance functor_compose : Functor -> Functor -> Functor.
Proof.
  intros F G.
  serapply (Build_Functor (F o G)).
Defined.

Global Instance functor_double_pmap (A B : pType) : Functor.
Proof.
  serapply (functor_compose (functor_pmap A) (functor_pmap B)).
Defined.

Global Instance functor_smash_pmap (A B : pType) : Functor.
Proof.
  serapply (functor_pmap (A ∧ B)).
Defined.

Global Instance natequiv_smash_adjunction (A B : pType)
  : NaturalEquivalence (functor_smash_pmap A B) (functor_double_pmap A B).
Proof.
  simple notypeclasses refine (Build_NaturalEquivalence _ _ _ _).
  1: exact (pequiv_smash_adj A B).
  serapply Build_IsNatural.
  intros X Y f.
  hnf.
  serapply Build_pHomotopy.
  { intro g.
    apply path_pmap.
    serapply Build_pHomotopy.
    { intro a.
      apply path_pmap.
      simpl.
      refine (pmap_precompose_idmap _ @* _ @* (pmap_precompose_idmap _)^*).
      refine (pmap_compose_assoc _ _ _ @* _).
      refine (pmap_compose_assoc _ _ _ @* _).
      apply pmap_postwhisker.
      refine (_ @* (pmap_compose_assoc _ _ _)^*).
      apply pmap_postwhisker.
      refine (pmap_postcompose_idmap _ @* (pmap_precompose_idmap _)^*). }
    hnf.
  
  refine ((pmap_compose_assoc _ _ _)^* @* _).
  
  

Global Instance isnatural_smash_adjunction_C {A B : pType}
  : IsNatural (fun C => @pequiv_smash_adj A B C).
Proof.
  serapply Build_IsNatural.
  intros X Y f.
  cbv beta.
  serapply equiv_adjunction_nat_l _ _ (adjunction_smash_pmap B) _ f
  apply PointedCategory.Adjunction

Defined.

Global Instance natequiv_smash_adjunction
  : NaturalEquivalence

End SmashAdj.