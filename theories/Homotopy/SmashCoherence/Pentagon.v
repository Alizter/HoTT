Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import PointedCategory.Functor.
Require Import PointedCategory.Natural.
Require Import PointedCategory.pMapFunctor.
Require Import Homotopy.SmashCoherence.SmashAdj.
Require Import Homotopy.SmashCoherence.Bifunctor.
Require Import Homotopy.SmashCoherence.Associator.
Require Import Homotopy.Smash.


Local Open Scope pointed_scope.

Local Notation id := pmap_idmap.
Local Notation α := pequiv_smash_assoc.
Local Notation ξ := natequiv_smash_adj.

Section Pentagon.

  Context `{Funext}.

  Definition natequiv_smash_assoc4 {A B C D : pType}
    : (functor_pmap (A ∧ (B ∧ (C ∧ D))))
      ~ (functor_pmap (((A ∧ B) ∧ C) ∧ D)).
  Proof.
    refine (natequiv_smash_adj oN _).
    refine (functor_postwhisker _ natequiv_smash_adj oN _).
    refine (functor_postwhisker _
      (functor_postwhisker _  natequiv_smash_adj) oN _).
    refine (natequiv_functor_compose_assoc _ _ _ oN _).
    refine (functor_prewhisker _ natequiv_smash_adj^N oN _).
    refine (natequiv_functor_compose_assoc _ _ _ oN _).
    refine (functor_prewhisker _ natequiv_smash_adj^N oN _).
    apply natequiv_smash_adj^N.
  Defined.

  Definition natequiv_smash_assocR {A B C D : pType}
    : (functor_pmap ((A ∧ (B ∧ C)) ∧ D))
      ~ (functor_pmap (((A ∧ B) ∧ C) ∧ D)).
  Proof.
    refine (natequiv_smash_adj oN _).
    refine (functor_prewhisker _ natequiv_smash_assoc oN _).
    apply natequiv_smash_adj^N.
  Defined.

  Definition natequiv_smash_assocL {A B C D : pType}
    : (functor_pmap (A ∧ (B ∧ (C ∧ D))))
      ~ (functor_pmap (A ∧ ((B ∧ C) ∧ D))).
  Proof.
    refine (natequiv_smash_adj oN _).
    refine (functor_postwhisker _ natequiv_smash_assoc oN _).
    apply natequiv_smash_adj^N.
  Defined.

  Lemma phomotopy_pentagon1 {A B C D : pType}
    : α A B (C ∧ D) o* α (A ∧ B) C D ==* pYoneda natequiv_smash_assoc4.
  Proof.
    unfold pequiv_smash_assoc.
    refine (pYoneda_compose _ _ @* _).
    apply pYoneda_2functor.
    unfold natequiv_smash_assoc.
    rewrite <- 4 natequiv_p_pp.
    rewrite (natequiv_p_pp ξ^N ξ).
    rewrite (natequiv_Vp ξ).
    rewrite natequiv_1p.
    unfold natequiv_smash_assoc4.
    pose (@ne_isnatural _ _ (@natequiv_smash_adj _ A B)).
    unfold IsNatural in i.
    apply natequiv_whiskerL.
    apply natequiv_whiskerL.
    rewrite 8 natequiv_p_pp.
    apply natequiv_whiskerR.
    apply natequiv_whiskerR.
    apply natequiv_whiskerR.
  Admitted.

  Lemma phomotopy_pentagon2 {A B C D : pType}
    : pYoneda natequiv_smash_assoc4
    ==* (pYoneda natequiv_smash_assocL o* α A (B ∧ C) D)
      o* pYoneda natequiv_smash_assocR.
  Proof.
    refine (_ @* pmap_prewhisker _ _^*).
    2: apply pYoneda_compose.
    refine (_ @* _^*).
    2: apply pYoneda_compose.
    apply pYoneda_2functor.
    unfold natequiv_smash_assocL.
    unfold natequiv_smash_assoc.
    
    rewrite <- 7 natequiv_p_pp.
    rewrite (natequiv_p_pp _ ξ).
    rewrite natequiv_Vp.
    rewrite natequiv_1p.
    unfold natequiv_smash_assocR.
    rewrite (natequiv_p_pp _ ξ).
    rewrite natequiv_Vp.
    rewrite natequiv_1p.
    
    
  Admitted.

  Lemma phomotopy_pentagon3 {A B C D : pType}
    : (pYoneda natequiv_smash_assocL o* α A (B ∧ C) D)
      o* pYoneda natequiv_smash_assocR
    ==* (id [∧] α B C D o* α A (B ∧ C) D) o* α A B C [∧] id.
  Proof.
    refine (pmap_prewhisker _ (pmap_prewhisker _ _)
      @* pmap_postwhisker _ _).
  Admitted.

  Theorem smash_pentagon (A B C D : pType)
    : α A B (C ∧ D) o* α (A ∧ B) C D
    ==* (id [∧] (α B C D) o* α A (B ∧ C) D) o* (α A B C) [∧] id.
  Proof.
    transitivity (pYoneda (@natequiv_smash_assoc4 A B C D)).
    1: apply phomotopy_pentagon1.
    transitivity (pYoneda natequiv_smash_assocL
      o* α A (B ∧ C) D o* pYoneda natequiv_smash_assocR).
    1: apply phomotopy_pentagon2.
    apply phomotopy_pentagon3.
  Defined.




