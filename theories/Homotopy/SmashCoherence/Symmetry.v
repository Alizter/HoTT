Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import Smash.
Require Import Bifunctor.
Require Import Cubical.

Local Open Scope pointed_scope.

Require Import pYoneda.
Require Import SmashAdj.


Definition pmap_smash_swap {X Y : pType} : X ∧ Y ->* Y ∧ X.
Proof.
  serapply Build_pMap.
  2: shelve.
  serapply Smash_rec'.
  + intros a b.
    exact (sm b a).
  + intro a.
    symmetry.
    apply glue.
  + intro b.
    apply glue.
  + cbn.
    change ((glue (point Y) (point X))^ = 1^).
    apply inverse2.
    unfold glue, gluel', gluer'.
    refine (whiskerL _ (concat_pV _) @ _).
    refine (whiskerR (concat_pV _) _).
  + cbn.
    unfold glue, gluel', gluer'.
    refine (whiskerL _ (concat_pV _) @ _).
    refine (whiskerR (concat_pV _) _).
  Unshelve.
  hott_simpl.
Defined.

Global Instance smash_symm : Symmetric Smash.
Proof.
  intros X Y.
  apply pmap_smash_swap.
Defined.

Lemma equiv_smash_symm (X Y : pType) : X ∧ Y <~> Y ∧ X.
Proof.
  refine (pequiv_adjointify' pmap_smash_swap pmap_smash_swap _ _).
  { serapply (Smash_ind _ (gluel _) (gluer _)).
    1: reflexivity.
    { intro a.
      apply dp_paths_FFlr.
      rewrite concat_p1.
      rewrite Smash_rec_beta_gluel.
      rewrite ap_V.
      rewrite Smash_rec_beta_glue.
      unfold glue.
      unfold gluel'.
      hott_simpl.
      rewrite inv_pp.
      rewrite inv_V.
      by apply moveR_pM. }
    intro b.
    apply dp_paths_FFlr.
    rewrite concat_p1.
    rewrite Smash_rec_beta_gluer.
    rewrite Smash_rec_beta_glue.
    unfold glue.
    unfold gluel'.
    unfold gluer'.
    hott_simpl. }
  serapply (Smash_ind _ (gluel _) (gluer _)).
  1: reflexivity.
  { intro a.
    apply dp_paths_FFlr.
    rewrite concat_p1.
    rewrite Smash_rec_beta_gluel.
    rewrite ap_V.
    rewrite Smash_rec_beta_glue.
    unfold glue.
    unfold gluel'.
    hott_simpl.
    rewrite inv_pp.
    rewrite inv_V.
    by apply moveR_pM. }
  intro b.
  apply dp_paths_FFlr.
  rewrite concat_p1.
  rewrite Smash_rec_beta_gluer.
  rewrite Smash_rec_beta_glue.
  unfold glue.
  unfold gluel'.
  unfold gluer'.
  hott_simpl.
Defined.

Definition pequiv_smash_symm (X Y : pType) : X ∧ Y <~>* Y ∧ X.
Proof.
  serapply Build_pEquiv'.
  1: apply equiv_smash_symm.
  reflexivity.
Defined.

Local Notation σ := pequiv_smash_symm.

Definition smash_symm_nat (A A' B B' : pType) (f : A ->* A')
  (g : B ->* B') : g [∧] f o* σ A B ==* σ A' B' o* f [∧] g.
Proof.
  serapply Build_pHomotopy.
  { serapply Smash_ind.
    { intros a b.
      reflexivity. }
    1,2: pointed_reduce; reflexivity.
    1,2: shelve. }
  by cbv; pointed_reduce.
  Unshelve.
  { intro a; cbn.
    apply dp_paths_FlFr.
    rewrite ap_compose.
    rewrite Smash_rec_beta_gluel.
    rewrite ap_V.
    rewrite Smash_rec_beta_glue.
    rewrite ap_compose.
    rewrite Smash_rec_beta_gluel.
    rewrite !transport_paths_Fl.
    rewrite ap_pp.
    rewrite Smash_rec_beta_gluel.
    pointed_reduce.
    unfold glue, gluel', gluer'.
    hott_simpl.
    apply moveR_pV.
    refine (concat_p1 _ @ _ @ (concat_1p _)^).
    reflexivity. }
  { intro a; cbn.
    apply dp_paths_FlFr.
    rewrite ap_compose.
    rewrite Smash_rec_beta_gluer.
    rewrite Smash_rec_beta_glue.
    rewrite ap_compose.
    rewrite Smash_rec_beta_gluer.
    rewrite !transport_paths_Fl.
    rewrite ap_pp.
    rewrite Smash_rec_beta_gluer.
    pointed_reduce.
    unfold glue, gluel', gluer'.
    hott_simpl.
    apply moveR_Mp.
    rewrite inv_pp, inv_V.
    refine (_  @ (concat_1p _)^ @ (concat_p1 _)^).
    reflexivity. }
Qed.

