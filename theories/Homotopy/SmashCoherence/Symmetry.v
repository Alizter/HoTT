Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import Smash.
Require Import Bifunctor.

Local Open Scope pointed_scope.

Definition smash_swap {X Y : pType} : X ∧ Y ->* Y ∧ X.
Proof.
  serapply Build_pMap.
  2: shelve.
  serapply smash_rec'.
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

Lemma equiv_smash_symm (X Y : pType) : X ∧ Y <~> Y ∧ X.
Proof.
  refine (pequiv_adjointify' smash_swap smash_swap _ _).
  { serapply (smash_ind _ (gluel _) (gluer _)).
    1: reflexivity.
    { intro a.
      rewrite transport_paths_FFlr.
      rewrite concat_p1.
      rewrite smash_rec_beta_gluel.
      rewrite ap_V.
      rewrite smash_rec_beta_glue.
      unfold glue.
      unfold gluel'.
      hott_simpl.
      rewrite inv_pp.
      rewrite inv_V.
      by apply moveR_pM. }
    intro b.
    rewrite transport_paths_FFlr.
    rewrite concat_p1.
    rewrite smash_rec_beta_gluer.
    rewrite smash_rec_beta_glue.
    unfold glue.
    unfold gluel'.
    unfold gluer'.
    hott_simpl. }
  serapply (smash_ind _ (gluel _) (gluer _)).
  1: reflexivity.
  { intro a.
    rewrite transport_paths_FFlr.
    rewrite concat_p1.
    rewrite smash_rec_beta_gluel.
    rewrite ap_V.
    rewrite smash_rec_beta_glue.
    unfold glue.
    unfold gluel'.
    hott_simpl.
    rewrite inv_pp.
    rewrite inv_V.
    by apply moveR_pM. }
  intro b.
  rewrite transport_paths_FFlr.
  rewrite concat_p1.
  rewrite smash_rec_beta_gluer.
  rewrite smash_rec_beta_glue.
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
  { serapply smash_ind.
    { intros a b.
      reflexivity. }
    1,2: pointed_reduce; reflexivity.
    1,2: shelve. }
  by cbv; pointed_reduce.
  Unshelve.
  { intro a; cbn.
    rewrite transport_paths_FlFr.
    rewrite ap_compose.
    rewrite smash_rec_beta_gluel.
    rewrite ap_V.
    rewrite smash_rec_beta_glue.
    rewrite ap_compose.
    rewrite smash_rec_beta_gluel.
    rewrite !transport_paths_Fl.
    rewrite ap_pp.
    rewrite smash_rec_beta_gluel.
    pointed_reduce.
    unfold glue, gluel', gluer'.
    hott_simpl.
    apply moveR_pV.
    refine (concat_p1 _ @ _ @ (concat_1p _)^).
    reflexivity. }
  { intro a; cbn.
    rewrite transport_paths_FlFr.
    rewrite ap_compose.
    rewrite smash_rec_beta_gluer.
    rewrite smash_rec_beta_glue.
    rewrite ap_compose.
    rewrite smash_rec_beta_gluer.
    rewrite !transport_paths_Fl.
    rewrite ap_pp.
    rewrite smash_rec_beta_gluer.
    pointed_reduce.
    unfold glue, gluel', gluer'.
    hott_simpl.
    apply moveR_Mp.
    rewrite inv_pp, inv_V.
    refine (_  @ (concat_1p _)^ @ (concat_p1 _)^).
    reflexivity. }
Qed.

