Require Import Basics Types Pointed Cubical.
Require Import Smash.
Require Import Coherence.

Local Open Scope pointed_scope.
Local Open Scope path_scope.

(* TODO: This should be in smash *)
Notation "X ∧ Y" := (Smash X Y) (at level 20).

Global Instance isbifunctor_smash : IsBifunctor Smash.
Proof.
  serapply Build_IsBifunctor.
  { intros A B A' B' f g.
    serapply Build_pMap.
    { serapply (Smash_rec (fun a a' => sm (f a) (g a')) auxl auxr); intro.
      + apply (transport (fun x => _ _ x = _) (point_eq _)^), gluel.
      + apply (transport (fun x => _ x _ = _) (point_eq _)^), gluer. }
    pointed_reduce; reflexivity. }
  { intros; cbn.
    serapply Build_pHomotopy.
    { serapply (Smash_ind (fun _ _ => 1) 1 1).
      1,2: intros; cbn.
      1,2: apply dp_paths_FFlr; rewrite ap_idmap.
      1: rewrite Smash_rec_beta_gluel.
      2: rewrite Smash_rec_beta_gluer.
      1,2: hott_simpl. }
    reflexivity. }
  intros; cbn.
  serapply Build_pHomotopy.
  { serapply (Smash_ind (fun _ _ => 1) 1 1).
    1,2: intros; cbn.
    1,2: apply dp_paths_FlFr.
    1: rewrite Smash_rec_beta_gluel.
    2: rewrite Smash_rec_beta_gluer.
    1,2: rewrite (ap_compose (Smash_rec _ _ _ _ _)).
    1: rewrite Smash_rec_beta_gluel.
    2: rewrite Smash_rec_beta_gluer.
    1: rewrite (transport_paths_FlFr (point_eq f')^).
    2: rewrite (transport_paths_FlFr (point_eq f)^).
    1,2: hott_simpl.
    1: rewrite (ap_pp _ _ (gluel _)).
    2: rewrite (ap_pp _ _ (gluer _)).
    1: rewrite Smash_rec_beta_gluel.
    2: rewrite Smash_rec_beta_gluer.
    1,2: pointed_reduce.
    1,2: apply concat_Vp. }
  (* This works but takes a long time *)
  pointed_reduce.
  hott_simpl.
Defined.

(* We explicitly define the smash bifunctor here *)
Definition bifunctor_smash {A A' B B' : pType}
  := @F_bifunctor Smash _ A A' B B'.

Notation "f [∧] g" := (bifunctor_smash f g) (at level 20).

Lemma bifunctor_smash_interchange {A1 A2 A3 B1 B2 B3 : pType}
  (f1 : A1 ->* A2) (f2 : A2 ->* A3) (g1 : B1 ->* B2) (g2 : B2 ->* B3)
  : (f2 o* f1) [∧] (g2 o* g1) ==* (f2 [∧] g2) o* (f1 [∧] g1).
Proof.
  serapply Build_pHomotopy.
  + serapply (Smash_ind (fun _ _ => 1) 1 1).
    1,2: intro; cbn.
    1,2: apply dp_paths_FlFr.
    1,2: rewrite concat_p1.
    1,2: apply moveR_Vp.
    1,2: refine (_ @ (concat_p1 _)^).
    1: refine (_ @ (Smash_rec_beta_gluel _ _ _)^).
    2: refine (_ @ (Smash_rec_beta_gluer _ _ _)^).
    1: refine (ap_compose (Smash_rec (fun a a' => sm (f1 a) (g1 a'))
      auxl auxr _ _) _ (gluel a) @ _).
    2: refine (ap_compose (Smash_rec (fun a a' => sm (f1 a) (g1 a'))
      auxl auxr _ _) _ (gluer b) @ _).
    1: refine (ap (ap _) (Smash_rec_beta_gluel _ _ _) @ _).
    2: refine (ap (ap _) (Smash_rec_beta_gluer _ _ _) @ _).
    1,2: pointed_reduce.
    1: erapply Smash_rec_beta_gluel.
    erapply Smash_rec_beta_gluer.
  + pointed_reduce.
    hott_simpl.
Defined.
