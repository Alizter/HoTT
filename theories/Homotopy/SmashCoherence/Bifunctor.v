Require Import Basics.
Require Import Types.
Require Import FunextAxiom.
Require Import Pointed.
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
    { serapply (smash_rec (fun a a' => sm (f a) (g a')) auxl auxr); intro;
     (apply (transport (fun x => _ _ x = _) (point_eq _)^), gluel ||
      apply (transport (fun x => _ x _ = _) (point_eq _)^), gluer). }
    pointed_reduce; reflexivity. }
  { intros; cbn.
    serapply Build_pHomotopy.
    { serapply (smash_ind (fun _ _ => 1) 1 1);
      intros; cbn; rewrite transport_paths_FFlr, ap_idmap;
      (rewrite smash_rec_beta_gluel || rewrite smash_rec_beta_gluer);
      rewrite concat_p1; apply concat_Vp. }
    reflexivity. }
  intros; cbn.
  serapply Build_pHomotopy.
  { (* We write this all as one tactic so we don't have to
       write it twice. If you wish to inspect whats going on
       you will have to break it apart. *)
    serapply (smash_ind (fun _ _ => 1) 1 1);
    intros; cbn;
    rewrite transport_paths_FlFr;
    (rewrite smash_rec_beta_gluel || rewrite smash_rec_beta_gluer);
    rewrite transport_paths_FlFr;
    rewrite (ap_compose (smash_rec _ _ _ _ _));
    (rewrite smash_rec_beta_gluel || rewrite smash_rec_beta_gluer);
    rewrite transport_paths_FlFr;
    rewrite concat_p1;
    rewrite ap_V, inv_V;
    rewrite ap_const, concat_p1;
    apply moveR_Vp;
    refine (_ @ (concat_p1 _)^);
    rewrite ap_V, inv_V;
    rewrite ap_const, concat_p1;
    rewrite (ap_pp (smash_rec _ _ _ _ _));
    (rewrite smash_rec_beta_gluel || rewrite smash_rec_beta_gluer);
    rewrite transport_paths_FlFr;
    rewrite ap_V, inv_V;
    rewrite ap_const, concat_p1;
    rewrite ap_pp;
    rewrite concat_p_pp;
    apply whiskerR, whiskerR;
    rewrite <- ap_compose;
    (rewrite <- (ap_compose (sm _)) ||
    rewrite <- (ap_compose (fun x : B => sm x _)));
    reflexivity. }
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
  + serapply (smash_ind (fun _ _ => 1) 1 1).
    1,2: intro; cbn.
    1,2: refine (transport_paths_FlFr _ _ @ _).
    1,2: refine (transport (fun x => x @ _ = _) (concat_p1 _)^ _).
    1,2: apply moveR_Vp.
    1,2: refine (_ @ (concat_p1 _)^).
    1: refine (_ @ (smash_rec_beta_gluel _ _ _)^).
    2: refine (_ @ (smash_rec_beta_gluer _ _ _)^).
    1: refine (ap_compose (smash_rec (fun a a' => sm (f1 a) (g1 a'))
      auxl auxr _ _) _ (gluel a) @ _).
    2: refine (ap_compose (smash_rec (fun a a' => sm (f1 a) (g1 a'))
      auxl auxr _ _) _ (gluer b) @ _).
    1: refine (ap (ap _) (smash_rec_beta_gluel _ _ _) @ _).
    2: refine (ap (ap _) (smash_rec_beta_gluer _ _ _) @ _).
    1,2: pointed_reduce.
    1: erapply smash_rec_beta_gluel.
    erapply smash_rec_beta_gluer.
  + pointed_reduce.
    hott_simpl.
Defined.