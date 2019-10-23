Require Import Basics.
Require Import Types.
Require Import Cubical.
Require Import Pointed.
Require Import PointedCategory.Bifunctor.
Require Import Homotopy.Smash.

Local Open Scope pointed_scope.
Local Open Scope path_scope.

(* TODO: This should be in smash *)
Notation "X ∧ Y" := (Smash X Y) (at level 20).

Definition smash_bifunctor {A B A' B' : pType}
  : (A ->* B) -> (A' ->* B') -> A ∧ A' ->* B ∧ B'.
Proof.
  intros f g.
  serapply Build_pMap.
  { serapply (Smash_rec (fun a a' => sm (f a) (g a')) auxl auxr); intro.
    + refine (ap _ (point_eq g) @ gluel (f a)).
    + refine (ap (fun x => sm x (g b)) (point_eq f) @ gluer (g b)). }
  cbv; apply ap, ap, path_prod; apply point_eq.
Defined.

Notation "f [∧] g" := (smash_bifunctor f g) (at level 20).

Definition smash_bifunctor_idmap {A A' : pType}
  : (@pmap_idmap A) [∧] (@pmap_idmap A') ==* pmap_idmap.
Proof.
  intros; cbn.
  serapply Build_pHomotopy.
  { serapply (Smash_ind (fun _ _ => 1) 1 1).
    1,2: intros; cbn.
    1,2: apply dp_paths_FFlr.
    1,2: refine (whiskerR (concat_p1 _) _ @ _).
    1,2: rewrite ap_idmap.
    1: rewrite Smash_rec_beta_gluel.
    2: rewrite Smash_rec_beta_gluer.
    1,2: rewrite concat_1p.
    1,2: apply concat_Vp. }
  reflexivity.
Defined.

Lemma smash_bifunctor_compose {A1 A2 A3 B1 B2 B3 : pType}
  (f1 : A1 ->* A2) (f2 : A2 ->* A3) (g1 : B1 ->* B2) (g2 : B2 ->* B3)
  : (f2 o* f1) [∧] (g2 o* g1) ==* (f2 [∧] g2) o* (f1 [∧] g1).
Proof.
  serapply Build_pHomotopy.
  { serapply (Smash_ind (fun _ _ => 1) 1 1).
    1,2: intro.
    1,2: serapply sq_dp^-1.
    1,2: serapply sq_path.
    1,2: rewrite concat_1p,  concat_p1.
    1,2: rewrite (ap_compose (f1 [∧] g1)).
    1: rewrite Smash_rec_beta_gluel.
    2: rewrite Smash_rec_beta_gluer.
    1,2: rewrite ap_pp.
    1: rewrite <- ap_compose.
    2: rewrite <- (ap_compose (fun x : A2 => _ x _)).
    1: rewrite 2 Smash_rec_beta_gluel.
    2: rewrite 2 Smash_rec_beta_gluer.
    1,2: rewrite ap_pp, <- ap_compose.
    1,2: apply concat_p_pp. }
  by simpl; pointed_reduce.
Defined.

Global Instance isbifunctor_smash : IsBifunctor Smash.
Proof.
  serapply Build_IsBifunctor; intros.
  1: by apply smash_bifunctor.
  1: by apply smash_bifunctor_idmap.
  by apply smash_bifunctor_compose.
Defined.

(* We explicitly define the smash bifunctor here *)
Definition bifunctor_smash : Bifunctor
  := @Build_Bifunctor _ isbifunctor_smash.



