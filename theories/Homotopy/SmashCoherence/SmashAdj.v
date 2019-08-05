Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import Smash.
Require Import Coherence.
Require Import Bifunctor.

Local Open Scope pointed_scope.
Local Open Scope path_scope.

(* TODO: This should be in smash *)
Notation "X ∧ Y" := (Smash X Y) (at level 20).
Local Notation "A '->*' B" := (Build_pType (A ->* B) _).

Section SmashAdj.

Context `{Funext}.

Definition smash_pmap_unit {A B : pType} : A ->* (B ->* (A ∧ B)).
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

Global Instance isfunctor_smash_right (B : pType)
  : IsFunctor (fun x => x ∧ B) := _.

Global Instance isfunctor_pmap_right (B : pType)
  : IsFunctor (fun y => B ->* y).
Proof.
  serapply Build_IsFunctor.
  { intros X Y f.
    serapply Build_pMap.
    { intro g.
      exact (f o* g). }
    serapply path_pmap.
    exact (pmap_postcompose_const f). }
  { intro A.
    serapply Build_pHomotopy.
    { cbn; intro.
      apply path_pmap, pmap_postcompose_idmap. }
    { refine (concat_p1 _). } }
  intros X Y Z f' f.
  serapply Build_pHomotopy.
  { cbn; intro.
    apply path_pmap, pmap_compose_assoc. }
  simpl.
  rewrite path_pmap_ap.
  rewrite path_pmap_pp.
  rewrite path_pmap_pp.
  apply ap.
  pointed_reduce.
  cbv.
Admitted.


(* How can we get coq to coerce into pTypes?
   (A ->* B) is a pType so can't coq guess this? *)
(* This should be natural in A B and C *)
Theorem smash_adjunction {A B C : pType}
  : (A ∧ B ->* C) <~>* (A ->* B ->* C).
Proof.
  


(*   serapply Build_pEquiv'.
  { serapply equiv_adjointify.
    { intro f.
      serapply Build_pMap.
      { serapply smash_rec'.
        1: apply f.
        { intro a; cbn.
          refine (point_eq (f a) @ _).
          symmetry.
          apply point_eq. }
        { intro b; cbn.
          destruct ((equiv_path_pmap _ _)^-1%equiv (point_eq f))
            as [g _].
          refine (g b @ _).
          symmetry.
          apply (point_eq (f (point A))). }
        1: apply concat_pV.
        cbn.
        apply moveR_pV.
        refine (_ @ (concat_1p _)^).
        destruct f as [f p].
        cbn in *.
        set (g := f (point A)).
        change (g = ispointed_pmap) in p.
        clearbody g; clear f.
        destruct g as [g q].
        cbn in *.
        pointed_reduce.
        cbv.
        rewrite <- (eisretr (equiv_path_pmap _ _) p).
        set (p' := ((equiv_path_pmap _ ispointed_pmap)^-1)%function p).
        clearbody p'; clear p.
        destruct p' as [p' j].
        cbn in *.
        destruct j.
        hott_simpl.
        set (g ispointed_type0).
        admit. }
      cbv; apply point_eq. }(* 
    { serapply path_pmap.
      { pointed_reduce.
        serapply Build_pHomotopy.
        { serapply (smash_ind (fun _ _ => 1) 1 1);
          intros; cbn in *;
          refine (transport_paths_Fl _ _ @ _);
          apply moveR_Vp;
          refine (_ @ (concat_p1 _)^);
          (refine (_ @ (smash_rec_beta_gluel _ _ _)^) ||
           refine (_ @ (smash_rec_beta_gluer _ _ _)^) );
          reflexivity. }
        reflexivity. } } *)
    { intro f.
      serapply Build_pMap.
      { intro a.
        refine (Build_pMap _ _ (fun b => f (sm a b)) _).
        refine (ap f (gluel a) @ _ @ point_eq f).
        apply ap; symmetry; apply gluel. }
      apply path_pmap.
      serapply Build_pHomotopy.
      { intro b.
        refine (ap f (gluer b) @ _ @ point_eq f).
        apply ap; symmetry; apply gluer. }
      cbn.
      serapply (transport (fun x => ((_ @ x) @ _) @ _ = _)).
      2: symmetry; apply ap_V.
      serapply (transport (fun x => _ = (_ @ x) @ _)).
      2: symmetry; apply ap_V.
      refine (concat_p1 _ @ _).
      serapply (transport (fun x => x @ _ = _)).
      2: symmetry; apply concat_pV.
      serapply (transport (fun x => _ = x @ _)).
      2: symmetry; apply concat_pV.
      reflexivity. }
    { intro f.
      serapply path_pmap.
      serapply Build_pHomotopy.
      { serapply (smash_ind (fun _ _ => 1)).
        { pointed_reduce.
          cbv.
          apply ap.
          exact (@gluel
            {| pointed_type := A; ispointed_type := ispointed_type1 |}
            {| pointed_type := B; ispointed_type := ispointed_type0 |}
            (point _)). }
        { pointed_reduce.
          cbv.
          apply ap.
          exact (@gluer
            {| pointed_type := A; ispointed_type := ispointed_type1 |}
            {| pointed_type := B; ispointed_type := ispointed_type0 |}
            (point _)). }
        { intro a.
          optimize_heap.
          rewrite transport_paths_FlFr.
          rewrite transport_paths_FlFr. *)
Admitted.

End SmashAdj.