Require Import Basics Types Pointed.
Require Import Homotopy.Smash.
Require Import Homotopy.Wedge.
Require Import EquivalenceVarieties.
Require Import Fibrations.

(** Hilton-Milnor splitting *)

Local Open Scope pointed_scope.
Local Open Scope path_scope.

Lemma isequiv_hfiber {A B C : Type} (f : A -> C) (g : B -> C) (h : A -> B)
  (s : f == g o h) (c : C)
  (p : IsEquiv (@functor_hfiber _ _ _ _ f g h idmap s c))
  : IsEquiv h.
Proof.
Admitted.

Lemma isequiv_splitting_lemma {A B : pType} (f : A ->* B)
  (g : loops B ->* loops A)
  (gissect : Sect g (loops_functor f))
  : IsEquiv ((uncurry concat o functor_prod pr1 g)
      : pfiber (loops_functor f) * loops B -> loops A).
Proof.
  simple notypeclasses refine (isequiv_hfiber snd (loops_functor f)
    (uncurry concat o functor_prod pr1 g) _ _ _).
  { unfold uncurry.
    intros [[x y] z].
    unfold snd.
    symmetry.
    refine (loops_functor_pp _ _ _ @ _).
    unfold functor_prod.
    unfold fst, snd, pr1.
    refine (whiskerL _ _ @ _).
    1: apply gissect.
    refine (whiskerR y _ @ concat_1p _). }
  1: exact (point _).
  serapply isequiv_adjointify.
  { intros x.
    exact ((x, _); x.2). }
  { intros [x p].
    serapply path_sigma.
    { simpl.
      unfold uncurry.
      simpl.
      refine (whiskerL _ _ @ concat_p1 _).
      refine (ap g p @ _).
      apply (point_eq g). }
    rewrite transport_paths_Fl.
    cbn in *.
    apply moveR_Vp.
    rewrite ap_idmap.
    apply whiskerR.
    rewrite inv_V.
    rewrite (ap_compose _ (concat _)).
    rewrite (ap_compose _ (fun x => concat x _)).
    
    
    pointed_reduce.
    
    
    unfold loops_
    hott_simpl.
    rewrite ? ap_pp.
    
    
Admitted.

(** TODO: move to Pointed.Loops *)
Definition pfiber_loops_functor {A B : pType} (f : A ->* B)
  : loops (pfiber f) <~>* pfiber (loops_functor f).
Proof.
  serapply Build_pEquiv'.
  { symmetry.
    etransitivity.
    2: serapply equiv_path_sigma.
    simpl; unfold hfiber.
    serapply equiv_functor_sigma_id.
    intro p; cbn.
    rewrite transport_paths_Fl.
    refine (_ oE equiv_moveL_Mp _ _ _).
    refine (equiv_moveR_Vp _ _ _ oE _).
    rewrite concat_p1.
    apply equiv_path_inverse. }
  by pointed_reduce.
Defined.

(** TODO: move to Pointed.pEquiv *)
Definition pmap_functor_prod {A B C D : pType}
  (f : A ->* C) (g : B ->* D) : A * B ->* C * D.
Proof.
  serapply Build_pMap.
  1: exact (functor_prod f g).
  apply path_prod.
  1,2: apply point_eq.
Defined.

Definition pequiv_functor_prod {A B C D : pType}
  (f : A <~>* C) (g : B <~>* D)
  : A * B <~>* C * D
  := Build_pEquiv _ _ (pmap_functor_prod f g) _.

Definition pequiv_splitting_lemma {A B : pType} (f : A ->* B)
  (g : loops B ->* loops A) (gissect : pSect g (loops_functor f))
  : loops (pfiber f) * loops B <~>* loops A.
Proof.
  transitivity (pfiber (loops_functor f) * loops B).
  { serapply pequiv_functor_prod.
    2: reflexivity.
    apply pfiber_loops_functor. }
  serapply Build_pEquiv'.
  { ntc_rapply Build_Equiv.
    exact (isequiv_splitting_lemma f g gissect). }
  refine (_ @ concat_p1 _).
  apply whiskerL.
  apply (point_eq g).
Defined.

Theorem pfiber_wedge_incl {X Y : pType}
  : pfiber (wedge_incl X Y) <~>* psusp (Smash (loops X) (loops Y)).
Proof.
  
Admitted.

Definition pmap_loops_concat {X : pType}
  : loops X * loops X ->* loops X.
Proof.
  serapply Build_pMap.
  1: exact (uncurry concat).
  reflexivity.
Defined.

Definition pequiv_prod_symm (X Y : pType) : X * Y <~>* Y * X.
Proof.
  serapply Build_pEquiv'.
  1: apply equiv_prod_symm.
  reflexivity.
Defined.

Definition pmap_prod_diag (X : pType) : X ->* X * X.
Proof.
  serapply Build_pMap.
  1: exact (fun x => (x, x)).
  reflexivity.
Defined.

Lemma path_prod_ap_ptype {A B : pType}
  {a a' : A} (p : a = a') {b b' : B} (q : b = b')
  : ap (fun x => (x, point _)) p @ ap (fun x => (point _, x)) q
    = path_prod' p q.
Proof.
  by destruct p, q.
Defined.

Lemma pointed_prod_foo {X Y : pType} (p : loops X) (q : loops Y)
  : ap (fun x : X => (x, point Y)) p @ ap (fun x : Y => (point X, x)) q
    = path_prod' p q.
Proof.
  apply path_prod_ap_ptype.
Defined.

Lemma path_prod_pp' {A B : Type} {a a' a'' : A} {b b' b'' : B}
  (p : a = a') (p' : a' = a'') (q : b = b') (q' : b' = b'')
  : path_prod' (p @ p') (q @ q') = path_prod' p q @ path_prod' p' q'.
Proof.
  apply path_prod_pp.
Defined.

Lemma path_prod_V' {A B : Type} {a a' : A} {b b' : B}
  (p : a = a') (q : b = b')
  : path_prod' p^ q^ = (path_prod' p q)^.
Proof.
  apply path_prod_V.
Defined.

Lemma foo_b {X Y A B : pType} (p : loops X) (q : loops Y)
  {f : X ->* A} {g : Y ->* B} 
  : loops_functor (pmap_functor_prod f g) (path_prod' p q)
    = path_prod' (loops_functor f p) (loops_functor g q).
Proof.
  refine (_ @ (path_prod_pp' _ _ _ _)^).
  refine (_ @ whiskerR (path_prod_V' _ _)^ _).
  apply whiskerL.
  refine (ap (fun x => x @ _) _ @ (path_prod_pp' _ _ _ _)^).
  apply ap_functor_prod.
Defined.

Lemma foo_c {X Y : pType} (p : loops X) (q : loops Y)
  : (pmap_loops_concat
     (loops_prod (X V Y) (X V Y)
        (path_prod' (loops_functor winl p) (loops_functor winr q))))
    = ap winl p @ (wpp @ (ap winr q @ wpp^)).
Proof.
  simpl; unfold uncurry.
  rewrite ap_fst_path_prod.
  rewrite ap_snd_path_prod.
  rewrite concat_1p, concat_p1, inv_V.
  reflexivity.
Defined.

Lemma foo_a {X Y : pType}
  : (loops_functor (wedge_incl X Y)
    o* ((pmap_loops_concat o* loops_prod (X V Y) (X V Y))
    o* loops_functor (pmap_functor_prod winl winr)))
    o* (loops_prod X Y)^-1* ==* (loops_prod X Y)^-1*.
Proof.
  serapply Build_pHomotopy.
  { intros [p q].
    unfold pmap_compose, pointed_fun.
    change (loops_functor (wedge_incl X Y) (pmap_loops_concat
      (loops_prod (X V Y) (X V Y) (loops_functor (pmap_functor_prod
          winl winr) (path_prod' p q)))) = (path_prod' p q)).
    refine (ap _ (ap _ (ap _ (foo_b _ _))) @ _).
    refine (ap _ (foo_c _ _) @ _).
    unfold loops_functor.
    unfold pointed_fun.
    
    rewrite 3 ap_pp.
    rewrite <- (ap_compose winl).
    rewrite <- (ap_compose winr).
    rewrite ap_V.
    
    rewrite Wedge_rec_beta_wpp.
    simpl.
    hott_simpl.
    apply pointed_prod_foo. }
  
(*  simpl. *)
Admitted.


Theorem hilton_milnor {X Y : pType}
  : loops (Wedge X Y) <~>* loops X * loops Y
      * loops (psusp (Smash (loops X) (loops Y))).
Proof.
  etransitivity.
  2: { erapply (pequiv_functor_prod (C := loops X * loops Y)).
    1: apply loops_prod.
    reflexivity. }
  etransitivity.
  { symmetry.
    serapply (pequiv_splitting_lemma (wedge_incl _ _)).
    { refine (_ o* loops_functor (B:= Wedge X Y * Wedge X Y) _).
      2: apply (pmap_functor_prod winl winr).
      refine (_ o* loops_prod _ _).
      apply pmap_loops_concat. }
    unfold pSect.
    refine ((pmap_precompose_idmap _)^* @* _).
    refine (pmap_postwhisker _ (peissect (loops_prod _ _))^* @* _).
    refine (_ @* peissect (loops_prod _ _)).
    refine ((pmap_compose_assoc _ _ _)^* @* _).
    apply pmap_prewhisker.
    apply foo_a. }
  refine (_ o*E pequiv_prod_symm _ _).
  apply pequiv_functor_prod.
  1: reflexivity.
  apply pequiv_loops_functor.
  apply pfiber_wedge_incl.
Defined.


