Require Import Basics.
Require Import Types.
Require Import Pointed.
(* Require Import Coherence. *)
(* Require Import pMapFunctor. *)
Require Import Homotopy.SmashCoherence.PointedCategory.Functor.
Require Import Homotopy.SmashCoherence.PointedCategory.Natural.

(* The yoneda lemma for pointed types. *)

Local Open Scope pointed_scope.

Local Notation id := pmap_idmap.

Lemma pYoneda (A B : pType) (phi : forall X, (B ->* X) <~>* (A ->* X))
  {p : IsNatural phi} : A <~>* B.
Proof.
  set (to := phi B id).
  set (fr := (phi A)^-1 id).
(*   destruct p as [p].
  serapply (pequiv_adjointify to fr).
  { simpl.
    serapply Build_pHomotopy.
    { apply ap10.
      refine (_ @ eisretr (phi A) id).
      intro x.
      simpl.
      unfold to, fr.
       (eisretr (phi A) id) x
      apply moveR_equiv_M.
  
    transitivity ((phi B)^-1 (to o* id)).
    2: { transitivity ((phi B)^-1 ((phi B) id)).
          { rewrite path_pmap_precompose_idmap.
            reflexivity. }
          apply phomotopy_paths.
          apply peissect. }
      rewrite path_pmap_precompose_idmap.
      apply phomotopy_paths.
      unfold to.
      unfold fr.
      refine (peissect
          
    serapply Build_pHomotopy.
    { apply 
    
       intro.
      refine ( *)
    
Admitted.