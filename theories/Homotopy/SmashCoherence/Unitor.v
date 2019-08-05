Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import Smash.
Require Import HIT.Spheres.
Require Import HIT.Suspension.

Require Import Bifunctor.
Require Import Symmetry.
Require Import Associator.
Require Import SmashAdj.

Local Open Scope pointed_scope.

Local Notation id := pmap_idmap.
Local Notation "A '->*' B" := (Build_pType (A ->* B) _).

Definition functor_pmap {A B C D : pType} (f : B ->* A) (g : C ->* D)
  : (A ->* C) ->* B ->* D.
Proof.
  serapply Build_pMap.
  { intros i.
    refine (g o* i o* f). }
  serapply path_pmap.
  pointed_reduce.
  (* Have to do it twice because pointed_reduce is not used to pointed pmaps *)
  pointed_reduce.
  reflexivity.
Defined.

(* TODO: Clean up *)
Definition pequiv_functor_pmap {A B C D : pType} (f : B <~>* A) (g : C <~>* D)
  : (A ->* C) <~>* (B ->* D).
Proof.
  serapply pequiv_adjointify'.
  1: apply (functor_pmap f g).
  { serapply Build_pMap.
    1: refine (fun h => g^-1* o* h o* f^-1*).
    serapply path_pmap.
    serapply Build_pHomotopy.
    1: intro x; apply point_eq.
    cbn.
    unfold moveR_equiv_V.
    pointed_reduce.
    hott_simpl. }
  { intro.
    serapply path_pmap.
    serapply Build_pHomotopy.
    { intro; cbv.
      refine (eisretr _ _ @ _).
      apply ap, eissect. }
    pointed_reduce.
    unfold moveR_equiv_V.
    rewrite ap_pp.
    pointed_reduce.
    rewrite !ap_pp.
    rewrite (ap_compose x g^-1).
    rewrite concat_p_pp.
    rewrite <- ap_pp.
    rewrite <- (ap_pp g^-1).
    rewrite <- (eisadj g).
    pointed_reduce.
    destruct (eissect f ispointed_type1).
    hott_simpl. }
  intro.
  pointed_reduce.
  pointed_reduce.
  serapply path_pmap.
  serapply Build_pHomotopy.
  { intro; cbv.
    refine (eissect _ _ @ _).
    apply ap, eisretr. }
  cbn.
  hott_simpl.
  rewrite eisadj.
  rewrite ap_pp.
  rewrite (ap_compose _ g^-1).
  hott_simpl.
  destruct (eissect f ispointed_type1).
  hott_simpl.
Defined.

Notation "f '=>*' g" := (functor_pmap f g) (at level 70).

Lemma yoneda (A B : pType) (phi : forall (X : pType), (B ->* X) <~>* (A ->* X))
  : (forall X X' (f : X ->* X'), (id =>* f) o* phi X ==* phi X' o* (id =>* f))
  -> A <~>* B.
Proof.
  intro p.
  set (to := phi B id).
  set (fr := (phi A)^-1 id).
  serapply (pequiv_adjointify to fr).
  { cbn. admit. }
  { cbn.
    unfold fr, to.
    set (p _ _ fr).
    destruct p0.
Admitted.

Definition smash_unit := psphere 0.

Local Notation "1" := smash_unit.

Lemma foo A : (1 ->* A) <~>* A.
Proof.
  serapply Build_pEquiv.
  { serapply Build_pMap.
    { intro f; exact (f (point _)). }
    reflexivity. }
  serapply isequiv_adjointify.
  { intro a.
    serapply Build_pMap.
    1: serapply (Susp_rec (point _) a Empty_rec).
    reflexivity. }
  { intro. admit. }
Admitted.

Definition smash_left_unitor (A : pType) : 1 ∧ A <~>* A.
Proof.
  serapply yoneda.
  { intro X.
    refine (smash_adjunction^-1* o*E _).
    symmetry.
    apply foo. }
  intros X X' f.
  serapply Build_pHomotopy.
  { intro.
    serapply path_pmap.
    serapply Build_pHomotopy.
    { serapply smash_ind.
      { serapply Susp_ind.
        { intro.
          pointed_reduce.
          pointed_reduce.
          
  (*
  
  serapply Build_pEquiv'.
  { serapply equiv_adjointify.
    { serapply smash_rec'.
      { serapply Susp_rec.
        1: apply idmap.
        1: intro; exact (point _).
        contradiction. }
      { serapply Susp_ind.
        1,2: reflexivity.
        contradiction. }
      1,2,3: cbv.
(*      1: reflexivity. }
    1: exact (sm (point _)).
    { intro. cbv. reflexivity.
      admit. }
    serapply smash_ind.
    { serapply Susp_ind.
      { cbv. admit. }
      { intro b.
        cbv.
        apply ap, ap.
        apply path_prod.
        2: reflexivity.
        cbn.
        apply merid. admit. }
      { contradiction. } }
    {
  cbv. *) *)
Admitted.

Local Notation λ := smash_left_unitor.
Local Notation α := pequiv_smash_assoc.

Definition smash_left_unitor_nat (A A' : pType) (f : A ->* A')
  : f o* λ A ==* λ A' o* id [∧] f.
Proof.
  serapply Build_pHomotopy.
  { serapply smash_ind.
    { serapply Susp_ind.
      { intro. cbv. pointed_reduce.
(*         unfold smash_left_unitor. *)
Admitted.

Definition smash_left_unitor_triangle (A B : pType)
  : λ (A ∧ B) o* α 1 A B ==* (λ A) [∧] id.
Proof.
Admitted.
