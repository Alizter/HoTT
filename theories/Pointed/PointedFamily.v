Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import UnivalenceAxiom.

Local Open Scope path_scope.
Local Open Scope pointed_scope.

(* pointed type family *)
Definition pFam (A : pType) := {P : A -> Type & P (point A)}.

Definition IsTrunc_pFam n {A} (X : pFam A) := forall x, IsTrunc n (X.1 x).

(* Dependent loops *)
Definition dep_loops A : pFam A -> pFam (loops A)
  := fun Pp => (fun q => transport Pp.1 q Pp.2 = Pp.2; 1).

(* Loops for pointed type families *)
Definition pfam_loops : {A : pType & pFam A} -> {A : pType & pFam A}
  := functor_sigma loops dep_loops.

(* Pointed sigma *)
Definition psigma : {A : pType & pFam A} -> pType.
Proof.
  intros [[A a] [P p]].
  exists {x : A & P x}.
  exact (a; p).
Defined.

(* psigma and loops 'commute' *)
Lemma loops_psigma_commute
  : loops o psigma == psigma o pfam_loops.
Proof.
  intros x.
  apply path_ptype.
  serapply Build_pEquiv.
  { serapply Build_pMap.
    1: exact (equiv_path_sigma _ _ _)^-1.
    reflexivity. }
  exact _.
Defined.

(* Universes blow up here?! *)

(* Pointed pi types, note that the domain is not pointed *)
Definition pforall : {A : Type & A -> pType} -> pType.
Proof.
  intros [A F].
  exact (Build_pType (forall (a : A), pointed_type (F a)) (ispointed_type o F)).
Defined.

(* pforall and loops 'commute' *)
Lemma loops_pforall_commute (A : Type) (F : A -> pType)
  : loops (pforall (A; F)) = pforall (A; loops o F).
Proof.
  apply path_ptype.
  serapply Build_pEquiv.
  + serapply Build_pMap.
    - intros x a.
      exact ((apD10 x) a).
    - reflexivity.
  + exact _.
Defined.

(* pforall and iterated loops commute *)
Lemma iterated_loops_pforall_commute (A : Type) (F : A -> pType) (n : nat)
  : iterated_loops n (pforall (A; F)) = pforall (A; iterated_loops n o F).
Proof.
  induction n; cbn.
  1: reflexivity.
  rewrite IHn.
  apply loops_pforall_commute.
Qed.

(* Nat to trunc index offset by 2 *)
Definition nat_to_trunc_index_2 (n : nat) : trunc_index.
Proof.
  induction n.
  + exact -2.
  + exact IHn.+1.
Defined.

(* Loops neutralise sigmas when truncated *)
Lemma loops_psigma_trunc (n : nat) : forall (Aa : pType) (Pp : pFam Aa)
  (istrunc_Pp : IsTrunc_pFam (nat_to_trunc_index_2 n) Pp),
  iterated_loops n (psigma (Aa; Pp))
  = iterated_loops n Aa.
Proof.
  induction n.
  { intros Aa Pp istrunc_Pp.
    serapply path_ptype.
    serapply Build_pEquiv.
    { serapply Build_pMap.
      1: apply equiv_sigma_contr.
      1: apply istrunc_Pp.
      reflexivity. }
    exact _. }
  intros Aa Pp istrunc_Pp.
  rewrite unfold_iterated_loops.
  rewrite loops_psigma_commute.
  rewrite IHn.
  { rewrite <- unfold_iterated_loops.
    reflexivity. }
  intro.
  set (istrunc_Pp (point Aa)).
  serapply istrunc_paths.
Qed.

Local Notation "( X , x )" := (Build_pType X x).

Lemma path_ptype_path_equiv `{Univalence} (A : Type)
  : (A = A, 1) = (A <~> A, 1%equiv).
Proof.
  apply path_ptype.
  srapply Build_pEquiv.
  { srapply Build_pMap.
    1: apply equiv_path.
    reflexivity. }
  exact (isequiv_equiv_path A A).
Defined.

Lemma path_ptype_issig_equiv `{Univalence} (A : Type)
  : (A <~> A, 1%equiv) = Build_pType
    {f : A -> A & IsEquiv f} (idmap; isequiv_idmap A).
Proof.
  apply path_ptype.
  apply pequiv_inverse.
  srapply Build_pEquiv.
  { srapply Build_pMap.
    1: apply issig_equiv.
    reflexivity. }
  exact _.
Defined.

Lemma local_global_looping (A : Type) (n : nat)
  : iterated_loops n.+2 (Type, A)
  = pforall (A; fun a => iterated_loops n.+1 (A, a)).
Proof.
  rewrite unfold_iterated_loops.
  change (loops (Type, A)) with (A = A, 1).
  rewrite (path_ptype_path_equiv A).
  rewrite (path_ptype_issig_equiv A).
  change ({f : A -> A & IsEquiv f}, (idmap; isequiv_idmap A)) with
    (psigma ((A -> A, idmap); (IsEquiv; isequiv_idmap A))).
  refine (loops_psigma_trunc n.+1 (A -> A, idmap)
    (IsEquiv; isequiv_idmap A) _ @ _).
  { intros x.
    induction n.
    1: apply hprop_isequiv.
    change (nat_to_trunc_index_2 n.+2) with ((nat_to_trunc_index_2 n.+1).+1).
    apply trunc_succ. }
  change (A -> A, idmap) with (pforall (A; fun a => (A, a))).
  rewrite (iterated_loops_pforall_commute _ _ n.+1).
  reflexivity.
Defined.

Require Import HSet.

(* 7.2.7 *)
Theorem equiv_istrunc_istrunc_loops n X
  : IsTrunc n.+2 X <~> forall x, IsTrunc n.+1 (loops (X, x)).
Proof.
  serapply equiv_iff_hprop.
  intro tr_loops.
  intros x y p.
  destruct p.
  apply tr_loops.
Defined.

Lemma equiv_pequiv A B : A <~>* B -> A <~> B.
Proof.
  intros [f p].
  exact (BuildEquiv _ _ f p).
Defined.

Lemma iterated_loops_functor_compose n A B C (f : B ->* C) (g : A ->* B)
  : iterated_loops_functor n (f o* g)
  ==* (iterated_loops_functor n f) o* (iterated_loops_functor n g).
Proof.
  induction n; cbn.
  1: reflexivity.
  rewrite (path_pmap IHn).
  apply loops_functor_compose.
Defined.

(* An alternate way to build pointed equivalences *)
Definition Build_pEquiv' A B (e : A <~> B) a b (p : e a = b)
  : (A, a) <~>* (B, b).
Proof.
  serapply Build_pEquiv.
  1: serapply Build_pMap.
  1: apply e.
  1: apply p.
  exact _.
Defined.

(* TODO: Move *)
Arguments pmap_idmap {_}.

Notation "e ^-1" := (pequiv_inverse e) : pointed_scope.

Lemma peissect A B (e : A <~>* B) : (pequiv_inverse e) o* e ==* pmap_idmap.
Proof.
  serapply Build_pHomotopy.
  + intro; apply eissect.
  + cbn.
    unfold moveR_equiv_V.
    rewrite concat_p_pp.
    rewrite ap_V.
    rewrite concat_pV.
    refine (concat_p1 _ @ 1 @ (concat_1p _)^).
Defined.

Lemma peisretr A B (e : A <~>* B) : e o* (pequiv_inverse e) ==* pmap_idmap.
Proof.
  serapply Build_pHomotopy.
  + intro; apply eisretr.
  + cbn.
    unfold moveR_equiv_V.
    rewrite ap_pp.
    destruct e as [[e p] [e' r s a]].
    unfold Sect in r, s; cbn in *.
    rewrite <- ap_compose.
    rewrite ap_V.
    pointed_reduce.
    apply a.
Defined.

Lemma pequiv_loops_functor A B : A <~>* B -> loops A <~>* loops B.
Proof.
  intro f.
  serapply Build_pEquiv.
  1: apply loops_functor, f.
  serapply isequiv_adjointify.
  + apply loops_functor, pequiv_inverse, f.
  + intro.
    change (((loops_functor f) o* (loops_functor (pequiv_inverse f))) x = x).
    rewrite <- (path_pmap (loops_functor_compose _ _)).
    rewrite (path_pmap (peisretr _ _ _)).
    rewrite (path_pmap (loops_functor_idmap _)).
    reflexivity.
  + unfold Sect.
    intro.
    change (((loops_functor (pequiv_inverse f) o* (loops_functor f))) x = x).
    rewrite <- (path_pmap (loops_functor_compose _ _)).
    rewrite (path_pmap (peissect _ _ _)).
    rewrite (path_pmap (loops_functor_idmap _)).
    reflexivity.
Defined.

Lemma pequiv_iterated_loops_functor A B n : A <~>* B
  -> iterated_loops n A <~>* iterated_loops n B.
Proof.
  intros f.
  induction n.
  1: apply f.
  cbn.
  apply pequiv_loops_functor.
  assumption.
Defined.

Global Instance reflexive_pequiv : Reflexive pEquiv.
Proof.
  intro x.
  serapply Build_pEquiv.
  1: apply pmap_idmap.
  exact _.
Defined.

Global Instance symmetry_pequiv : Symmetric pEquiv.
Proof.
  intros a b; apply pequiv_inverse.
Defined.

Global Instance transitive_pequiv : Transitive pEquiv.
Proof.
  intros a b c.
  apply pequiv_compose.
Defined.

(* This is slightly different to 7.2.9 in that we ommit n = -1, which is
   inhabited hsets are contractible *)
Theorem istrunc_iterated_loops (n : nat) : forall A,
  IsTrunc n A <~> forall a : A, Contr (iterated_loops n.+1 (A, a)).
Proof.
  induction n.
  { intro A.
    refine (equiv_composeR' equiv_hset_axiomK _).
    serapply equiv_iff_hprop.
    { intros K a.
      serapply (BuildContr _ 1).
      exact (fun x => (K a x)^). }
    intros ? ? ?; apply path_contr. }
  intro A.
  transitivity (forall x, IsTrunc n (loops (A, x))).
  1: destruct n; apply equiv_istrunc_istrunc_loops.
  serapply equiv_functor_forall_id.
  intro a.
  cbv beta.
  apply (equiv_composeR' (IHn (loops (A, a)))).
  serapply equiv_iff_hprop.
  { intro X.
    rewrite unfold_iterated_loops.
    apply (X 1). }
  intros X p.
  refine (@contr_equiv' _ _ _ X).
  repeat rewrite unfold_iterated_loops.
  apply equiv_pequiv.
  apply pequiv_iterated_loops_functor.
  symmetry.
  transitivity (p @ p^ = p @ p^, 1).
  { serapply Build_pEquiv'.
    1: serapply (equiv_ap (fun r => r @ p^)).
    reflexivity. }
  serapply Build_pEquiv'.
  { apply equiv_concat_lr.
    1: symmetry; apply concat_pV.
    apply concat_pV. }
  cbn.
  rewrite concat_p1.
  apply concat_Vp.
Qed.



