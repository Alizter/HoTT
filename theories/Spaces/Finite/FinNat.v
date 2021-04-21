Require Import
  HoTT.Basics
  HoTT.Types
  HoTT.HSet
  HoTT.Spaces.Nat
  HoTT.Spaces.Finite.Fin
  HoTT.DProp.

Local Open Scope nat_scope.

Definition FinNat (n : nat) : Type := {x : nat | x < n}.

Definition zero_finnat (n : nat) : FinNat n.+1
  := (0; leq_1_Sn ).

Lemma path_zero_finnat (n : nat) (h : 0 < n.+1) : zero_finnat n = (0; h).
Proof.
  by apply path_sigma_hprop.
Defined.

Definition succ_finnat {n : nat} (u : FinNat n) : FinNat n.+1.
Proof.
  exists u.1.+1.
  pose u.2 as l; cbn in l.
  by rapply leq_S_n'.
Defined.
  
(*   := (u.1.+1; leq_S_n' _ _ u.2). *)

Lemma path_succ_finnat {n : nat} (u : FinNat n) (h : u.1.+1 < n.+1)
  : succ_finnat u = (u.1.+1; h).
Proof.
  by apply path_sigma_hprop.
Defined.

Definition last_finnat (n : nat) : FinNat n.+1.
Proof.
  exists n.
  exact _.
Defined.

Lemma path_last_finnat (n : nat) (h : n < n.+1)
  : last_finnat n = (n; h).
Proof.
  by apply path_sigma_hprop.
Defined.

Definition incl_finnat {n : nat} (u : FinNat n) : FinNat n.+1.
Proof.
  destruct u as [u1 u2].
  exists u1.
  rapply transitivity.
Defined.

Lemma path_incl_finnat (n : nat) (u : FinNat n) (h : u.1 < n.+1)
  : incl_finnat u = (u.1; h).
Proof.
  by apply path_sigma_hprop.
Defined.

Definition finnat_ind (P : forall n : nat, FinNat n -> Type)
  (z : forall n : nat, P n.+1 (zero_finnat n))
  (s : forall (n : nat) (u : FinNat n), P n u -> P n.+1 (succ_finnat u))
  {n : nat} (u : FinNat n)
  : P n u.
Proof.
  induction n as [| n IHn].
  - pose u.2 as u'.
    inversion u'.
  - destruct u as [x h].
    destruct x as [| x].
    + exact (transport (P n.+1) (path_zero_finnat _ h) (z _)).
    + refine (transport (P n.+1) (path_succ_finnat (x; leq_S_n _ _ h) _) _).
      apply s. apply IHn.
Defined.

Lemma compute_finnat_ind_zero (P : forall n : nat, FinNat n -> Type)
  (z : forall n : nat, P n.+1 (zero_finnat n))
  (s : forall (n : nat) (u : FinNat n), P n u -> P n.+1 (succ_finnat u))
  (n : nat)
  : finnat_ind P z s (zero_finnat n) = z n.
Proof.
  simpl.
  unfold path_zero_finnat.
  rewrite  path_sigma_hprop_1.
  reflexivity.
Defined.

Lemma compute_finnat_ind_succ (P : forall n : nat, FinNat n -> Type)
  (z : forall n : nat, P n.+1 (zero_finnat n))
  (s : forall (n : nat) (u : FinNat n),
       P n u -> P n.+1 (succ_finnat u))
  {n : nat} (u : FinNat n)
  : finnat_ind P z s (succ_finnat u) = s n u (finnat_ind P z s u).
Proof.
Admitted.

Monomorphic Definition is_bounded_fin_to_nat {n} (k : Fin n)
  : fin_to_nat k < n.
Proof.
  induction n as [| n IHn].
  - elim k.
  - destruct k as [k | []].
    + nrapply leq_trans.
      * apply IHn.
      * by apply leq_S.
    + apply leq_n.
Defined.

Monomorphic Definition fin_to_finnat {n} (k : Fin n) : FinNat n
  := (fin_to_nat k; is_bounded_fin_to_nat k).

Monomorphic Fixpoint finnat_to_fin {n : nat} : FinNat n -> Fin n.
Proof.
  destruct n.
  { intros u.
    contradiction (not_leq_Sn_0 _ u.2). }
  intros u.
  destruct u as [u p].  
  destruct u as [|u].
  1: exact fin_zero.
  apply fsucc.
  apply finnat_to_fin.
  exists u.
  apply leq_S_n in p.
  assumption.
Defined.

Lemma path_fin_to_finnat_fsucc {n : nat} (k : Fin n)
  : fin_to_finnat (fsucc k) = succ_finnat (fin_to_finnat k).
Proof.
  apply path_sigma_hprop.
  apply path_nat_fsucc.
Defined.

Lemma path_fin_to_finnat_fin_zero (n : nat)
  : fin_to_finnat (@fin_zero n) = zero_finnat n.
Proof.
  apply path_sigma_hprop.
  apply path_nat_fin_zero.
Defined.

Lemma path_fin_to_finnat_fin_incl {n : nat} (k : Fin n)
  : fin_to_finnat (fin_incl k) = incl_finnat (fin_to_finnat k).
Proof.
  reflexivity.
Defined.

Lemma path_fin_to_finnat_fin_last (n : nat)
  : fin_to_finnat (@fin_last n) = last_finnat n.
Proof.
  reflexivity.
Defined.

Lemma path_finnat_to_fin_succ {n : nat} (u : FinNat n)
  : finnat_to_fin (succ_finnat u) = fsucc (finnat_to_fin u).
Proof.
  destruct u as [u p].
  induction p.
  1: reflexivity.
  destruct u.
  1: reflexivity.
  simpl.
  refine (ap (fun x =>
    match fsucc (finnat_to_fin (u; x)) with
    | inl i' => inl (fsucc i')
    | inr tt => inr tt
    end) _).
  apply path_ishprop.
Defined.

Lemma path_finnat_to_fin_zero (n : nat)
  : finnat_to_fin (zero_finnat n) = fin_zero.
Proof.
  reflexivity.
Defined.

Lemma path_finnat_to_fin_incl {n : nat} (u : FinNat n)
  : finnat_to_fin (incl_finnat u) = fin_incl (finnat_to_fin u).
Proof.
  induction n as [| n IHn].
  - pose u.2 as p; inversion p.
  - destruct u as [x h].
    destruct x as [| x]; [reflexivity|].
    simpl.
    srefine ((ap _ (ap _ (path_succ_finnat (x; _) _)))^ @ _).
    1: hnf; by apply leq_S_n.
    simpl.
    unfold fin_incl.
    
    refine (ap fsucc (IHn (x; _))).
Admitted.

Lemma path_finnat_to_fin_last (n : nat)
  : finnat_to_fin (last_finnat n) = fin_last.
Proof.
  induction n as [| n IHn].
  - reflexivity.
  - exact (ap fsucc IHn).
Defined.

Lemma path_finnat_to_fin_to_finnat {n : nat} (u : FinNat n)
  : fin_to_finnat (finnat_to_fin u) = u.
Proof.
  induction n as [| n IHn].
  - pose u.2 as p; inversion p.
  - destruct u as [x h].
    destruct x as [| x].
    + destruct h.
(*       apply path_fin_to_finnat_fin_zero.
    + apply path_sigma_hprop.
      refine ((path_fin_to_finnat_fsucc _)..1 @ _).
      exact (ap S (IHn (x; h))..1). *)
(* Defined. *)
Admitted.

Lemma path_fin_to_finnat_to_fin {n : nat} (k : Fin n)
  : finnat_to_fin (fin_to_finnat k) = k.
Proof.
  induction n as [| n IHn].
  - elim k.
  - destruct k as [k | []].
    + specialize (IHn k).
      refine (path_finnat_to_fin_incl (fin_to_finnat k) @ _).
      exact (ap fin_incl IHn).
    + apply path_finnat_to_fin_last.
Defined.

Definition equiv_fin_finnat (n : nat) : Fin n <~> FinNat n
  := equiv_adjointify fin_to_finnat finnat_to_fin
      path_finnat_to_fin_to_finnat
      path_fin_to_finnat_to_fin.
