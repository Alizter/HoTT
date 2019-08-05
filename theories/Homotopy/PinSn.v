Require Import Basics.
Require Import Types.
Require Import Pointed.

Require Import Spaces.Int.
Require Import Spaces.Nat.

Require Import HIT.Spheres.
Require Import HIT.Truncations.
Require Import HIT.Suspension.

Require Import HomotopyGroup.
Require Import Pi1S1.

Import TrM.

(* Formalisation of Pi n Sn = Z *)

Local Open Scope pointed_scope.
Local Open Scope path_scope.
Local Open Scope trunc_scope.

Lemma ptr_iterated_loops (n : nat) : forall {X : pType},
   pTr 0 (iterated_loops n X) = iterated_loops n (pTr n X).
Proof.
  induction n.
  1: reflexivity.
  intro X.
  refine (ap _ (unfold_iterated_loops n X) @ _).
  refine (IHn (loops X) @ _).
  refine (ap _ (ptr_loops_eq n X) @ _).
  symmetry.
  apply unfold_iterated_loops.
Defined.

Definition decode {n : nat}
  : pTr n.+1 (psphere n.+1) ->* pTr n.+1 (loops (psphere n.+2)).
Proof.
  apply ptr_functor.
  apply loop_susp_unit.
Defined.

Lemma isequiv_conn_map {A B} {f : A -> B} {n} {c : IsConnMap n f}
  : IsEquiv (Trunc_functor n f).
Proof.
  serapply isequiv_adjointify.
  { refine (Trunc_rec (fun b =>
      Trunc_rec (tr o pr1)
      (center (n (hfiber f b))))). }
  { intro y.
    strip_truncations; cbv.
    destruct c as [d _].
    strip_truncations.
    cbv; apply ap, d.2. }
  intro x.
  strip_truncations; cbv.
  destruct c as [d e].
  revert e.
  strip_truncations.
  intro e. unfold hfiber in d.
  set (e (tr (x; 1%path))).
  apply (ap (Trunc_functor n pr1)) in p.
  assumption.
Defined.

Require Import BlakersMassey.
Require Import HIT.Connectedness.

Global Instance conn_map_merid_concat (X : pType) `{IsConnected n.+1 X}
  : IsConnMap (n +2+ n) (fun x => merid x @ (merid (point X))^).
Proof.
  refine (conn_map_compose _ _ (equiv_concat_r (merid (point _))^ _)).
Defined.

Fixpoint bar n m : n <= m -> n <= m.+1.
Proof.
  destruct m.
  { intro.
    destruct n.
    1: exact tt.
    1: contradiction. }
  destruct n.
  1: intro; exact tt.
  intro.
  cbn.
  apply bar.
  apply H.
Defined.

Definition foo n m : n.+1 <= m -> n <= m.
Proof.
  intro.
  destruct m.
  1: contradiction.
  apply bar.
  assumption.
Defined.

Definition isconnected_trunc_index_leq n m A `{n <= m}
  `{IsConnected m A} : IsConnected n A.
Proof.
Admitted.

(* (* This follows from Freudenthal suspension *)
Global Instance conn_map_loop_susp_unit {X : pType} {n} {c : IsConnected n X}
  : IsConnMap n.+1 (loop_susp_unit X).
Proof.
  intro.
  serapply (isconnected_trunc_index_leq n.+1 (n +2+ n)).
  { induction n.

  apply conn_map_merid_concat.
Admitted. *)

Lemma isconnected_susp {X : Type} {n} {c : IsConnected n X}
  : IsConnected n.+1 (Susp X).
Proof.
  apply isconnected_from_elim.
  intros C H' f.
  exists (f North).
  assert ({ p0 : f North = f South & forall x:X, ap f (merid x) = p0 })
    as [p0 allpath_p0] by (apply (isconnected_elim n); apply H').
  apply (Susp_ind (fun a => f a = f North) 1%path p0^).
  intros x.
  apply (concat (transport_paths_Fl _ _)).
  apply (concat (concat_p1 _)).
  apply ap, allpath_p0.
Defined.

Lemma isconnected_sphere n : IsConnected n.+1 (Sphere n.+2).
Proof.
  induction n.
  { unfold IsConnected.
    erapply contr_inhabited_hprop.
    apply to, North. }
  apply isconnected_susp.
Defined.

Lemma isconnected_psphere {n : nat} : IsConnected n (psphere n.+1).
Proof.
  induction n.
  1: erapply isconnected_sphere.
  apply isconnected_susp.
Defined.

Definition trunc_index_add_succ m n : m +2+ n.+1 = (m +2+ n).+1.
Proof.
  revert m.
  induction n; induction m.
  1,3: reflexivity.
  all: cbn; apply ap.
  all: assumption.
Defined.

Lemma mainlemma `{Univalence} {n : nat}
  : pTr n.+1 (loops (psphere n.+2)) = pTr n.+1 (psphere n.+1).
Proof.
  symmetry.
  apply path_ptype.
  refine (Build_pEquiv _ _ decode _).
  serapply isequiv_conn_map. (*
  destruct n.
  { intro x.
    unfold hfiber.
    serapply (@isconnected_sigma 1 (psphere).
  
    apply isconnected_pred.
    revert x.
    change (IsConnMap (0 +2+ 0) (loop_susp_unit (psphere 1))).
    apply conn_map_merid_concat.
     admit. } *)
  intro.
  destruct n.
  { cbn.
  
  
  serapply (isconnected_trunc_index_leq n.+1 (n +2+ n)).
  { induction n.
    { exact tt. }
    { apply foo.
      change (n.+3 <= n.+1 +2+ n.+1).
      rewrite trunc_index_add_succ.
      apply IHn.
      exact 1%path. } }
  apply conn_map_merid_concat.
  apply (@isconnected_psphere n.+1).
Admitted.

(* TODO: Rename *)
Lemma rearrange {n : nat} : Pi n.+2 (psphere n.+2) = Pi n.+1 (psphere n.+1).
Proof.
  unfold Pi.
  apply path_universe_uncurried.
  change (pTr 0 (iterated_loops n.+2 (psphere n.+2))
    <~> pTr 0 (iterated_loops n.+1 (psphere n.+1))).
  apply equiv_path.
  rewrite unfold_iterated_loops.
  rewrite !ptr_iterated_loops.
  apply ap, ap.
  apply mainlemma.
Defined.

Theorem PinSn {n : nat} : Pi n.+1 (psphere n.+1) <~> Int.
Proof.
  induction n.
  1: apply Pi1S1'.
  rewrite rearrange.
  apply IHn.
Qed.