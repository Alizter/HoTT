Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import Fibrations.
Require Import NullHomotopy.
Require Import HIT.Truncations.
Require Import HIT.Suspension.
Require Import HIT.Connectedness.
Import TrM.

Local Notation N := North.
Local Notation S := South.
Local Notation pt := (point _).

Section Freudenthal.

Context `{Univalence} {n : trunc_index} {X : pType} `{IsConnected n.+1 X}.

Local Notation mer := (@merid X).
Local Notation mer' := (fun x : X => merid x @ (merid pt)^).

Definition code_N (p : N = N) := Trunc (n +2+ n) (hfiber mer' p).
Definition code_S (q : N = S) := Trunc (n +2+ n) (hfiber mer q).

Definition code_cross (x : X) (q : N = S)
  : code_N (q @ (mer x)^) -> code_S q.
Proof.
  apply Trunc_rec.
  intros [x' p]; revert x x' p.
  serapply (wedge_incl_elim_uncurried (n:=n) (m:=n) pt pt).
  srefine (_;_;_).
  { intros x p.
    apply cancelR in p.
    exact (tr (x; p)). }
  { intros x p.
    apply (concat (concat_pV _)^) in p.
    apply (concat (concat_pV (mer x))) in p.
    apply cancelR in p.
    exact (tr (x; p)). }
  apply path_forall.
  intro r.
  apply ap, ap, ap.
  refine (_ @ concat_pp_p _ _ _).
  symmetry.
  refine (whiskerR _ _ @ _).
  1: apply concat_pV.
  apply concat_1p.
Defined.

Definition code_cross_pt (q : N = S) : code_N (q @ (mer pt)^) -> code_S q.
Proof.
  unfold code_N, code_S.
  apply Trunc_functor, (functor_sigma idmap).
  intro x.
  apply cancelR.
Defined.

Global Instance foo : IsConnMap n.+1 (unit_name (ispointed_type X)).
Proof.
Admitted.

Instance isequiv_code_cross (x : X) (q : N = S)
  : IsEquiv (code_cross x q).
Proof.
  revert x.
  serapply (@conn_map_elim n.+1 _ _ (unit_name (ispointed_type X)) _
    (fun x => IsEquiv (code_cross x q))).
  1: intro; apply (@trunc_leq -1); [exact tt | apply hprop_isequiv].
  intros [].
  serapply isequiv_homotopic.
  1: apply code_cross_pt.
  { unfold code_cross_pt.
    apply isequiv_Trunc_functor.
    apply @isequiv_functor_sigma.
    + exact _.
    + intro; apply isequiv_cancelR. }
  serapply Trunc_ind.
  intros [x r].
  symmetry.
  exact (ap10 (wedge_incl_comp1 pt pt _ _ _ _ x) r).
Defined.

Definition code
  : forall (y : Susp X), (N = y) -> Type.
Proof.
  serapply (Susp_ind _ code_N code_S).
  intro x; apply path_forall; intro q.
  refine (transport_arrow_toconst _ _ _ @ _).
  refine (ap _ (transport_paths_r _ _) @ _).
  apply path_universe_uncurried.
  serapply (BuildEquiv _ _ (code_cross _ _)).
Defined.

Local Open Scope path_scope.

Definition code_center' (y : Susp X) (p : N = y) : code y p.
Proof.
  refine (transport _ _ _).
  1: refine (transport_paths_r _ _ @ concat_1p _).
  apply transportD, tr.
  exists pt.
  apply concat_pV.
Defined.

Definition code_uncurried : {y : Susp X & N = y} -> Type
  := sig_rec _ _ _ code.

Definition code_center (y : Susp X) (p : N = y) : code y p.
Proof.
  change (code_uncurried (y; p)).
  srefine (transport code_uncurried _ _).
  1: exact (N; 1).
  { serapply (path_sigma' _ p).
    1: refine (transport_paths_r _ _ @ concat_1p _). }
  exact (tr (pt; concat_pV _)).
Defined.

Definition code_contr' (p : N = N) (d : code N p) : code_center N p = d.
Proof.
  revert d.
  serapply Trunc_ind.
  intros [x r].
  destruct r.
  unfold code_center.
  rewrite path_sigma_p1_1p'.
  rewrite transport_pp.
  cbn.
Admitted.

Definition code_contr (y : Susp X) (p : N = y) (rr : code y p)
  : code_center y p = rr.
Proof.
  destruct p.
  apply code_contr'.
Defined.

Global Instance conn_map_merid : IsConnMap (n +2+ n) (@merid X)
  := fun p => BuildContr _ (code_center S p) (code_contr _ _).

Global Instance freudenthal : IsConnMap (n +2+ n) mer'.
Proof.
  refine (conn_map_compose _ _ (equiv_concat_r (merid pt)^ _)).
Defined.

End Freudenthal.
