Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import HIT.Pushout.

(* Here we define the Wedge sum of two pointed types *)

Local Open Scope pointed_scope.

Definition Wedge (X Y : pType) : pType
  := Build_pType
    (Pushout (fun _ : Unit => point X) (fun _ => point Y))
    (pushl (point X)).

Notation "X 'V' Y" := (Wedge X Y) (at level 10) : pointed_scope.

Definition winl {X Y : pType} : X ->* X V Y.
Proof.
  by erapply Build_pMap.
Defined.

Definition winr {X Y : pType} : Y ->* X V Y.
Proof.
  serapply Build_pMap.
  1: apply pushr.
  exact (pp tt)^.
Defined.

Arguments Wedge : simpl never.
Arguments winl : simpl never.
Arguments winr : simpl never.

Definition wpp {X Y : pType}
  : winl (point X) = winr (point Y).
Proof.
  exact (pp tt).
Defined.

Definition path_wpp_point_eq {X Y : pType}
  : point_eq (@winl X Y) @ (point_eq winr)^ = wpp.
Proof.
  refine (concat_1p _ @ inv_V _).
Defined.

Definition path_wpp_point_eq_V {X Y : pType}
  : point_eq (@winr X Y) @ (point_eq winl)^ = wpp^.
Proof.
  rewrite <- (inv_V (point_eq winr)).
  rewrite <- inv_pp.
  apply inverse2, path_wpp_point_eq.
Defined.

Definition Wedge_ind {X Y : pType} (P : X V Y -> Type)
  (f : forall x, P (winl x)) (g : forall y, P (winr y))
  (h : transport P (wpp) (f (point X)) = g (point Y))
  : forall w : X V Y, P w.
Proof.
  serapply pushout_ind.
  1,2: assumption.
  intros [].
  assumption.
Defined.

Definition Wedge_ind_beta_wpp {X Y : pType} (P : X V Y -> Type)
  (f : forall x, P (winl x)) (g : forall y, P (winr y))
  (h : transport P (pp tt) (f (point X)) = g (point Y))
  : apD (Wedge_ind P f g h) wpp = h.
Proof.
  serapply pushout_ind_beta_pp.
Defined.

Definition Wedge_rec' {X Y : pType} (P : pType)
  (f : X ->* P) (g : Y ->* P) : X V Y ->* P.
Proof.
  serapply Build_pMap.
  { serapply (pushout_rec _ f g (Unit_ind _)).
    refine (point_eq _ @ (point_eq _)^). }
  apply point_eq.
Defined.

Arguments Wedge_rec' : simpl never.

Definition Wedge_rec'_beta_wpp {X Y : pType} (P : pType)
  (f : X ->* P) (g : Y ->* P)
  : ap (Wedge_rec' P f g) wpp = point_eq f @ (point_eq g)^.
Proof.
  refine (pushout_rec_beta_pp P f g (Unit_ind _) _).
Defined.

Definition wedge_incl {X Y : pType} : X V Y -> X * Y :=
  pushout_rec _ (fun x => (x, point Y)) (fun y => (point X, y)) 
  (fun _ : Unit => idpath).

Definition wedge_symm {X Y : pType} : X V Y <~>* Y V X.
Proof.
  serapply pequiv_adjointify'.
  1,2: serapply (Wedge_rec' _ winr winl).
  1,2: serapply Wedge_ind; try reflexivity.
  1,2: rewrite transport_paths_FFlr.
  1,2: rewrite concat_p1.
  1,2: apply moveR_Vp.
  1,2: symmetry.
  1,2: rewrite concat_p1.
  1,2: rewrite Wedge_rec'_beta_wpp.
  1,2: rewrite path_wpp_point_eq_V.
  1,2: rewrite ap_V.
  1,2: rewrite Wedge_rec'_beta_wpp.
  1,2: rewrite path_wpp_point_eq_V.
  1,2: apply inv_V.
Defined.

(* 3x3 lemma? *)
Definition wedge_assoc {X Y Z : pType} : (X V Y) V Z <~>* X V (Y V Z).
Proof.
Admitted.



