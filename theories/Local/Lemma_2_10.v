Require Import Basics.
Require Import Types.
Require Import Colimit.
Require Import Sequence.
Require Import Diagram.
Require Import Graph.
Require Import ReflectiveSubuniverse.
Require Import Lemma_2_9.

(* Lemma 2.10 of CORS

  If the maps in a sequential diagram
          h_0      h_1      h_2
      X_0 ---> X_1 ---> X_2 ---> ...

  are L-equivalences (O_inverts), then the transfinite composite h^ : X_0 -> Colimit_n X_n is an L-equivalence.

*)

(* We can construct a diagram from a given diagram by turning all maps into precompositions and all objects into exponential objects. *)
Definition diagram_precompose {G : Graph} (X : Diagram G) (Z : Type)
  : Diagram (graph_transpose G).
Proof.
  serapply Build_Diagram.
  { intro i.
    exact (X i -> Z). }
  intros i j g.
  exact (fun h => h o X _f g).
Defined.

Require Import Limit.
Require Import Cocone.
Require Import ConstantDiagram.

Lemma equiv_cocone_limit `{Funext} {G : Graph} (X : Diagram G) (Z : Type)
  : Cocone X Z <~> Limit (diagram_precompose X Z).
Proof.
  serapply equiv_adjointify.
  1,2: intros [? w]; econstructor; intros ???.
  1: funext x.
  2: apply ap10.
  1,2: apply w.
  1,2: intros[]; apply ap; funext ???.
  1: apply eissect.
  apply eisretr.
Defined.

Theorem equiv_colimit_limit `{Funext} {G : Graph} (X : Diagram G) (Z : Type)
  : (Colimit X -> Z) <~> Limit (diagram_precompose X Z).
Proof.
  refine (_ oE colimit_adjoint).
  refine (_ oE equiv_diagram_const_cocone _ _).
  apply equiv_cocone_limit.
Defined.

Local Open Scope nat_scope.
Local Open Scope path_scope.

Global Instance isequiv_lim_precomp `{Funext} (X : Sequence) (Z : Type)
  (X' := diagram_precompose X Z)
(*   (e : forall n, IsEquiv (X _f idpath : X n -> X n.+1)) *)
  (e : forall n, IsEquiv (X' _f idpath : X' n.+1 -> X' n))
  : forall i, IsEquiv (fun x => lim (D:=X') x i).
Proof.
  cbn.
  intro n.
  serapply isequiv_adjointify.
  { intro f.
    serapply Build_Limit.
    { cbn.
      intro k.
      induction k.
      { induction n.
        1: apply f.
        apply IHn.
        apply (X' _f 1).
        exact f. }
      apply (X' _f 1)^-1.
      exact IHk. }
    intros i k p.
    destruct p.
    apply eisretr. }
  { intro.
    induction n.
    1: reflexivity.
    unfold lim in *.
    admit. }
  intros [].

  
Admitted.

(* 
Global Instance isequiv_colim {G : Grap} (X : Diagram G)
  (e : forall i j (g : G i j), IsEquiv (X _f g))
  :  *)

Module Lem_2_10 (Ls : ReflectiveSubuniverses).

Import Ls.
Module Import Ls_Theory := ReflectiveSubuniverses_Theory Ls.

(* For now we have to import Lemma 2.9. In the future this should come bundled with Ls_Theory above. *)
Module Import Lem_2_9 := Lem_2_9 Ls.

Section Lem_2_10.

  Local Open Scope nat_scope.

  Context `{Funext} (L : ReflectiveSubuniverse).

  (* TODO: Better way to access nth map of sequence? *)
  Lemma lemma_2_10  (X : Sequence) (isLeq : forall n : nat,
    O_inverts L ((X _f idpath) : X n -> X n.+1))
    : O_inverts L (@colim _ X 0).
  Proof.
    apply (lemma_2_9 _ _)^-1.
    intros Z ZinL.
    serapply isequiv_homotopic.
    { intro f.
      apply equiv_colimit_limit in f.
      apply (lim f 0). }
    { cbv zeta; hnf.
      refine (isequiv_compose' (equiv_colimit_limit X Z)_ (fun x => lim x 0) _).
      apply isequiv_lim_precomp.
      intro n.
      revert Z ZinL.
      apply lemma_2_9.
      apply isLeq. }
    reflexivity.
  Defined.

End Lem_2_10.

End Lem_2_10.

