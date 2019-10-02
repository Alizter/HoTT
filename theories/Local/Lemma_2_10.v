Require Import Basics.
Require Import Types.
Require Import Colimit.
Require Import Sequence.
Require Import Diagram.
Require Import ReflectiveSubuniverse.
Require Import Lemma_2_9.

(* Lemma 2.10 of CORS

  If the maps in a sequential diagram
          h_0      h_1      h_2
      X_0 ---> X_1 ---> X_2 ---> ...

  are L-equivalences (O_inverts), then the transfinite composite h^ : X_0 -> Colimit_n X_n is an L-equivalence.

*)

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
    refine (equiv_isequiv _).




End Lem_2_10.

End Lem_2_10.

