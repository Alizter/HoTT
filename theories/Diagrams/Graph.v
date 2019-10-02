Require Import Basics.
Require Import Types.

(** * Graphs *)

(** A [Graph] is a type [graph0] of points together with a type [graph1] of arrows between each points. *)

Record Graph := {
  graph0 : Type;
  graph1 : graph0 -> graph0 -> Type;
}.

Coercion graph0 : Graph >-> Sortclass.
Coercion graph1 : Graph >-> Funclass.

(* The transpose of a graph has the same vertecies but the edges are reversed. *)
Definition graph_transpose : Graph -> Graph.
Proof.
  intro G.
  econstructor.
  intros i j.
  exact (G j i).
Defined.

Global Instance isequiv_graph_transpose : IsEquiv graph_transpose.
Proof.
  serapply isequiv_adjointify.
  1: exact graph_transpose.
  1,2: cbn; reflexivity.
Defined.
