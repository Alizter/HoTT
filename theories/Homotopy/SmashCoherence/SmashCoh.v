Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import Smash.
Require Import HIT.Spheres.
Require Import Coherence.

Require Import Associator.
Require Import Bifunctor.
Require Import Symmetry.
Require Import Pentagon.
Require Import Hexagon.
Require Import Unitor.

Local Open Scope pointed_scope.
Local Open Scope path_scope.

Notation id := pmap_idmap.
Notation S := psphere.

(* Smash product is a symmetric monoidal product *)

Global Instance symmetricmonoidalproduct_smash
  : SymmetricMonoidalProduct Smash.
Proof.
  serapply Build_SymmetricMonoidalProduct.
  (* Associator *)
  { apply pequiv_smash_assoc. }
  (* Associator naturality square *)
  { apply smash_assoc_nat. }
  (* Pentagon *)
  { apply smash_pentagon. }
  (* Braiding *)
  { apply pequiv_smash_symm. }
  (* Braiding naturality square *)
  { apply smash_symm_nat. }
  (* Hexagon *)
  { apply smash_hexagon. }
  (* Unit *)
  { apply smash_unit. }
  (* Left unitor *)
  { apply smash_left_unitor. }
  (* Left unitor naturality square *)
  { apply smash_left_unitor_nat. }
  (* Left unitor triangle *)
  { apply smash_left_unitor_triangle. }
Defined.
