Require Import Basics Types Pointed.Core.
Require Import Truncations.Core.
Require Import Homotopy.EMSpace.
Require Import Homotopy.HSpace.Core Homotopy.HSpace.Pointwise Homotopy.HSpace.HGroup Homotopy.HSpace.Coherent.
Require Import Algebra.AbGroups.AbelianGroup.

Local Open Scope pointed_scope.

(** * Cohomology groups *)

(** Reduced cohomology groups are defined as the homotopy classes of pointed maps from the space to an Eilenberg-MacLane space. The group structure comes from the H-space structure on [K(G, n)]. *)
Definition Cohomology `{Univalence} (n : nat) (X : pType) (G : AbGroup) : AbGroup.
Proof.
  snrapply Build_AbGroup'.
  1: exact (Tr 0 (X ->** K(G, n))).
  1-3: shelve.
  nrapply isabgroup_ishabgroup_tr.
  nrapply ishabgroup_hspace_pmap. 
  apply iscohhabgroup_em.
Defined.
