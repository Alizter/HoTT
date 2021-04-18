Require Import Basics Types WildCat.
Require Import Spaces.Nat Spaces.Finite.
Require Import Algebra.Rings.CRing.
Require Import Algebra.AbGroups.
Require Import Algebra.Rings.Ideal.
Require Import Algebra.Rings.QuotientRing.

Local Open Scope nat_scope.
Local Open Scope mc_scope.
Local Open Scope ring_scope.
Local Open Scope ideal_scope.

(** * Radical of an ideal *)

(** We can define the radical of an ideal directly, but showing that it is an ideal will require quite a bit of work. Notably, we will require the binomial theorem for rings. We therefore choose a slicker definition as the preimage of the quotient map of the nilradical, the ideal consisting of nilpotent elements. *)

(** Nilradical *)
Definition ideal_nilradical (R : CRing) : Ideal R.
Proof.
  snrapply Build_Ideal.
  { snrapply Build_Subgroup'.
    1: exact (fun x => hexists (fun n => rng_power x n.+1 = cring_zero)).
    1: exact _.
    { apply tr.
      exists 0%nat.
      apply rng_mult_one_r. }
    intros x y p q.
    strip_truncations.
    destruct p as [n p], q as [m q].
    apply tr.
    exists (n.+1 * m.+1)%nat.
    change (rng_power (x - y) (n.+1 * m.+1).+1 = cring_zero).
    admit. }
  intros x y; apply Trunc_functor.
  intros [n p].
  exists n.
  rewrite rng_power_mult.
  rewrite p.
  apply rng_mult_zero_r.
Admitted.

(** Preimage of ideal *)
Definition ideal_preimage {R S : CRing} (I : Ideal S) (f : R $-> S) : Ideal R
  := ideal_kernel (rng_homo_compose (rng_quotient_map I) f).

(** The radical of an ideal. *)
Definition ideal_radical {R : CRing} (I : Ideal R) : Ideal R
  := ideal_preimage (ideal_nilradical (R / I)) (rng_quotient_map I).
