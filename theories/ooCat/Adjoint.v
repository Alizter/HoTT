(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.
Require Export ooCat.Comma ooCat.Sigma.

Generalizable Variables m n X A B.

(** * Adjoint oo-functors *)

(** TODO: generalize dimensions. For now we have made them all the same otherwise typeclasses has trouble guessing. This is probably due to some of our instances not being general enough. *)

(** ** Having a left or right adjoint *)

(** Having a left adjoint *)
Definition HasLeftAdjoint {A B : Type} (F : A -> B)
  `{IsFunctor0 n A n B F, !IsCat0 n A, !IsCat0 n B, !HasEquivs n B}
  := forall (x : B), HasInitial (Comma (@const A B x) F).
Existing Class HasLeftAdjoint.

(** Having a right adjint *)
Definition HasRightAdjoint {A B : Type} (F : A -> B)
  `{IsFunctor0 n A n B F, !IsCat0 n A, !IsCat0 n B, !HasEquivs n B}
  := forall (x : B), HasInitial (Comma F (@const A B x)).
Existing Class HasRightAdjoint.

(** ** Properties of adjoints *)

(** We can recover the functor given by a left adjoint. The coherence of this functor should go up as the coherence of the original functor with a left adjoint does. *)

Section LeftAdjointFunctor.

  Context {A B : Type} (F : A -> B) `{H : HasLeftAdjoint A B F}.

  Definition LeftAdjoint : B -> A
    := fun b => snd (@initial_obj _ _ _ (H b)).1.

  CoFixpoint isfunctor0_leftadjoint : IsFunctor0 LeftAdjoint.
  Proof.
    snrapply Build_IsFunctor0.
    { intros X Y f.
      unfold HasLeftAdjoint in H.
      exact (snd (cat_center' _ _ ((@isinitial_initial _ _ _ (H X))
        ((fst (initial_obj (Comma (const X) F) _).1,_);
        (initial_obj _ (H Y)).2 $o f)) _).1). }
    intros X Y.
    snrapply Build_IsFunctor0.
    { intros f g p.
      simpl.
  Abort.

End LeftAdjointFunctor.

