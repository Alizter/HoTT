(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.
Require Export ooCat.Comma ooCat.Sigma.

Generalizable Variables m n X A B.

(** * Adjoint oo-functors *)

(** TODO: generalize dimensions. For now we have made them all the same otherwise typeclasses has trouble guessing. This is probably due to some of our instances not being general enough. *)

(** ** Having a left or right adjoint *)

(** Having a left adjoint *)
Definition HasGenLeftAdjoint (l : Stream Laxity) {A B : Type} (F : A -> B)
  `{IsFunctor0 n A n B F, !IsCat0 n A, !IsCat0 n B, !HasEquivs n B}
  := forall (x : B), HasInitial (GenComma l (@const A B x) F).
Existing Class HasGenLeftAdjoint.

(** Having a right adjoint *)
Definition HasGenRightAdjoint (l : Stream Laxity) {A B : Type} (F : A -> B)
  `{IsFunctor0 n A n B F, !IsCat0 n A, !IsCat0 n B, !HasEquivs n B}
  := forall (x : B), HasInitial (GenComma l F (@const A B x)).
Existing Class HasGenRightAdjoint.

(** ** Properties of adjoints *)

(** We can recover the functor given by a left adjoint. The coherence of this functor should go up as the coherence of the original functor with a left adjoint does. *)

Definition GenLeftAdjoint (l : Stream Laxity) {A B : Type} (F : A -> B)
  `{H : HasGenLeftAdjoint l A B F}
  : B -> A
  := fun b => gencomma_pr2 l (initial_obj _ (H b)).

CoFixpoint isfunctor0_genleftadjoint (l : Stream Laxity) {A B : Type} (F : A -> B)
  `{H : HasGenLeftAdjoint l A B F}
  : IsFunctor0 (GenLeftAdjoint l F).
Proof.
  snrapply Build_IsFunctor0.
  { intros X Y f.
    unfold HasGenLeftAdjoint in H.
    pose (a := fst (initial_obj _ (H Y)).1).
    pose (LY := snd (initial_obj _ (H Y)).1).
    pose (eta_Y := (initial_obj _ (H Y)).2).
(*     pose (i_Y := @isinitial_initial _ _ _ (H Y)). *)
(*     destruct (H Y) as [[[a LY] eta_Y] i_Y]. *)
    unfold const in eta_Y; simpl in *.
(*     pose (a' := fst (initial_obj _ (H X)).1). *)
(*     pose (LX := snd (initial_obj _ (H X)).1). *)
(*     pose (eta_X := (initial_obj _ (H X)).2). *)
    pose (i_X := @isinitial_initial _ _ _ (H X)).
(*     unfold const in eta_X; simpl in *. *)
(*     destruct (H X) as [[[a' LX] eta_X] i_X]. *)
    hnf in i_X.
    (** Depending on the laxity *)
    (** Cannot destruct (head l) and get this to work *)
  (*   cbv in eta_Y.
    unfold GenComma in i_X.
    unfold GenDComma in i_X.
    clearbody eta_Y.
    set (l' := head l) in *.
    set (ls := tail l) in *.
    change (
      match l' with
       | colax => Y $-> F (snd (initial_obj (GenComma l (const Y) F) (H Y)).1)
       | pseudo => Y $<~> F (snd (initial_obj (GenComma l (const Y) F) (H Y)).1)
       | lax => F (snd (initial_obj (GenComma l (const Y) F) (H Y)).1) $-> Y
       end) in eta_Y.
    destruct l'. *)
    

(*     destruct l'.
    { (** Colax *)
      pose (j := i_X ((a, LY); eta_Y $o f)).
      pose (k := cat_center' _ _ j _).
      LeftAdjoint k
    exact (snd (pr1 k)). }
  intros a b.
  rapply isfunctor0_leftadjoint. *)
  
Abort.


