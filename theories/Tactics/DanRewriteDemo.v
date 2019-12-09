(* Examples of using the tactics in DanRewrite.v.  See that file for
   more information. *)

Require Import Basics.
Require Import Spaces.Nat.
Require Import Tactics.DanRewrite.


Open Scope nat_scope.

Axiom add_double : forall n : nat, n + n = n * 2.

Definition test1 (n : nat) : 2 * (n + n) * 3 = 2 * (n * 2) * 3.
  rewritel add_double.
Defined.

Print test1.                 (* Lots of unneeded lets that disappear definitionally. *)
Eval unfold test1 in test1.  (* Gone here. *)
(* [fun n : nat => ap (fun w : nat => 2 * w * 3) (add_double n)] *)

Definition test1' (n : nat) : 2 * (n + n) * 3 = 2 * (n * 2) * 3.
  rewrite add_double.
  reflexivity.
Defined.

Print test1'.  (* This proof term is harder to work with in practice. *)
(* [fun n : nat =>
    internal_paths_rew_r nat (n + n) (n * 2)
        (fun n0 : nat => 2 * n0 * 3 = 2 * (n * 2) * 3)
        1 (add_double n)] *)

(* Test all versions. *)
Definition test1_more (n : nat) : 2 * (n + n) * 3 = 2 * (n * 2) * 3.
  rewritel add_double.  Undo.
  rewritels add_double.  Undo.
  rewriterV add_double.  Undo.
  rewriterVs add_double.
Defined.

Definition test1_flipped (n : nat) : 2 * (n * 2) * 3 = 2 * (n + n) * 3.
  rewriter add_double.  Undo.
  rewriters add_double.  Undo.
  rewritelV add_double.  Undo.
  rewritelVs add_double.
Defined.

Axiom add_comm : forall n m : nat, n + m = m + n.

Definition test2 (n m k : nat) : 2 * n * (m + k) = n.
  (* In this case, rewritel is overeager, unfolding the first multiplication: *)
  rewritel add_comm.
  (* Goal: [(n + 0 + n) * (m + k) = n] *)
  Undo.
  (* But the syntactic version rewritels doesn't do this: *)
  rewritels add_comm.
  (* Goal: [2 * n * (k + m) = n] *)
  (* However, in practice, the syntactic version is too picky, so the eager one is the default. *)
Abort.

Definition test3 (A : Type) (x y z : A) (p : x = y) (q : y = z) : 1 @ p @ 1 @ q @ 1 = p @ q.
  rewritel concat_p1.
  rewritel concat_p1.
  rewritel concat_1p.
Defined.

Print test3.                 (* Lots of unneeded lets. *)
Eval unfold test3 in test3.  (* Gone here.  Good proof. *)

Axiom Pt : Type.
Axiom c0 : Pt.
Axiom alleq : forall c : Pt, c = c0.
Definition test4 (c c' : Pt) : c = c'.
  rewritel alleq.
  rewriter alleq.
Defined.
