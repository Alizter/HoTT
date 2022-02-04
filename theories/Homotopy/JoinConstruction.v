Require Import Basics Types HFiber.
Require Import PropResizing.
Require Import Small.
Require Import Colimits.Pushout.
Require Import Homotopy.HomotopyImage.
Require Import Diagrams.Sequence Colimits.Colimit.

(* TODO: Update comments *)
(** Adapted from the formalization of Dan Christensen's "Non-accessible localizations".

The formalization NonAccessible: https://github.com/jdchristensen/NonAccessible *)

Section FiberwiseJoin.

  Context {X A B : Type} {s : IsLocallySmall 1 X} (f : A -> X) (g : B -> X).

  Definition SmallPullback : Type
    := {x : A & { y : B & s (f x) (g y) } }.

  Definition FiberwiseJoin : Type
    := @Pushout SmallPullback A B pr1 (fun x => pr1 (pr2 x)).

  Definition map_join : FiberwiseJoin -> X.
  Proof.
    srapply (Pushout_rec X f g _).
    intros [x [y p]].
    exact (equiv_smalltype _ p).
  Defined.

(** TODO: reduce universe count, harder than it looks *)
End FiberwiseJoin.

Section JoinConstruction.

  Local Open Scope nat_scope.
  Universe i j k.
  Constraint i < k, j <= k.
  Context {A : Type@{i}} {X : Type@{j}}
    {s : IsLocallySmall@{i j k} 1 X} (f : A -> X).

  (** We need recursive-recursive fixpoints in Coq to write this as a mutual fixpoint. *)

  (** Automatic universe minimization is terrible here. *)
  Fixpoint map_join_power_sigma@{} (n : nat)
    : @sig@{j j} Type@{i} (fun A' => A' -> X) :=
    match n with
    | 0 => @exist@{j j} Type@{i} _ A f
    | k.+1 => let f' := @proj2@{j j} Type@{i} _ (map_join_power_sigma k) in
      @exist@{j j} Type@{i} _
        (FiberwiseJoin@{j i i i k i i i} f f')
        (map_join@{j i i i k i i} f f')
    end.

  (** We use positive powers *)
  Definition fiberwisejoin_power@{} (n : nat) : Type@{i} := (map_join_power_sigma n).1.
  Definition map_join_power@{} (n : nat) : fiberwisejoin_power n -> X
    := (map_join_power_sigma n).2.

  Definition diagram_jc@{} : Sequence@{i j k} :=
    Build_Sequence fiberwisejoin_power (fun _ => pushr).

  Set Printing Universes.
  Set Printing All.
  About Colimit.
  Fail About Colimit@{i i}.

  Definition JoinConstruction : Type@{i} := Colimit@{i i} diagram_jc.

End JoinConstruction.


(* Rijke's join construction, taken as an axiom. Egbert assumes [Funext] globally, so we assume it here. *)
(* A more detailed formulation of this is in the HoTT library, but this is all we need (and is equivalent). *)
(* This has been formalized by Valery Isaev in the Arend Standard Library available at https://github.com/JetBrains/arend-lib.  See the file Homotopy/Image.ard. *)
Definition jc_surjection@{i j k | i < k, j <= k} `{Funext} (A : Type@{i}) (X : Type@{j})
           (ls : IsLocallySmall@{i j k} 1 X)
           (f : A -> X) (s : IsSurjection@{k} f)
  : IsSmall@{i j} X.
Admitted.

(* If [f : A -> X] is n-connected, [A] is in [Type@{i}] and [X] is (n+2)-locally small, then [X] is small.  This is Proposition 2.2 from the paper. This could of course be generalized to only requiring that [A] be small. *)
Definition issmall_n_image@{i j k u | i < k, j <= k, k < u} `{Univalence}
           (n : trunc_index) {A : Type@{i}} {X : Type@{j}}
           (f : A -> X) (C : IsConnMap@{k} n f) (ls : IsLocallySmall@{i j k} (trunc_index_to_nat n) X)
  : IsSmall@{i j} X.
Proof.
  revert n A X f C ls.
  rapply trunc_index_rect@{u}.
  - intros A X f C ls.  exact ls.
  - intros n IHn A X f C ls.
    assert (IsConnMap (Tr (-1)) f) as C' by rapply minus_one_connmap_isconnmap.
    snrefine (jc_surjection A X _ f C').
    (* [f] is surjective and [IsSmall] is an [HProp], so we can assume that [x] and [y] are in the image of [f]. *)
    (* We speed up typeclass inference by providing this: *)
    pose proof (fun x y : X => ishprop_issmall (x = y)) as HP.
    intro x.
    apply (@conn_map_elim@{k i j k} (Tr (-1)) _ _ f C' _ (HP x)).
    intro b.
    revert x.
    apply (@conn_map_elim@{k i j k} (Tr (-1)) _ _ f C' _ (fun x => HP x (f b))).
    intro a.
    snrapply (IHn (a = b) _ (ap@{i j} f)).
    + srapply isconnmap_ap@{k u}.
    + apply ls.
Defined.

(* If [f : X -> Y] is (n+1)-truncated and [Y] is (n+2)-locally small, then [X] is (n+2)-locally small.  This is Lemma 2.4 from the paper. When [n] is -2, it says that a subtype of a small type is small. *)
Definition islocally_small_truncmap@{i j k u | i < k, j <= k, k <= u, j < u} `{PropResizing}
           (n : trunc_index) {X : Type@{j}} {Y : Type@{j}}
           (f : X -> Y) (T : IsTruncMap n.+1 f) (ls : IsLocallySmall@{i j k} (trunc_index_to_nat n) Y)
  : IsLocallySmall@{i j k} (trunc_index_to_nat n) X.
Proof.
  apply (islocally_small_codomain_fibers_locally_small@{i j k u} _ f).
  - exact ls.
  - intro y.
    apply islocally_small_trunc.
    apply T.
Defined.

(* This is Lemma 2.5 from the paper. *)
Definition issmall_truncmap_connected@{i j k u | i < k, j <= k, k < u} `{PropResizing} `{Univalence}
           (n : trunc_index)
           {X Y : Type@{j}}
           (f : X -> Y) (T : IsTruncMap n.+1 f)
           (ls : IsLocallySmall@{i j k} (trunc_index_to_nat n) Y)
           (C : IsConnected n.+1 X)
  : IsSmall@{i j} X.
Proof.
  pose proof (x := merely_isconnected n X).
  strip_truncations.
  apply (issmall_n_image@{i j k u} n (unit_name x)).
  - apply lift_isconnmap_trunc@{j k}.
    rapply conn_point_incl@{j j j j j j j j j j j j u}. 
  - by rapply islocally_small_truncmap@{i j k u}.
Defined.

(* This is Theorem 2.6 from the paper. *)
Definition issmall_iff_locally_small_truncated@{i j k u | i < k, j <= k, k < u} `{PropResizing} `{Univalence}
           (n : trunc_index) (X : Type@{j})
  : IsSmall@{i j} X <-> (IsLocallySmall@{i j k} (trunc_index_to_nat n) X * IsSmall@{i j} (Trunc n.+1 X)).
Proof.
  split.
  - intro sX.
    split.
    + by apply islocally_small_small@{i j k u}.
    + apply (issmall_equiv_issmall (Trunc_functor_equiv@{i j k} _ (equiv_smalltype sX))).
      apply issmall_in.
  - intros [lsX sTrX].
    apply (issmall_codomain_fibers_small (@tr n.+1 X)).
    + exact sTrX.
    + intro y.
      apply (issmall_truncmap_connected@{i j k u} n pr1).
      * rapply istruncmap_pr1.
      * exact lsX.
      * exact _.
Defined.

(* This is Corollary 2.7 from the paper. *)
Definition issmall_truncmap_small_truncation@{i j k u | i < k, j <= k, k < u} `{PropResizing} `{Univalence}
           (n : trunc_index)
           {X Y : Type@{j}}
           (f : X -> Y) (T : IsTruncMap n.+1 f)
           (ls : IsLocallySmall@{i j k} (trunc_index_to_nat n) Y)
           (sTrX : IsSmall@{i j} (Trunc n.+1 X))
  : IsSmall@{i j} X.
Proof.
  apply (snd (issmall_iff_locally_small_truncated@{i j k u} n X)).
  refine (_, sTrX).
  rapply islocally_small_truncmap@{i j k u}; assumption.
Defined.
