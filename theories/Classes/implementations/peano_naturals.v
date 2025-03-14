Require Import
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Classes.interfaces.naturals
  HoTT.Classes.interfaces.orders
  HoTT.Classes.theory.rings
  HoTT.Classes.orders.semirings
  HoTT.Classes.theory.apartness.

Local Set Universe Minimization ToSet.

(* This should go away one Coq has universe cumulativity through inductives. *)
Section nat_lift.

Universe N.
(* It's important that the universe [N] be free.  Occasionally, Coq will choose universe variables in proofs that force [N] to be [Set].  To pinpoint where this happens, you can add the line [Constraint Set < N.] here, and see what fails below. *)

Let natpaths := @paths@{N} nat.
Arguments natpaths (_ _)%_nat_scope.
Infix "=N=" := natpaths.

Definition natpaths_symm : Symmetric@{N N} natpaths.
Proof.
  unfold natpaths; exact _.
Defined.

#[export] Instance nat_0: Zero@{N} nat := 0%nat.
#[export] Instance nat_1: One@{N} nat := 1%nat.

#[export] Instance nat_plus: Plus@{N} nat := Nat.Core.nat_add.

Notation mul := Nat.Core.nat_mul.

#[export] Instance nat_mult: Mult@{N} nat := Nat.Core.nat_mul.

Ltac simpl_nat :=
  change (@plus nat _) with Nat.Core.nat_add;
  change (@mult nat _) with Nat.Core.nat_mul;
  simpl;
  change Nat.Core.nat_add with (@plus nat Nat.Core.nat_add);
  change Nat.Core.nat_mul with (@mult nat Nat.Core.nat_mul).

(** [0 + a =N= a] *)
Local Instance add_0_l : LeftIdentity@{N N} (plus : Plus nat) 0 := fun _ => idpath.

Definition add_S_l a b : S a + b =N= S (a + b) := idpath.

(** [a + 0 =N= a] *)
Local Instance add_0_r : RightIdentity@{N N} (plus : Plus nat) (zero : Zero nat).
Proof.
  intros a; induction a as [| a IHa].
  - reflexivity.
  - apply (ap S), IHa.
Qed.

Lemma add_S_r : forall a b, a + S b =N= S (a + b).
Proof.
  intros a b; induction a as [| a IHa].
  - reflexivity.
  - apply (ap S), IHa.
Qed.

(** [forall a b c : nat, a + (b + c) = (a + b) + c].  The RHS is written [a + b + c]. *)
Local Instance add_assoc : Associative@{N} (plus : Plus nat).
Proof.
  intros a b c; induction a as [| a IHa].
  - reflexivity.
  - change (S (a + (b + c)) = S (a + b + c)).
    apply (ap S), IHa.
Qed.

Local Instance add_comm : Commutative@{N N} (plus : Plus nat).
Proof.
  intros a b; induction a as [| a IHa].
  - rhs apply add_0_r.
    reflexivity.
  - rhs apply add_S_r.
    apply (ap S), IHa.
Qed.

Local Instance mul_0_l : LeftAbsorb@{N N} (mult : Mult nat) (zero : Zero nat)
  := fun _ => idpath.

Definition mul_S_l a b : (S a) * b =N= b + a * b := idpath.

(** [1 * a =N= a]. *)
Local Instance mul_1_l : LeftIdentity@{N N} (mult : Mult nat) (one : One nat)
  := add_0_r.

Local Instance mul_0_r : RightAbsorb@{N N} (mult : Mult nat) (zero : Zero nat).
Proof.
  intros a; induction a as [| a IHa].
  - reflexivity.
  - change (a * 0 = 0).
    exact IHa.
Qed.

Lemma mul_S_r a b : a * S b =N= a + a * b.
Proof.
  induction a as [| a IHa].
  - reflexivity.
  - change (S (b + a * S b) = S (a + (b + a * b))).
    apply (ap S).
    rhs rapply add_assoc.
    rhs rapply (ap (fun x => x + _) (add_comm _ _)).
    rhs rapply (add_assoc _ _ _)^.
    exact (ap (plus b) IHa).
Qed.

(** [a * 1 =N= a]. *)
Local Instance mul_1_r : RightIdentity@{N N} (mult : Mult nat) (one : One nat).
Proof.
  intros a.
  lhs napply mul_S_r.
  lhs napply (ap _ (mul_0_r a)).
  apply add_0_r.
Qed.

Local Instance mul_comm : Commutative@{N N} (mult : Mult nat).
Proof.
  intros a b; induction a as [| a IHa].
  - rhs apply mul_0_r.
    reflexivity.
  - rhs apply mul_S_r.
    change (b + a * b = b + b * a).
    apply (ap (fun x => b + x)), IHa.
Qed.

(** [a * (b + c) =N= a * b + a * c]. *)
Local Instance add_mul_distr_l
  : LeftDistribute@{N} (mult : Mult nat) (plus : Plus nat).
Proof.
  intros a b c; induction a as [| a IHa].
  - reflexivity.
  - change ((b + c) + a * (b + c) = (b + a * b) + (c + a * c)).
    lhs rapply (add_assoc _ _ _)^.
    rhs rapply (add_assoc _ _ _)^.
    apply (ap (plus b)).
    rhs rapply add_assoc.
    rhs rapply (ap (fun x => x + _) (add_comm _ _)).
    rhs rapply (add_assoc _ _ _)^.
    apply (ap (plus c)), IHa.
Qed.

(** [(a + b) * c =N= a * c + b * c].  This also follows from [plus_mult_distr_r], which currently requires that we already have a semiring.  It should be adjusted to not require associativity. *)
Local Instance add_mul_distr_r
  : RightDistribute@{N} (mult : Mult nat) (plus : Plus nat).
Proof.
  intros a b c.
  lhs apply mul_comm.
  lhs apply add_mul_distr_l.
  apply ap011; apply mul_comm.
Defined.

Local Instance mul_assoc : Associative@{N} (mult : Mult nat).
Proof.
 intros a b c; induction a as [| a IHa].
  - reflexivity.
  - simpl_nat.
    rhs apply add_mul_distr_r.
    apply ap, IHa.
Qed.

#[export] Instance S_neq_0 x : PropHolds (~ (S x =N= 0)).
Proof.
intros E.
change ((fun a => match a with S _ => Unit | 0%nat => Empty end) 0).
eapply transport.
- exact E.
- split.
Qed.

Definition pred x := match x with | 0%nat => 0 | S k => k end.

#[export] Instance S_inj : IsInjective@{N N} S
  := { injective := fun a b E => ap pred E }.

(** This is also in Spaces.Nat.Core. *)
#[export] Instance nat_dec: DecidablePaths@{N} nat.
Proof.
hnf.
apply (nat_rect@{N} (fun x => forall y, _)).
- intros [|b].
  + left;reflexivity.
  + right;apply symmetric_neq,S_neq_0.
- intros a IHa [|b].
  + right;apply S_neq_0.
  + destruct (IHa b).
    * left. apply ap;trivial.
    * right;intros E. apply (injective S) in E. auto.
Defined.

#[export] Instance nat_set : IsTrunc@{N} 0 nat.
Proof.
apply hset_pathcoll, pathcoll_decpaths, nat_dec.
Qed.

Instance nat_semiring : IsSemiCRing@{N} nat.
Proof.
  repeat (split; try exact _).
Qed.

(* Add Ring nat: (rings.stdlib_semiring_theory nat). *)

Lemma O_nat_0 : O =N= 0.
Proof. reflexivity. Qed.

Lemma S_nat_plus_1 x : S x =N= x + 1.
Proof.
rewrite add_comm. reflexivity.
Qed.

Lemma S_nat_1_plus x : S x =N= 1 + x.
Proof. reflexivity. Qed.

Lemma nat_induction (P : nat -> Type) :
  P 0 -> (forall n, P n -> P (1 + n)) -> forall n, P n.
Proof. apply nat_rect. Qed.

Lemma plus_eq_zero : forall a b : nat, a + b =N= 0 -> a =N= 0 /\ b =N= 0.
Proof.
intros [|a];[intros [|b];auto|].
- intros E. destruct (S_neq_0 _ E).
- intros ? E. destruct (S_neq_0 _ E).
Qed.

Lemma mult_eq_zero : forall a b : nat, a * b =N= 0 -> a =N= 0 |_| b =N= 0.
Proof.
intros [|a] [|b];auto.
- intros _;right;reflexivity.
- simpl_nat.
  intros E.
  destruct (S_neq_0 _ E).
Defined.

Instance nat_zero_divisors : NoZeroDivisors nat.
Proof.
intros x [Ex [y [Ey1 Ey2]]].
apply mult_eq_zero in Ey2.
destruct Ey2;auto.
Qed.

Instance nat_plus_cancel_l : forall z:nat, LeftCancellation@{N} plus z.
Proof.
red. intros a;induction a as [|a IHa];simpl_nat;intros b c E.
- trivial.
- apply IHa. apply (injective S). assumption.
Qed.

Instance nat_mult_cancel_l
  : forall z : nat, PropHolds (~ (z =N= 0)) -> LeftCancellation@{N} (.*.) z.
Proof.
unfold PropHolds. unfold LeftCancellation.
intros a Ea b c E;revert b c a Ea E.
induction b as [|b IHb];intros [|c];simpl_nat;intros a Ea E.
- reflexivity.
- rewrite mul_0_r in E.
  rewrite mul_S_r in E;apply symmetry in E.
  apply plus_eq_zero in E. destruct (Ea (fst E)).
- rewrite mul_0_r,mul_S_r in E. apply plus_eq_zero in E.
  destruct (Ea (fst E)).
- rewrite 2!mul_S_r in E.
  apply (left_cancellation _ _) in E.
  apply ap. apply IHb with a;trivial.
Qed.

(* Order *)
#[export] Instance nat_le: Le@{N N} nat := Nat.Core.leq.
#[export] Instance nat_lt: Lt@{N N} nat := Nat.Core.lt.

Lemma le_plus : forall n k, n <= k + n.
Proof.
induction k.
- apply Nat.Core.leq_refl.
- simpl_nat. constructor. assumption.
Qed.

Lemma le_exists : forall n m : nat,
  iff@{N N N} (n <= m) (sig@{N N} (fun k => m =N= k + n)).
Proof.
intros n m;split.
- intros E;induction E as [|m E IH].
  + exists 0;split.
  + destruct IH as [k IH].
    exists (S k). rewrite IH;reflexivity.
- intros [k Hk].
  rewrite Hk. apply le_plus.
Qed.

Lemma zero_least : forall a, 0 <= a.
Proof.
induction a;constructor;auto.
Qed.

Lemma le_S_S : forall a b : nat, iff@{N N N} (a <= b) (S a <= S b).
Proof.
intros. etransitivity;[apply le_exists|].
etransitivity;[|apply symmetry,le_exists].
split;intros [k E];exists k.
- rewrite E,add_S_r. reflexivity.
- rewrite add_S_r in E;apply (injective _) in E. trivial.
Qed.

Lemma lt_0_S : forall a : nat, 0 < S a.
Proof.
intros. apply le_S_S. apply zero_least.
Qed.

Lemma le_S_either : forall a b, a <= S b -> a <= b |_| a = S b.
Proof.
intros [|a] b.
- intros;left;apply zero_least.
- intros E. apply (snd (le_S_S _ _)) in E. destruct E as [|b E];auto.
  left. apply le_S_S. trivial.
Defined.

Lemma le_lt_dec : forall a b : nat, a <= b |_| b < a.
Proof.
induction a as [|a IHa].
- intros;left;apply zero_least.
- intros [|b].
  + right. apply lt_0_S.
  + destruct (IHa b).
    * left. apply le_S_S;trivial.
    * right. apply le_S_S. trivial.
Defined.

Lemma not_lt_0 : forall a, ~ (a < 0).
Proof.
intros a E. apply le_exists in E.
destruct E as [k E].
apply natpaths_symm,plus_eq_zero in E.
exact (S_neq_0 _ (snd E)).
Qed.

Lemma lt_le : forall a b, a < b -> a <= b.
Proof.
intros.
destruct b.
- destruct (not_lt_0 a). trivial.
- constructor. apply le_S_S. trivial.
Qed.

Local Instance nat_le_total : TotalRelation@{N N} (_:Le nat).
Proof.
hnf. intros a b.
destruct (le_lt_dec a b);[left|right].
- trivial.
- apply lt_le;trivial.
Qed.

Local Instance nat_lt_irrefl : Irreflexive@{N N} (_:Lt nat).
Proof.
hnf. intros x E.
apply le_exists in E.
destruct E as [k E].
apply (S_neq_0 k).
apply (left_cancellation@{N} (+) x).
fold natpaths.
rewrite add_0_r, add_S_r,<-add_S_l.
rewrite add_comm. apply natpaths_symm,E.
Qed.

Local Instance nat_le_hprop : is_mere_relation nat le.
Proof.
intros m n;apply Trunc.hprop_allpath.
generalize (idpath (S n) : S n =N= S n).
generalize n at 2 3 4 5.
change (forall n0 : nat,
S n =N= S n0 -> forall le_mn1 le_mn2 : m <= n0, le_mn1 = le_mn2).
induction (S n) as [|n0 IHn0].
- intros ? E;destruct (S_neq_0 _ (natpaths_symm _ _ E)).
- clear n; intros n H.
  apply (injective S) in H.
  rewrite <- H; intros le_mn1 le_mn2; clear n H.
  pose (def_n2 := idpath n0);
  path_via (paths_ind n0 (fun n _ => le m _) le_mn2 n0 def_n2).
  generalize def_n2; revert le_mn1 le_mn2.
  generalize n0 at 1 4 5 8; intros n1 le_mn1.
  destruct le_mn1; intros le_mn2; destruct le_mn2.
  + intros def_n0.
    rewrite (Trunc.path_ishprop def_n0 idpath).
    simpl. reflexivity.
  + intros def_n0; generalize le_mn2; rewrite <-def_n0; intros le_mn0.
    destruct (irreflexivity nat_lt _ le_mn0).
  + intros def_n0.
    destruct (irreflexivity nat_lt m0).
    rewrite def_n0 in le_mn1;trivial.
  + intros def_n0. pose proof (injective S _ _ def_n0) as E.
    destruct E.
    rewrite (Trunc.path_ishprop def_n0 idpath). simpl.
    apply ap. apply IHn0;trivial.
Qed.

Local Instance nat_le_po : PartialOrder nat_le.
Proof.
repeat split.
- exact _.
- exact _.
- hnf;intros; constructor.
- hnf. intros a b c E1 E2.
  apply le_exists in E1;apply le_exists in E2.
  destruct E1 as [k1 E1], E2 as [k2 E2].
  rewrite E2,E1,add_assoc. apply le_plus.
- hnf. intros a b E1 E2.
  apply le_exists in E1;apply le_exists in E2.
  destruct E1 as [k1 E1], E2 as [k2 E2].
  assert (k1 + k2 = 0) as E.
  + apply (left_cancellation (+) a).
    rhs rapply plus_0_r.
    path_via (k2 + b).
    rewrite E1.
    rewrite (plus_comm a), (plus_assoc k2), (plus_comm k2).
    reflexivity.
  + apply plus_eq_zero in E. destruct E as [Ek1 Ek2].
    rewrite Ek2,plus_0_l in E2.
    trivial.
Qed.

Local Instance nat_strict : StrictOrder (_:Lt nat).
Proof.
split.
- cbv; exact _.
- exact _.
- hnf. intros a b c E1 E2.
  apply le_exists;apply le_exists in E1;apply le_exists in E2.
  destruct E1 as [k1 E1], E2 as [k2 E2].
  exists (S (k1+k2)).
  rewrite E2,E1.
  rewrite !add_S_r,add_S_l.
  rewrite (add_assoc k2), (add_comm k2).
  reflexivity.
Qed.

#[export] Instance nat_trichotomy : Trichotomy@{N N i} (lt:Lt nat).
Proof.
hnf. fold natpaths.
intros a b. destruct (le_lt_dec a b) as [[|]|E];auto.
- right;left;split.
- left. apply le_S_S. trivial.
Qed.

#[export] Instance nat_apart : Apart@{N N} nat := fun n m => n < m |_| m < n.

Instance nat_apart_mere : is_mere_relation nat nat_apart.
Proof.
intros;apply ishprop_sum;try exact _.
intros E1 E2. apply (irreflexivity nat_lt x).
transitivity y;trivial.
Qed.

Instance decidable_nat_apart x y : Decidable (nat_apart x y).
Proof.
  rapply decidable_sum@{N N N}; apply Nat.Core.decidable_lt.
Defined.

#[export] Instance nat_trivial_apart : TrivialApart nat.
Proof.
split.
- exact _.
- intros a b;split;intros E.
  + destruct E as [E|E];apply irrefl_neq in E;trivial.
    apply symmetric_neq;trivial.
  + hnf. destruct (trichotomy _ a b) as [?|[?|?]];auto.
    destruct E;trivial.
Qed.

Lemma nat_not_lt_le : forall a b, ~ (a < b) -> b <= a.
Proof.
intros ?? E.
destruct (le_lt_dec b a);auto.
destruct E;auto.
Qed.

Lemma nat_lt_not_le : forall a b : nat, a < b -> ~ (b <= a).
Proof.
intros a b E1 E2.
apply le_exists in E1;apply le_exists in E2.
destruct E1 as [k1 E1], E2 as [k2 E2].
apply (S_neq_0 (k1 + k2)).
apply (left_cancellation (+) a).
fold natpaths. rewrite add_0_r.
rewrite E1 in E2.
rewrite add_S_r;rewrite !add_S_r in E2.
rewrite (add_assoc a), (add_comm a), <-(add_assoc k1), (add_comm a).
rewrite (add_assoc k1), (add_comm k1), <-(add_assoc k2).
apply natpaths_symm,E2.
Qed.

#[export] Instance nat_le_dec: forall x y : nat, Decidable (x ≤ y).
Proof.
intros a b. destruct (le_lt_dec a b).
- left;trivial.
- right. apply nat_lt_not_le. trivial.
Defined.

Lemma S_gt_0 : forall a, 0 < S a.
Proof.
intros;apply le_S_S,zero_least.
Qed.

Lemma nonzero_gt_0 : forall a, ~ (a =N= 0) -> 0 < a.
Proof.
intros [|a] E.
- destruct E;split.
- apply S_gt_0.
Qed.

Lemma nat_le_lt_trans : forall a b c : nat, a <= b -> b < c -> a < c.
Proof.
intros a b c E1 E2.
apply le_exists in E1;apply le_exists in E2.
destruct E1 as [k1 E1],E2 as [k2 E2];rewrite E2,E1.
rewrite add_S_r,add_assoc. apply le_S_S,le_plus.
Qed.

Lemma lt_strong_cotrans : forall a b : nat, a < b -> forall c, a < c |_| c < b.
Proof.
intros a b E1 c.
destruct (le_lt_dec c a) as [E2|E2].
- right. apply nat_le_lt_trans with a;trivial.
- left;trivial.
Defined.

Lemma nat_full' : FullPseudoSemiRingOrder nat_le nat_lt.
Proof.
split;[exact _|split|].
- split;try exact _.
  + intros a b [E1 E2].
    destruct (irreflexivity lt a).
    transitivity b;trivial.
  + hnf.
    intros a b E c;apply tr;apply lt_strong_cotrans;trivial.
  + reflexivity.
- intros a b E. apply nat_not_lt_le,le_exists in E.
  destruct E as [k E];exists k;rewrite plus_comm;auto.
- split.
  + intros a b E.
    apply le_exists in E;destruct E as [k Hk].
    rewrite Hk. rewrite add_S_r,<-add_S_l.
    rewrite plus_assoc,(plus_comm z (S k)), <-plus_assoc.
    apply le_S_S,le_plus.
  + intros a b E.
    apply le_exists in E;destruct E as [k E].
    rewrite <-add_S_r,plus_assoc,(plus_comm k z),<-plus_assoc in E.
    apply (left_cancellation plus _) in E.
    rewrite E;apply le_plus.
- intros ???? E.
  apply trivial_apart in E.
  destruct (dec (apart x₁ x₂)) as [?|ex];apply tr;auto.
  right. apply tight_apart in ex.
  apply trivial_apart. intros ey.
  apply E. apply ap011;trivial.
- unfold PropHolds.
  intros a b Ea Eb.
  apply nonzero_gt_0. intros E.
  apply mult_eq_zero in E.
  destruct E as [E|E];[rewrite E in Ea|rewrite E in Eb];
  apply (irreflexivity lt 0);trivial.
- intros a b;split.
  + intros E1 E2. apply nat_lt_not_le in E2.
    auto.
  + intros E.
    destruct (le_lt_dec a b);auto.
    destruct E;auto.
Qed.

(* Coq pre 8.8 produces phantom universes, see GitHub Coq/Coq#1033. *)
Definition nat_full@{} := ltac:(first[exact nat_full'@{Ularge Ularge}|
                                      exact nat_full'@{Ularge Ularge N}|
                                      exact nat_full'@{}]).
Local Existing Instance nat_full.

Lemma le_nat_max_l n m : n <= Nat.Core.nat_max n m.
Proof.
  revert m.
  induction n as [|n' IHn];
  intros m; induction m as [|m' IHm]; try reflexivity; cbn.
  - apply zero_least.
  - apply le_S_S. exact (IHn m').
Qed.
Lemma le_nat_max_r n m : m <= Nat.Core.nat_max n m.
Proof.
  revert m.
  induction n as [|n' IHn];
  intros m; induction m as [|m' IHm]; try reflexivity; cbn.
  - apply zero_least.
  - apply le_S_S. exact (IHn m').
Qed.
Instance S_embedding : OrderEmbedding S.
Proof.
split.
- intros ??;apply le_S_S.
- intros ??;apply le_S_S.
Qed.

#[export] Instance S_strict_embedding : StrictOrderEmbedding S.
Proof.
split;exact _.
Qed.

#[export] Instance nat_naturals_to_semiring : NaturalsToSemiRing@{N i} nat :=
  fun _ _ _ _ _ _ => fix f (n: nat) := match n with 0%nat => 0 | 1%nat => 1 |
   S n' => 1 + f n' end.

Section for_another_semiring.
  Universe U.
  Context {R:Type@{U} } `{IsSemiCRing@{U} R}.

  Notation toR := (naturals_to_semiring nat R).

(*   Add Ring R: (rings.stdlib_semiring_theory R). *)

  Local Definition f_S : forall x, toR (S x) = 1 + toR x.
  Proof.
  intros [|x].
  - symmetry;apply plus_0_r.
  - reflexivity.
  Defined.

  Local Definition f_preserves_plus a a': toR (a + a') = toR a + toR a'.
  Proof.
  induction a as [|a IHa].
  - change (toR a' = 0 + toR a').
    apply symmetry,plus_0_l.
  - change (toR (S (a + a')) = toR (S a) + toR a').
    rewrite !f_S,IHa.
    apply associativity.
  Qed.

  Local Definition f_preserves_mult a a': toR (a * a') = toR a * toR a'.
  Proof.
  induction a as [|a IHa].
  - change (0 = 0 * toR a').
    rewrite mult_0_l. reflexivity.
  - rewrite f_S.
    change (toR (a' + a * a') = (1 + toR a) * toR a').
    rewrite f_preserves_plus, IHa.
    rewrite plus_mult_distr_r,mult_1_l.
    reflexivity.
  Qed.

  #[export] Instance nat_to_sr_morphism
    : IsSemiRingPreserving (naturals_to_semiring nat R).
  Proof.
    split; split.
    - exact f_preserves_plus.
    - reflexivity.
    - exact f_preserves_mult.
    - reflexivity.
  Defined.

  Lemma toR_unique (h : nat -> R) `{!IsSemiRingPreserving h} x :
    naturals_to_semiring nat R x = h x.
  Proof.
  induction x as [|n E].
  + change (0 = h 0).
    apply symmetry,preserves_0.
  + rewrite f_S. change (1 + naturals_to_semiring nat R n = h (1+n)).
    rewrite (preserves_plus (f:=h)).
    rewrite E. apply ap10,ap,symmetry,preserves_1.
  Qed.
End for_another_semiring.

Lemma nat_naturals : Naturals@{N N N N N N N i} nat.
Proof.
split;try exact _.
intros;apply toR_unique, _.
Qed.
#[export] Existing Instance nat_naturals.

#[export] Instance nat_cut_minus: CutMinus@{N} nat := Nat.Core.nat_sub.

Lemma plus_minus : forall a b, cut_minus (a + b) b =N= a.
Proof.
unfold cut_minus,nat_cut_minus.
intros a b;revert a;induction b as [|b IH].
- intros [|a];simpl;try split.
  apply ap,add_0_r.
- intros [|a].
  + simpl. pose proof (IH 0) as E.
    rewrite add_0_l in E. exact E.
  + simpl. change nat_plus with plus.
    rewrite add_S_r,<-add_S_l;apply IH.
Qed.

Lemma le_plus_minus : forall n m : nat, n <= m -> m =N= (n + (cut_minus m  n)).
Proof.
intros n m E. apply le_exists in E.
destruct E as [k E];rewrite E.
rewrite plus_minus. apply add_comm.
Qed.

Lemma minus_ge : forall a b, a <= b -> cut_minus a b =N= 0.
Proof.
unfold cut_minus,nat_cut_minus.
intros a b;revert a;induction b as [|b IH];intros [|a];simpl.
- split.
- intros E;destruct (not_lt_0 _ E).
- split.
- intros E. apply IH;apply le_S_S,E.
Qed.

#[export] Instance nat_cut_minus_spec : CutMinusSpec@{N N} nat nat_cut_minus.
Proof.
split.
- intros x y E. rewrite add_comm.
  symmetry.
  exact (le_plus_minus _ _ E).
- exact minus_ge.
Qed.

End nat_lift.
