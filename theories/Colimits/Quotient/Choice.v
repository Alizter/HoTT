Require Import
  HoTT.Basics
  HoTT.Types
  HoTT.HSet
  HoTT.Truncations
  HoTT.Colimits.Quotient
  HoTT.Projective.

(** The following is an alternative (0,-1)-projectivity predicate on [A]. Given a family of quotient equivalence classes [f : forall x : A, B x / R x], for [R : forall x : A, Relation (B x)], we merely have a choice function [g : forall x, B x], factoring [f] as [f x = class_of (g x)]. *)

Definition HasQuotientChoice (A : Type) :=
  forall (B : A -> Type), (forall x, IsHSet (B x)) ->
  forall (R : forall x, Relation (B x))
         (pR : forall x, is_mere_relation (B x) (R x)),
         (forall x, Reflexive (R x)) ->
         (forall x, Symmetric (R x)) ->
         (forall x, Transitive (R x)) ->
  forall (f : forall x : A, B x / R x),
  hexists (fun g : (forall x : A, B x) =>
                   forall x, class_of (R x) (g x) = f x).

Section choose_has_quotient_choice.
  Context `{Univalence}
    {A : Type} {B : A -> Type} `{!forall x, IsHSet (B x)}
    (P : forall x, B x -> Type) `{!forall x (a : B x), IsHProp (P x a)}.

  Local Definition RelClassEquiv (x : A) (a : B x) (b : B x) : Type
    := P x a <~> P x b.

  Local Instance reflexive_relclass
    : forall x, Reflexive (RelClassEquiv x).
  Proof.
    intros a b. apply equiv_idmap.
  Qed.

  Local Instance symmetric_relclass
    : forall x, Symmetric (RelClassEquiv x).
  Proof.
    intros a b1 b2 p. apply (equiv_inverse p).
  Qed.

  Local Instance transitive_relclass
    : forall x, Transitive (RelClassEquiv x).
  Proof.
    intros a b1 b2 b3 p q. apply (equiv_compose q p).
  Qed.

  Local Instance hprop_choose_cod (a : A)
    : IsHProp {c : B a / RelClassEquiv a
                 | forall b, in_class (RelClassEquiv a) c b <~> P a b}.
  Proof.
    apply ishprop_sigma_disjoint.
    refine (Quotient_ind_hprop _ _ _).
    intro b1.
    refine (Quotient_ind_hprop _ _ _).
    intros b2 f g.
    apply qglue.
    apply (f b2)^-1.
    apply g.
    apply reflexive_relclass.
  Qed.

  Local Definition prechoose (i : forall x, hexists (P x)) (a : A)
    : {c : B a / RelClassEquiv a
         | forall b : B a, in_class (RelClassEquiv a) c b <~> P a b}.
  Proof.
    specialize (i a).
    strip_truncations.
    destruct i as [b1 h].
    exists (class_of _ b1).
    intro b2.
    apply equiv_iff_hprop.
    - intro f. exact (f h).
    - intro p. by apply equiv_iff_hprop.
  Defined.

  Local Definition choose (i : forall x, hexists (P x)) (a : A)
    : B a / RelClassEquiv a
    := (prechoose i a).1.

End choose_has_quotient_choice.

(** The following section derives [HasTrChoice 0 A] from [HasQuotientChoice A]. *)

Section has_tr0_choice_quotientchoice.
  Context `{Univalence} (A : Type) (qch : HasQuotientChoice A).

  Local Definition RelUnit (B : A -> Type) (a : A) (b1 b2 : B a) : HProp
    := Build_HProp Unit.

  Local Instance reflexive_relunit (B : A -> Type) (a : A)
    : Reflexive (RelUnit B a).
  Proof.
    done.
  Qed.

  Local Instance symmetric_relunit (B : A -> Type) (a : A)
    : Symmetric (RelUnit B a).
  Proof.
    done.
  Qed.

  Local Instance transitive_relunit (B : A -> Type) (a : A)
    : Transitive (RelUnit B a).
  Proof.
    done.
  Qed.

  Local Instance ishprop_quotient_relunit (B : A -> Type) (a : A)
    : IsHProp (B a / RelUnit B a).
  Proof.
    apply hprop_allpath.
    refine (Quotient_ind_hprop _ _ _).
    intro r.
    refine (Quotient_ind_hprop _ _ _).
    intro s.
    by apply qglue.
  Qed.

  Lemma has_tr0_choice_quotientchoice : HasTrChoice 0 A.
  Proof.
    intros B sB f.
    transparent assert (g : (forall a, B a / RelUnit B a)).
    - intro a.
      specialize (f a).
      strip_truncations.
      exact (class_of _ f).
    - specialize (qch B _ (RelUnit B) _ _ _ _ g).
      strip_truncations.
      apply tr.
      apply qch.
  Qed.

End has_tr0_choice_quotientchoice.

Lemma has_quotient_choice_tr0choice (A : Type)
  : HasTrChoice 0 A -> HasQuotientChoice A.
Proof.
  intros ch B sB R pR rR sR tR f.
  set (P := fun a b => class_of (R a) b = f a).
  assert (forall a, merely ((fun x => {b | P x b}) a)) as g.
  - intro a.
    refine (Quotient_ind_hprop _
              (fun c => merely {b | class_of (R a) b = c}) _ (f a)).
    intro b.
    apply tr.
    by exists b.
  - pose proof (ch (fun a => {b | P a b}) _ g) as h.
    strip_truncations.
    apply tr.
    exists (fun x => (h x).1).
    intro a.
    apply h.
Qed.

Global Instance isequiv_has_tr0_choice_to_has_quotient_choice
  `{Univalence} (A : Type)
  : IsEquiv (has_quotient_choice_tr0choice A).
Proof.
  srapply isequiv_iff_hprop.
  - apply istrunc_forall.
  - apply has_tr0_choice_quotientchoice.
Qed.

Definition equiv_has_tr0_choice_has_quotient_choice
  `{Univalence} (A : Type)
  : HasTrChoice 0 A <~> HasQuotientChoice A
  := Build_Equiv _ _ (has_quotient_choice_tr0choice A) _.

(** The next section uses [has_quotient_choice_tr0choice] to generalize [quotient_rec2], see [choose_quotient_ind] below. *)

Section choose_quotient_ind.
  Context `{Univalence}
    {I : Type} `{!HasTrChoice 0 I}
    {A : I -> Type} `{!forall i, IsHSet (A i)}
    (R : forall i, Relation (A i))
    `{!forall i, is_mere_relation (A i) (R i)}
    {rR : forall i, Reflexive (R i)}
    {sR : forall i, Symmetric (R i)}
    {tR : forall i, Transitive (R i)}.

(** First generalize the [qglue] constructor. *)

  Lemma qglue_forall
    (f g : forall i, A i) (r : forall i, R i (f i) (g i))
    : (fun i => class_of (R i) (f i)) = (fun i => class_of (R i) (g i)).
  Proof.
    funext s.
    by apply qglue.
  Defined.

(** Given suitable preconditions, we will show that [ChooseProp P a g] is inhabited, rather than directly giving an inhabitant of [P g]. This turns out to be beneficial because [ChooseProp P a g] is a proposition. *)

  Local Definition ChooseProp
    (P : (forall i, A i / R i) -> Type) `{!forall g, IsHSet (P g)}
    (a : forall (f : forall i, A i), P (fun i => class_of (R i) (f i)))
    (g : forall i, A i / R i)
    : Type
    := {b : P g
       | merely (exists (f : forall i, A i)
                        (q : g = fun i => class_of (R i) (f i)),
                 forall (f' : forall i, A i)
                        (r : forall i, R i (f i) (f' i)),
                 qglue_forall f f' r # q # b = a f')}.

  Local Instance ishprop_choose_quotient_ind_chooseprop
    (P : (forall i, A i / R i) -> Type) `{!forall g, IsHSet (P g)}
    (a : forall (f : forall i, A i), P (fun i => class_of (R i) (f i)))
    (g : forall i, A i / R i)
    : IsHProp (ChooseProp P a g).
  Proof.
    apply ishprop_sigma_disjoint.
    intros x y h1 h2.
    strip_truncations.
    destruct h1 as [f1 [q1 p1]].
    destruct h2 as [f2 [q2 p2]].
    specialize (p1 f1 (fun i => rR i (f1 i))).
    set (pR := fun i =>
                related_quotient_paths (R i) _ _ (ap (fun h => h i) q2^
                @ ap (fun h => h i) q1)).
    specialize (p2 f1 pR).
    do 2 apply moveL_transport_V in p1.
    do 2 apply moveL_transport_V in p2.
    refine (p1 @ _ @ p2^).
    apply moveR_transport_p.
    rewrite inv_V.
    rewrite <- transport_pp.
    apply moveR_transport_p.
    rewrite inv_V.
    do 2 rewrite <- transport_pp.
    set (pa := (qglue_forall f2 f1 pR)^
               @ (q2^ @ q1 @ qglue_forall f1 f1 _)).
    by induction (hset_path2 idpath pa).
  Qed.

(* Since [ChooseProp P a g] is a proposition, we can apply [has_quotient_choice_tr0choice] and strip its truncation in order to derive [ChooseProp P a g]. *)

  Lemma chooseprop_quotient_ind
    (P : (forall i, A i / R i) -> Type) `{!forall g, IsHSet (P g)}
    (a : forall (f : forall i, A i), P (fun i => class_of (R i) (f i)))
    (E : forall (f f' : forall i, A i) (r : forall i, R i (f i) (f' i)),
         qglue_forall f f' r # a f = a f')
    (g : forall i, A i / R i)
    : ChooseProp P a g.
  Proof.
    pose proof
      (has_quotient_choice_tr0choice I _ A _ R _ _ _ _ g) as h.
    strip_truncations.
    destruct h as [h p].
    apply path_forall in p.
    refine (transport _ p _).
    exists (a h).
    apply tr.
    exists h.
    exists 1.
    apply E.
  Defined.

(** By projecting out of [chooseprop_quotient_ind] we obtain a generalization of [quotient_rec2]. *)

  Lemma choose_quotient_ind
    (P : (forall i, A i / R i) -> Type) `{!forall g, IsHSet (P g)}
    (a : forall (f : forall i, A i), P (fun i => class_of (R i) (f i)))
    (E : forall (f f' : forall i, A i) (r : forall i, R i (f i) (f' i)),
         qglue_forall f f' r # a f = a f')
    (g : forall i, A i / R i)
    : P g.
  Proof.
    exact (chooseprop_quotient_ind P a E g).1.
  Defined.

(** A specialization of [choose_quotient_ind] to the case where [P g] is a proposition. *)

  Lemma choose_quotient_ind_prop
    (P : (forall i, A i / R i) -> Type) `{!forall g, IsHProp (P g)}
    (a : forall (f : forall i, A i), P (fun i => class_of (R i) (f i)))
    (g : forall i, A i / R i)
    : P g.
  Proof.
    refine (choose_quotient_ind P a _ g). intros. apply path_ishprop.
  Defined.

(** The recursion principle derived from [choose_quotient_ind]. *)

  Definition choose_quotient_rec
    {B : Type} `{!IsHSet B} (a : (forall i, A i) -> B)
    (E : forall (f f' : forall i, A i),
         (forall i, R i (f i) (f' i)) -> a f = a f')
    (g : forall i, A i / R i)
    : B
    := choose_quotient_ind (fun _ => B) a
        (fun f f' r => transport_const _ _ @ E f f' r) g.

(** The "beta-rule" of [choose_quotient_ind]. *)

  Lemma choose_quotient_ind_compute
    (P : (forall i, A i / R i) -> Type) `{!forall g, IsHSet (P g)}
    (a : forall (f : forall i, A i), P (fun i => class_of (R i) (f i)))
    (E : forall (f f' : forall i, A i) (r : forall i, R i (f i) (f' i)),
         qglue_forall f f' r # a f = a f')
    (f : forall i, A i)
    : choose_quotient_ind P a E (fun i => class_of (R i) (f i)) = a f.
  Proof.
    refine (Trunc_ind (fun a => (_ a).1 = _) _ _). cbn.
    intros [f' p].
    rewrite transport_sigma.
    set (p' := fun x => related_quotient_paths (R x) _ _ (p x)).
    assert (p = (fun i => qglue (p' i))) as pE.
    - funext x. apply hset_path2.
    - rewrite pE. apply E.
  Qed.

(** The "beta-rule" of [choose_quotient_rec]. *)

  Lemma choose_quotient_rec_compute
    {B : Type} `{!IsHSet B} (a : (forall i, A i) -> B)
    (E : forall (f f' : forall i, A i),
         (forall i, R i (f i) (f' i)) -> a f = a f')
    (f : forall i, A i)
    : choose_quotient_rec a E (fun i => class_of (R i) (f i)) = a f.
  Proof.
    apply (choose_quotient_ind_compute (fun _ => B)).
  Qed.
End choose_quotient_ind.

