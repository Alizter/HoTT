Require Import Basics Types.
Require Import WildCat.Core.
Require Import WildCat.NatTrans.
Require Import WildCat.FunctorCat.
Require Import WildCat.Adjoint.
Require Import WildCat.Equiv.
Require Import WildCat.Opposite.
Require Import WildCat.Yoneda.
Require Import WildCat.Type.
Require Import WildCat.Prod.

(** Limits and colimits *)


(** For any category [A] there is a functor [diagonal : A $-> Fun01 J A] *)

Section ConstantFunctor.

  Context (A J : Type) `{Is1Cat A, IsGraph J}.

  Definition diagonal : A -> Fun01 J A :=
    fun x : A => Build_Fun01 J A (fun _ => x).

  Global Instance is0functor_diagonal : Is0Functor diagonal.
  Proof.
    apply Build_Is0Functor.
    intros a b f.
    snrapply Build_NatTrans.
    - intros c.
      exact f.
    - intros x y g.
      exact (cat_idr _ $@ (cat_idl _)^$).
  Defined.

  Global Instance is1functor_diagonal : Is1Functor diagonal.
  Proof.
    apply Build_Is1Functor.
    - intros a b f g p j.
      exact p.
    - intros a j.
      reflexivity.
    - intros a b c f g j.
      reflexivity.
  Defined.

  Definition fun11_diagonal : Fun11 A (Fun01 J A)
    := Build_Fun11 _ _ diagonal.

  (** The property of having a [J]-shaped limit. *)
  Class HasLimit := {
    cat_limit : Fun11 (Fun01 J A) A ;
    adjunction_cat_limit : Adjunction fun11_diagonal cat_limit;
  }.

  Class HasColimit := {
    cat_colimit : Fun11 (Fun01 J A) A ;
    adjunction_cat_colimit : Adjunction cat_colimit fun11_diagonal ;
  }.

End ConstantFunctor.

(** Preservation of limits *)

(** Property of a functor preserving limits. *)
Class PreservesLimits (A B J : Type) `{Is1Cat A, IsGraph J, !HasLimit A J,
  HasEquivs B, !HasLimit B J} (F : Fun11 A B) :=
  equiv_preserveslimits (x : Fun01 J A)
    : F (cat_limit A J x) $<~> cat_limit B J (fun01_compose F x).

(** This seems to be too strong *)
(* 
(** Property of a functor preserving limits. *)
Class PreservesLimits (A B J : Type) `{Is1Cat A, IsGraph J, !HasLimit A J,
  HasEquivs B, !HasLimit B J} (F : Fun11 A B) :=
  natequiv_preserveslimits
    : NatEquiv (F o cat_limit A J) (cat_limit B J o fun01_compose F).
 *)

(** Properties of limits (and colimits) *)

(** Right adjoints preserve limits *)
Global Instance preserveslimits_right_adjoint `{Funext} (A B J : Type)
  `{HasEquivs A, HasEquivs B, Is01Cat J, !HasLimit A J, !HasLimit B J,
     !HasMorExt A, !HasMorExt B, !HasMorExt (Fun01 J A), !HasMorExt (Fun01 J B)}
  (L : Fun11 A B) (R : Fun11 B A) (adj : L ⊣ R)
  : PreservesLimits B A J R.
Proof.
  intros K.
  (** We proceed via the yoneda lemma. We will also show what the goal looks like in a more compact and readable notation. Ideally, the goal would actually look like this. *)
  srapply yon_equiv.
  (** A(x, R (lim y)) ≃ B(x, lim (R o y)) *)
  refine (natequiv_compose (natequiv_adjunction_l
    (adjunction_cat_limit _ _) (fun11_fun01_postcomp R K)) _).
  (** A(x, R (lim y)) ≃ B^J(Δx, (R o y)) *)
  refine (natequiv_compose (natequiv_prewhisker (natequiv_adjunction_l
    (adjunction_postcomp _ _ J L R adj) K) (diagonal A J)) _).
  (** A(x, R (lim y)) ≃ A^J(L o Δx, y) *)
  refine (natequiv_compose _ (natequiv_inverse _ _
    (natequiv_adjunction_l adj (cat_limit B J K)))).
  (** B(L x, lim y) ≃ A^J(L o Δx, y) *)
  refine (natequiv_compose _ (natequiv_inverse _ _ (natequiv_prewhisker
    (natequiv_adjunction_l (adjunction_cat_limit _ _) K) L))).
  (** A^J(Δ o L, y) ≃ A^J(L o Δx, y) *)
  (** Now we do some reshuffling to show that the diagonal and L commute. *)
  refine (natequiv_compose (natequiv_inverse _ _ _) _).
  1: apply natequiv_functor_assoc_ff_f.
  refine (natequiv_compose _ _).
  2: apply natequiv_functor_assoc_ff_f.
  (** This is where morphism extensionality and funext is used. *)
  snrapply natequiv_postwhisker.
  (** Why can't typeclasses find this? *)
  4: rapply hasequivs_op.
  2: rapply is1functor_yon.
  (** This can probably be generalized, but this particular proof is pretty complicated due to all the op terms involved. *)
  (** Perhaps it's time for a natequiv_adjointify? *)
  snrapply Build_NatEquiv.
  { intros a. cbn.
    srapply cate_adjointify.
    - snrapply Build_NatTrans.
      1: intro j; exact (Id _).
      intros i j f.
      rapply cat_postwhisker.
      rapply fmap_id.
    - snrapply Build_NatTrans.
      1: intro j; exact (Id _).
      intros i j f.
      rapply cat_prewhisker.
      rapply gpd_rev.
      rapply fmap_id.
    - intros i.
      rapply cat_idl.
    - intros j.
      rapply cat_idr. }
  intros a a' f.
  unfold trans_comp.
  unfold cate_adjointify.
  refine ((cate_buildequiv_fun _ $@R _) $@ _).
  refine (_ $@ (_ $@L _)).
  2: symmetry; rapply cate_buildequiv_fun.
  intros j; exact (cat_idr _ $@ (cat_idl _)^$).
Defined.

(** Property of a functor preserving colimits. *)
Class PreservesColimits (A B J : Type) `{Is1Cat A, IsGraph J, !HasColimit A J,
  HasEquivs B, !HasColimit B J} (F : Fun11 A B) :=
  equiv_preservescolimits (x : Fun01 J A)
    : F (cat_colimit A J x) $<~> cat_colimit B J (fun01_compose F x).

(* TODO: there may be a clever way to do this using op *)
(** Left adjoints preserve colimits *)
Global Instance preservescolimits_left_adjoint `{Funext} (A B J : Type)
  `{HasEquivs A, HasEquivs B, Is01Cat J, !HasColimit A J, !HasColimit B J,
    !HasMorExt (Fun01 J A), !HasMorExt (Fun01 J B), !HasMorExt A, !HasMorExt B}
  (L : Fun11 A B) (R : Fun11 B A) (adj : L ⊣ R)
  : PreservesColimits A B J L.
Proof.
  intros K.
  (** We proceed via the coyoneda lemma. The proof is very much the same as before only dual. Ideally it would simply be a consequence of the other proof, but that seems to require cleverness I am unable to provide currently. *)
  (** Note that writing these steps can be tricky, since coq doesn't follow when they are broken up. Doing them in one go however let's coq pick the correct typeclasses. There maybe a way around this. *)
  srapply opyon_equiv.
  (** We do the right hand side first *)
  refine (natequiv_compose (natequiv_inverse _ _
    (natequiv_adjunction_r adj (cat_colimit A J K))) _).
  refine (natequiv_compose (natequiv_inverse _ _ (natequiv_prewhisker
    (natequiv_adjunction_r (adjunction_cat_colimit A J) K) R)) _).
  (** Now the left hand side *)
  refine (natequiv_compose _
    (natequiv_adjunction_r (adjunction_cat_colimit B J) _)).
  refine (natequiv_compose _ (natequiv_prewhisker
    (natequiv_adjunction_r (adjunction_postcomp _ _ _ _ _ adj) _) _)).
  (** Reassociating *)
  refine (natequiv_compose _
    (natequiv_functor_assoc_ff_f _ (fun11_fun01_postcomp R) _)).
  refine (natequiv_compose (natequiv_inverse _ _
    (natequiv_functor_assoc_ff_f (opyon K) (diagonal A J) R)) _).
  rapply natequiv_postwhisker.
  (** TODO: We can probably make this a seperate lemma *)
  (** Strange that this is shorter than the limit one. *)
  snrapply Build_NatEquiv.
  { intros b.
    snrapply Build_NatEquiv.
    1: intros j; reflexivity.
    intros a a' f.
    refine ((_ $@R _) $@ _ $@ (_ $@L _^$)).
    1,3: apply cate_buildequiv_fun.
    exact (cat_idl _ $@ fmap_id _ _ $@ (cat_idr _)^$). }
  intros a a' f j.
  refine ((_ $@R _) $@ _ $@ (_ $@L _^$)).
  1,3: apply cate_buildequiv_fun.
  exact (cat_idl _ $@ (cat_idr _)^$).
Defined.

(** * Properties of diagonal functor *)

(** The diagonal functor has various useful properties we would like to use. *)

Definition fun11_eval_fun01 {A B : Type}
  `{IsGraph A, Is1Cat B}
  (a : A)
  : Fun11 (Fun01 A B) B.
Proof.
  snrapply Build_Fun11.
  - intros F.
    exact (F a).
  - snrapply Build_Is0Functor.
    intros F G [t n].
    exact (t a).
  - snrapply Build_Is1Functor.
    + intros F G u v r.
      exact (r a).
    + reflexivity.
    + reflexivity.
Defined.


Section Swap.

  Context (A B C : Type)
    `{Is1Cat A, Is1Cat B, Is1Cat C}.

  Definition swap_fun01
    : Fun01 A (Fun01 B C) -> Fun01 B (Fun01 A C).
  Proof.
    intros F.
    snrapply Build_Fun01.
    { intros b.
      snrapply Build_Fun01.
      { intros a.
        exact (F a b). }
      apply Build_Is0Functor.
      intros a a' f.
      exact (fmap F f b). }
    snrapply Build_Is0Functor.
    intros b b' g.
    simpl.
    snrapply Build_NatTrans.
    { intros a.
      exact (fmap (F a) g). }
    hnf.
    intros a a' f.
    symmetry.
    cbn; set (fmap F f) as r.
    exact (isnat r g).
  Defined.

  Global Instance is0functor_swap_fun01 : Is0Functor swap_fun01.
  Proof.
    snrapply Build_Is0Functor.
    intros F G n.
    snrapply Build_NatTrans.
    { intros b.
      snrapply Build_NatTrans.
      { intros a.
        exact (n a b). }
      intros a a' f.
      exact (isnat n f b). }
    intros b b' g a.
    exact (isnat (n a) g).
  Defined.

  Global Instance is1functor_swap_fun01 : Is1Functor swap_fun01.
  Proof.
    unshelve econstructor; simpl.
    - intros F G n m p b a.
      exact (p a b).
    - intros F b a.
      exact (Id _).
    - intros F G K n m b a.
      exact (Id _).
  Defined.

  (** The swap functor (for Fun01). *)
  Definition fun11_swap_fun01
    : Fun11 (Fun01 A (Fun01 B C)) (Fun01 B (Fun01 A C))
    := Build_Fun11 _ _ swap_fun01.

  (** Composing a pulled back diagonal with the swap functor is again the diagonal. *)
  Lemma natequiv_swap_fun01_diagonal `{!HasEquivs C}
    : NatEquiv
        (fun11_compose fun11_swap_fun01 (fun11_fun01_postcomp (fun11_diagonal _ _)))
        (fun11_diagonal _ _).
  Proof.
    snrapply Build_NatEquiv.
    { intros F.
      snrapply Build_NatEquiv.
      { intros b.
        snrapply Build_NatEquiv.
        { intros a.
          reflexivity. }
        intros a a' f; cbn.
        refine ((cate_buildequiv_fun _ $@R _) $@ cat_idl _ $@ _^$).
        exact ((_ $@L cate_buildequiv_fun _) $@ cat_idr _). }
        intros b b' g a; cbn.
        refine (cat_idr _ $@ (cat_idl _)^$). }
    simpl.
    intros F G n b a. simpl. cbv.
    refine ((cate_buildequiv_fun _ $@R _) $@ cat_idl _ $@ _^$).
    exact ((_ $@L cate_buildequiv_fun _) $@ cat_idr _).
  Defined.

End Swap.

(* (** TODO: swap is an equivlanece therefore an adjunction *)
Global Instance iequiv_swap_fun01 {A B C} `{IsGraph A, IsGraph B, Is1Cat C}
  : IsEquiv (swap_fun01 A B C).
Proof.
  snrapply isequiv_adjointify.
  1: exact (swap_fun01 B A C).
  - intros F.
    cbv. *)
    
(** Showing that swap_fun01 is an equivalence requires some funext *)

Lemma adjunction_swap_fun01 {A B C : Type}
  `{IsGraph A, IsGraph B, Is1Cat C,
    !HasMorExt (Fun01 A (Fun01 B C)), !HasMorExt (Fun01 B (Fun01 A C))}
  : swap_fun01 A B C ⊣ swap_fun01 B A C.
Proof.
  snrapply Build_Adjunction_unit_counit.
  1-4: exact _.
  { snrapply Build_NatTrans.
    { intros F.
      snrapply Build_NatTrans.
      1: exact (id_transformation _).
      intros b b' f a.
      exact (cat_idl _ $@ (cat_idr _)^$). }
    intros F G h b a.
    exact (cat_idl _ $@ (cat_idr _)^$). }
  { snrapply Build_NatTrans.
    { intros F.
      snrapply Build_NatTrans.
      1: exact (id_transformation _).
      intros b b' f a.
      exact (cat_idl _ $@ (cat_idr _)^$). }
    intros F G h b a.
    exact (cat_idl _ $@ (cat_idr _)^$). }
  1: intros F b a; exact (cat_idl _).
  intros F a b; exact (cat_idl _).
Defined.

(** ** (Co)limits in functor categories *)

(** These are computed pointwise *)

(** Proof sketch:
We use the swap equivalence and its interaction with diagonal functors to construct the appropriate (co)limit functor.

Let C, D be cats. J be an indexing shape (basically a cat). We have the following functors:

   Δ  : D -> [J,D]             (diagonal functor from D)
   Δ* : [C,D] -> [C,[J,D]]     (pullback of diagonal functor)
 lim  : [J,D] -> D             (limit functor)
 lim* : [C,[J,D]] -> [C,D]     (pullback of limit functor)

Observe that Δ ⊣ lim and therefore Δ* ⊣ lim*.
Now we also have the following functors:

   Δ' : [C,D] -> [J,[C,D]]     (diagonal functor from [C,D])
s_C,J : [C,[J,D]] -> [J,[C,D]] (argument swap functor)

Note that s_C,J is an equivalence, and s_C,J ⊣ s_J,C
Importantly, the swap functor interacts with the diagonal as follows:

(★)  s_C,J o Δ* ≃ Δ'

Now we need to show that (lim* o s_J,C) is a limit functor. i.e. we need to have the following adjunction:

   Δ' ⊣ lim* o s_J,C      i.e.   [J,[C,D]](Δ'x,y) ≃ [C,D](x,lim*(s_J,C y))

This can be calculated:

  [J,[C,D]](Δ'x,y) ≃ [J,[C,D]]((s_C,J (Δ*x)),y)    (via (★)) 
                   ≃ [C,[J,D]](Δ*x,(s_J,C y))      (via s_C,J ⊣ s_J,C)
                   ≃ [C,D](x,lim*(s_J,C y))        (via Δ* ⊣ lim* )

Perhaps a more direct calculation would be the following:

             Δ' ⊣ lim* o s_J,C
 <=> s_C,J o Δ* ⊣ lim* o s_J,C      (via (★))
 <=> (Δ* ⊣ lim* ) o (s_C,J ⊣ s_J,C) (composition of adjoints)

And for colimits:

      colim* o s_J,C ⊣ Δ'
  <=> colim* o s_J,C ⊣ s_C,J o Δ*
  <=> (s_J,C ⊣ s_J,C) o (colim* o ⊣ Δ* )

*)

Global Instance haslimit_fun01 `{Funext}
  (A B J : Type) `{Is01Cat A, HasEquivs B, Is01Cat J}
  `{!HasLimit B J}
  `{!HasMorExt B,
    !HasMorExt (Fun01 A B),
    !HasMorExt (Fun01 A (Fun01 J B)),
    !HasMorExt (Fun01 J (Fun01 A B)),
    !HasMorExt (Fun01 J B)}
  : HasLimit (Fun01 A B) J.
Proof.
  snrapply Build_HasLimit.
  { nrefine (fun11_compose _ (fun11_swap_fun01 J A B)).
    apply fun11_fun01_postcomp.
    rapply cat_limit. }
  rapply (adjunction_natequiv_left _ _ _
    (natequiv_swap_fun01_diagonal _ _ _)).
  rapply adjunction_compose.
  { rapply adjunction_postcomp.
    apply adjunction_cat_limit. }
  apply adjunction_swap_fun01.
Defined.

Global Instance hascolimit_fun01 `{Funext}
  (A B J : Type) `{Is01Cat A, HasEquivs B, Is01Cat J}
  `{!HasColimit B J}
  `{!HasMorExt B,
    !HasMorExt (Fun01 A B),
    !HasMorExt (Fun01 A (Fun01 J B)),
    !HasMorExt (Fun01 J (Fun01 A B)),
    !HasMorExt (Fun01 J B)}
  : HasColimit (Fun01 A B) J.
Proof.
  snrapply Build_HasColimit.
  { nrefine (fun11_compose _ (fun11_swap_fun01 J A B)).
    apply fun11_fun01_postcomp.
    rapply cat_colimit. }
  rapply (adjunction_natequiv_right _ _ _
    (natequiv_swap_fun01_diagonal _ _ _)).
  rapply adjunction_compose.
  1: apply adjunction_swap_fun01.
  rapply adjunction_postcomp.
  apply adjunction_cat_colimit.
Defined.

(** ** Preservation of (co)limits by (co)limits *)

Lemma preserveslimits_cat_limit `{Funext} (A I J : Type)
  `{HasEquivs A, Is01Cat I, Is01Cat J}
  `{!HasMorExt A,
    !HasMorExt (Fun01 I A),
    !HasMorExt (Fun01 J A),
    !HasMorExt (Fun01 I (Fun01 J A)),
    !HasMorExt (Fun01 J (Fun01 I A))}
  (** We have a lot of morphism extensionality assumptions here. One wonders if there ought to be a lemma hasmorext_fun01 which sorts these out. I wasn't able to come up with such a lemma and I think this is due to the incoherent 2-cells in the functor category. *)
  `{!HasLimit A I, !HasLimit A J}
  : PreservesLimits _ _ I (cat_limit A J).
Proof.
  exact (preserveslimits_right_adjoint _ _ _ _ _ (adjunction_cat_limit A J)).
Defined.

Lemma preservescolimits_cat_colimit `{Funext} (A I J : Type)
  `{HasEquivs A, Is01Cat I, Is01Cat J}
  `{!HasMorExt A,
    !HasMorExt (Fun01 I A),
    !HasMorExt (Fun01 J A),
    !HasMorExt (Fun01 I (Fun01 J A)),
    !HasMorExt (Fun01 J (Fun01 I A))}
  `{!HasColimit A I, !HasColimit A J}
  (** See comment above. *)
  `{!HasColimit (Fun01 J A) I}
  : PreservesColimits _ _ I (cat_colimit A J).
Proof.
  exact (preservescolimits_left_adjoint _ _ _ _ _ (adjunction_cat_colimit A J)).
Defined.

