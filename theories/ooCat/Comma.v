(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.
Require Export ooCat.Cat1 ooCat.Laxity.
Require Export ooCat.Prod.
Require Import ooCat.Sigma.

Generalizable Variables m n p A B C.

(** ** Comma categories *)

(** We define the comma category of [F : A -> C] and [G : B -> C] as a displayed category over [A * B], of which we can then take the sigma-type (but also other things like the pi-type, or pullbacks along functors). *)

(** Since products are not minning the dimensions, we have to take [A] and [B] to be the same dimension also. *)

Definition GenDComma (l : Stream Laxity)
           {A B C : Type} `{IsGlob n A} `{IsGlob n B} `{HasEquivs p C}
           (F : A -> C) `{!IsFunctor0 F} (G : B -> C) `{!IsFunctor0 G}
           (z : A * B)
  := lHom (head l) (F (fst z)) (G (snd z)).

Notation DIsoComma := (GenDComma all_pseudo).
Notation DComma := (GenDComma one_colax).

(** This is one of the sneakiest coinductions so far: we have to identify the hom-categories of a comma category as comma categories themselves.  Given objects [p1 : F a1 $-> G b1] and [p2 : F a2 $-> G b2] of the comma (F/G), a morphism [p1 $-> p2] consists of morphisms [f : a1 $-> a2] and [g : b1 $-> b2] together with a morphism (perhaps invertible) [(p2 $o fmap F f) $-> (fmap G g $o p1)].  But this is an *object* of the comma category between the composite functors
(a1 $-> a2)  --(fmap F)-->  (F a1 $-> F a2)  --(p2 $o ?)-->  (F a1 $-> G b2)
(b1 $-> b2)  --(fmap G)-->  (G b1 $-> G b2)  --(? $o p1)-->  (F a1 $-> G b2).
*)

CoFixpoint isdglob_gendcomma (l : Stream Laxity)
           {A B C : Type} `{IsGlob n A} `{IsGlob n B} `{HasEquivs m C}
           (F : A -> C) `{!IsFunctor0 F} (G : B -> C) `{!IsFunctor0 G}
  : IsDGlob m (GenDComma l F G).
Proof.
  unshelve econstructor.
  - intros [a1 b1] [a2 b2] fg p1 p2; unfold GenDComma in *; cbn in *.
    destruct (head l); cbn in *.
    (** The colax and pseudo cases are the same, with an equivalence just regarded as a map. *)
    1-2:refine (GenDComma (tail l) (cat_postcomp (F a1) p2 o fmap F) (cat_precomp (G b2) p1 o fmap G) fg).
    refine (GenDComma (tail l) (cat_precomp (F a2) p1 o fmap F) (cat_postcomp (G b1) p2 o fmap G) fg).
  - intros [a1 b1] [a2 b2] p1 p2; unfold GenDComma in p1, p2.
    destruct (head l); cbn; apply isdglob_gendcomma.
Defined.

Global Existing Instance isdglob_gendcomma.

(** The standard comma category is the sigma-category of the displayed one. *)
Definition GenComma (l : Stream Laxity)
           {A B C : Type} `{IsGlob n A} `{IsGlob n B} `{HasEquivs m C}
           (F : A -> C) `{!IsFunctor0 F} (G : B -> C) `{!IsFunctor0 G}
  := sig (GenDComma l F G).

Notation IsoComma := (GenComma all_pseudo).
Notation Comma := (GenComma one_colax).

Section CommaProjections.

  Context (l : Stream Laxity) {A B C : Type}
   `{IsGlob n A} `{IsGlob n B} `{HasEquivs m C}
    {F : A -> C} `{!IsFunctor0 F}
    {G : B -> C} `{!IsFunctor0 G}.

  Definition gencomma_pr1 : GenComma l F G -> A
    := fun x => fst x.1.

  Definition gencomma_pr2 : GenComma l F G -> B
    := fun x => snd x.1.

  Global Instance isfunctor0_gencomma_pr1 : IsFunctor0 gencomma_pr1.
  Proof.
    rapply isfunctor0_compose.
  Defined.

  Global Instance isfunctor0_gencomma_pr2 : IsFunctor0 gencomma_pr2.
  Proof.
    rapply isfunctor0_compose.
  Defined.

End CommaProjections.

Notation comma_pr1 := (gencomma_pr1 one_colax).
Notation comma_pr2 := (gencomma_pr2 one_colax).

(** The arrow category of [A] is the comma category of its identity functor over itself. *)
Definition GenDArrow (l : Stream Laxity) (A : Type) `{HasEquivs n A}
  := @GenDComma l A A A n _ _ n _ _ _ idmap _ idmap _.

(** Note that the general comma category [GenDComma l F G] could be obtained by pullback of [GenDArrow l C] along [F*G : A*B -> C*C].  However, a coinductive definition of [GenDArrow] would involve more general comma categories at the coinductive step, so it makes more sense (and probably makes it easier to satisfy Coq's guardedness checker) to define general comma categories directly. *)

(** TODO: If [A] and [B] are 0-coherent and [F] and [G] are 1-coherent, then the comma category should be 1-coherent with equivalences, and so on. *)

