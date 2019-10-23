(** * Category Theory *)
(** To get all of the category theory library in scope with the proper qualified names, you should [Require Import Categories.] or [Require Import HoTT.Categories.] *)

(** First we give modules to all of the kinds of category theory constructions (corresponding to directories), so that we can refer to them as [Category.foo] or [Functor.foo] after [Require Import Categories.] *)
(** ** Categories *)
Require Categories.Category.
(** ** Functors *)
Require Categories.Functor.
(** ** Natural Transformations *)
Require Categories.NaturalTransformation.
(** ** Functor Categories *)
Require Categories.FunctorCategory.
(** ** Groupoids *)
Require Categories.GroupoidCategory.
(** ** Precategory of Groupoids *)
Require Categories.CategoryOfGroupoids.
(** ** Discrete Categories *)
Require Categories.DiscreteCategory.
(** ** Indiscrete Categories *)
Require Categories.IndiscreteCategory.
(** ** Finite Discrete Categories (natural numbers as categories) *)
Require Categories.NatCategory.
(** ** Chain Categories [[n]] *)
Require Categories.ChainCategory.
(** ** Initial and Terminal Categories *)
Require Categories.InitialTerminalCategory.
(** ** The Category of Sets *)
Require Categories.SetCategory.
(** ** The Category of Simplicial Sets *)
Require Categories.SimplicialSets.
(** ** The Category of Semi-Simplicial Sets *)
Require Categories.SemiSimplicialSets.
(** ** The Hom Functor *)
Require Categories.HomFunctor.
(** ** Profunctors *)
Require Categories.Profunctor.
(** ** The Category of Categories *)
Require Categories.Cat.
(** ** Laws about Functor Categories *)
Require Categories.ExponentialLaws.
(** ** Laws about Product Categories *)
Require Categories.ProductLaws.
(** ** Comma Categories *)
Require Categories.Comma.
(** ** Universal Properties and Universal Morphisms *)
Require Categories.UniversalProperties.
(** ** Kan Extensions *)
Require Categories.KanExtensions.
(** ** Adjunctions *)
Require Categories.Adjoint.
(** ** Limits *)
Require Categories.Limits.
(** ** Pseudofunctors *)
Require Categories.Pseudofunctor.
(** ** Pseudonatural Transformations *)
Require Categories.PseudonaturalTransformation.
(** ** Lax Comma Categories *)
Require Categories.LaxComma.
(** ** Duality as a Functor *)
Require Categories.DualFunctor.
(** ** The Grothendieck Construction *)
Require Categories.Grothendieck.
(** ** The Category of Sections of a Functor *)
Require Categories.CategoryOfSections.
(** ** The Dependent Product *)
Require Categories.DependentProduct.
(** ** The Yoneda Lemma *)
Require Categories.Yoneda.
(** ** The Structure Identity Principle *)
Require Categories.Structure.
(** ** Fundamental Pregroupoids *)
Require Categories.FundamentalPreGroupoidCategory.
(** ** Homotopy PreCategory *)
Require Categories.HomotopyPreCategory.

(* We bind the record structures for [PreCategory], [IsCategory], [IsStrictCategory], [Functor], and eventually [NaturalTransformation] at top level. *)
Local Set Warnings Append "-notation-overridden".
Include Categories.Category.Core.
Include Categories.Category.Strict.
Include Categories.Category.Univalent.
Include Categories.Functor.Core.
Include Categories.NaturalTransformation.Core.
Include Categories.FunctorCategory.Core.
Include Categories.GroupoidCategory.Core.
Include Categories.CategoryOfGroupoids.
Include Categories.DiscreteCategory.Core.
Include Categories.IndiscreteCategory.Core.
Include Categories.NatCategory.Core.
Include Categories.ChainCategory.Core.
Include Categories.InitialTerminalCategory.Core.
Include Categories.SetCategory.Core.
Include Categories.SimplicialSets.Core.
Include Categories.SemiSimplicialSets.Core.
Include Categories.HomFunctor.
Include Categories.Profunctor.Core.
Include Categories.Cat.Core.
Include Categories.Comma.Core.
Include Categories.UniversalProperties.
Include Categories.KanExtensions.Core.
Include Categories.Adjoint.Core.
Include Categories.Limits.Core.
Include Categories.Pseudofunctor.Core.
Include Categories.PseudonaturalTransformation.Core.
Include Categories.LaxComma.Core.
Include Categories.DualFunctor.
Include Categories.CategoryOfSections.Core.
Include Categories.DependentProduct.
Include Categories.Yoneda.
Include Categories.Structure.Core.
Include Categories.FundamentalPreGroupoidCategory.
Include Categories.HomotopyPreCategory.

Require Export Categories.Notations.

(** Some checks that should pass, if all of the importing went correctly. *)
(*Check PreCategory.
Check IsStrictCategory _.
Check Category.compose.
Check Category.sum.
Check Category.Sum.sum_compose.
Check Functor.sum.
Check Functor.Prod.Core.unique.
Check (_ o _)%morphism.
Check (_ o _)%functor.*)
