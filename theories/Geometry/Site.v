Require Import Basics Types WildCat.

(** In this file we develop the notion of a site as developed in Peter Johnstones "Sketches of an Elephant". This file will largely follow the ideas developed in section C2.1. *)

(** A sink is just a collection of morphisms with common codomain. *)
Record Sink {A : Type} `{IsGraph A} (U : A) := {
  sink_index : Type;
  ishset_sink_index : IsHSet sink_index;
  sink_domain : sink_index -> A;
  sink_map : forall i, sink_domain i $-> U;
}.

Coercion sink_map : Sink >-> Funclass.
Arguments sink_index {A _ U}.
Arguments sink_domain {A _ U}.
Arguments sink_map {A _ U}.
Global Existing Instance ishset_sink_index.

(** A coverage of a category C is a family deciding which sinks in C are coverings, equipped with a proof that for any morphism B -> A in C, the coverings of B factor through the coverings of A. *)
Record Coverage (C : Type) `{Is1Cat C} := {
  (** We have a type family deciding if a sink is a cover. We call such a sink a covering family. *)
  coverage_iscover {A : C} : Sink A -> Type;
  (** Let [f] be a covering family of [A] in the category [C] *)
  coverage_closed (A : C) (f : Sink A) (f_iscover : coverage_iscover f)
    (B : C) (g : B $-> A) (** Given a morphism [B $-> A] *) 
      : exists (** There exists a covering family [h] of [B] *)
          (h : Sink B) (h_iscover : coverage_iscover h),
          forall (j : sink_index h), (** Such that forall morphisms in [h] *)
            (** There exists a morphism in [f] such that [g $o h] factors through [f] *)
            exists (i : sink_index f) (k : sink_domain h j $-> sink_domain f i),
              g $o sink_map h j $== sink_map f i $o k;
}.

(** A site consists of a category C and a coverge on C. *)
(** We want a site to be a coherent 1-category as later we will be doing presheaf constructions over this site. These constructions typically require homs to be hsets. *)
Record Site := {
  (** A wild cat with equivalences *)
  site_type : Type;
  site_isgraph : IsGraph site_type;
  site_is01cat : Is01Cat site_type;
  site_is1cat  : Is1Cat  site_type;
  site_istrunc_hom : forall x y, IsHSet (x $-> y);
  site_coverage : Coverage site_type;
}.

Coercion site_type : Site >-> Sortclass.
Global Existing Instances site_isgraph site_is01cat
  site_is1cat site_istrunc_hom.

(** We give a better name for [coverage_iscover] and make it a class *)
Definition IsCover {C : Site} {U : C} (f : Sink U)
  := coverage_iscover C (site_coverage C) f.
Existing Class IsCover.
