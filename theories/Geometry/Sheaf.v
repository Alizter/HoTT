Require Import Basics Types WildCat.
Require Import Geometry.Site.
Require Import Geometry.Presheaf.

(** In this file we define sheaves on a site. We follow Johnstones definition from "Sketches of an elephant", C2.1. *)

(** First we package up the notion of a compatible family. This will be useful when we define what it means for a presheaf to be a sheaf wrt. a certain topology. *)
Record CompatibleFamily
  {C : Site}   (** Let C be a site *)
  (A : PSh C)  (** Let A be a presheaf on C *)
  {U : C}      (** Let U be an object of C *)
   (** And let f be a covering of U *)
  (f : Sink U) `{!IsCover f} :=
{ (** We call a family of elements of [A U] a compatible family if *)
  cf_fam (i : sink_index f) : A (sink_domain f i);
  (** For all f and g from V so that they commute with the cover *)
  cf_comp (V : C) (i j : sink_index f)
    (g : V $-> sink_domain f i) (h : V $-> sink_domain f j)
    (p : f i $o g $== f j $o h)
    (** [A] agrees on the corresonding elements *)
    : fmap A (g : Hom (A:=C^op) _ V) (cf_fam i)
    = fmap A (h : Hom (A:=C^op) _ V) (cf_fam j);
}.

Coercion cf_fam : CompatibleFamily >-> Funclass.

(** A presheaf [A] on a site [C] is a sheaf if for every cover f, and every compatible family [s], there exists a unique [t : A U] such that for all [i], [fmap A (f i) t = s i]. *)
Class IsSheaf {C : Site} (A : PSh C) := {
  issheaf {U : C} (f : Sink U) `{!IsCover f}
    (s : CompatibleFamily A f)
    : Contr {t : A U & forall i,
        fmap A (f i : Hom (A:=C^op) U _) t = (s i)};
}.

Record Sh (C : Site) := {
  sheaf_presheaf : PSh C;
  sheaf_issheaf : IsSheaf sheaf_presheaf;
}.

Coercion sheaf_presheaf : Sh >-> PSh.
Global Existing Instance sheaf_issheaf.

(** Sheaves form a wild category induced by the wild category structure on presheaves *)
Global Instance isgraph_sh {C} : IsGraph (Sh C) := induced_graph (sheaf_presheaf C).
Global Instance is01cat_sh {C} : Is01Cat (Sh C) := induced_01cat (sheaf_presheaf C).
Global Instance is1cat_sh  {C} : Is1Cat  (Sh C) := induced_1cat  (sheaf_presheaf C).
Global Instance hasequivs_sh {C} : HasEquivs (Sh C) := induced_hasequivs (sheaf_presheaf C).


