Require Import Basics.
Require Import WildCat.Core.
Require Import WildCat.Induced.
Require Import WildCat.Type.

(** n-Type is a (not so) wild category *)

Section Trunc.
  Context (n : trunc_index).

  Global Instance isgraph_trunctype : IsGraph n-Type := induced_graph trunctype_type.
  Global Instance is01cat_trunctype : Is01Cat n-Type := induced_01cat trunctype_type.
  Global Instance is1cat_trunctype  : Is1Cat  n-Type := induced_1cat  trunctype_type.
  Global Instance hasequivs_trunctype : HasEquivs n-Type := induced_hasequivs trunctype_type.
  Global Instance hasmorext_trunctype `{Funext} : HasMorExt n-Type
    := induced_hasmorext trunctype_type.
End Trunc.
