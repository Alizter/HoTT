Require Import Basics.Overture Basics.Tactics.
Require Import Pointed.Core.
Require Import WildCat.Core WildCat.TwoOneCat WildCat.Universe.
Require Import Homotopy.SuccessorStructure.

Local Open Scope pointed_scope.

(** * Scratch work on structured-object wild categories *)

(** [Type] is better regarded as the ambient [(2,1)]-category than as another instance of the construction sought here.  Both [pType] and [SuccStr] are lax equalizers of endofunctors of [Type]. *)

(** ** Wild homotopy equalizers *)

(** This is the object part of a lax equalizer.  The witness is a wild morphism rather than an equality, which is essential if this construction is to remain independent of function extensionality. *)
Record WildEqualizer {A B : Type} `{IsGraph B} (L R : A -> B) := {
  weq_point : A;
  weq_witness : L weq_point $-> R weq_point
}.

Arguments weq_point {A B _ L R} x : rename.
Arguments weq_witness {A B _ L R} x : rename.

Section WildEqualizerCategory.
  Context {A B : Type} `{Is1Cat A} `{Is1Cat B}.
  Context (L R : A -> B)
    `{!Is0Functor L, !Is1Functor L}
    `{!Is0Functor R, !Is1Functor R}.

  (** A morphism is a morphism of underlying objects together with a square between the two equalizer witnesses. *)
  Record WildEqualizerHom (X Y : WildEqualizer L R) := {
    weq_hom : weq_point X $-> weq_point Y;
    weq_hom_square :
      fmap R weq_hom $o weq_witness X
      $== weq_witness Y $o fmap L weq_hom
  }.

  Arguments weq_hom {X Y} f : rename.
  Arguments weq_hom_square {X Y} f : rename.

  Instance isgraph_wildequalizer : IsGraph (WildEqualizer L R)
    := Build_IsGraph _ WildEqualizerHom.

  Definition wildequalizer_id (X : WildEqualizer L R)
    : WildEqualizerHom X X.
  Proof.
    snapply Build_WildEqualizerHom.
    - exact (Id (weq_point X)).
    - exact ((fmap_id R _ $@R weq_witness X)
        $@ cat_idl (weq_witness X)
        $@ (cat_idr (weq_witness X))^$
        $@ (weq_witness X $@L (fmap_id L _)^$)).
  Defined.

  Definition wildequalizer_compose
    {X Y Z : WildEqualizer L R}
    (g : WildEqualizerHom Y Z) (f : WildEqualizerHom X Y)
    : WildEqualizerHom X Z.
  Proof.
    snapply Build_WildEqualizerHom.
    - exact (weq_hom g $o weq_hom f).
    - exact ((fmap_comp R (weq_hom f) (weq_hom g)
                $@R weq_witness X)
        $@ cat_assoc (weq_witness X) (fmap R (weq_hom f))
              (fmap R (weq_hom g))
        $@ (fmap R (weq_hom g) $@L weq_hom_square f)
        $@ cat_assoc_opp (fmap L (weq_hom f)) (weq_witness Y)
              (fmap R (weq_hom g))
        $@ (weq_hom_square g $@R fmap L (weq_hom f))
        $@ cat_assoc (fmap L (weq_hom f)) (fmap L (weq_hom g))
              (weq_witness Z)
        $@ (weq_witness Z
              $@L (fmap_comp L (weq_hom f) (weq_hom g))^$)).
  Defined.

  Instance is01cat_wildequalizer : Is01Cat (WildEqualizer L R)
    := Build_Is01Cat _ _ wildequalizer_id
         (fun X Y Z => @wildequalizer_compose X Y Z).

End WildEqualizerCategory.

(** At the next level a 2-cell consists of an underlying 2-cell and a modification equation between the two resulting pastings. *)
Section WildEqualizerTwoCells.
  Context {A B : Type} `{Is1Cat A} `{Is21Cat B}.
  Context (L R : A -> B)
    `{!Is0Functor L, !Is1Functor L}
    `{!Is0Functor R, !Is1Functor R}.

  Record WildEqualizer2
    {X Y : WildEqualizer L R}
    (f g : WildEqualizerHom L R X Y) := {
    weq_homotopy : weq_hom L R X Y f $== weq_hom L R X Y g;
    weq_homotopy_square :
      weq_hom_square L R X Y f
        $@ (weq_witness Y $@L fmap2 L weq_homotopy)
      $== (fmap2 R weq_homotopy $@R weq_witness X)
        $@ weq_hom_square L R X Y g
  }.

  Arguments weq_homotopy {X Y f g} p : rename.
  Arguments weq_homotopy_square {X Y f g} p : rename.

End WildEqualizerTwoCells.

(** Continuing through [Is21Cat] requires a notion of functor that acts coherently on 3-cells.  [Is1Functor] stops one dimension too early, so that missing interface is a real prerequisite rather than an example-specific proof obligation. *)

(** ** Pointed types *)

Section StructuredObjectsAtUniverse.
  Universe u.

  Definition PointedObjects
    := WildEqualizer (fun _ : Type@{u} => (Unit : Type@{u})) idmap.

  Definition pointedobjects_of_ptype (X : pType) : PointedObjects.
  Proof.
    snapply Build_WildEqualizer.
    - exact X.
    - exact (fun _ => point X).
  Defined.

  Definition ptype_of_pointedobjects (X : PointedObjects) : pType
    := Build_pType (weq_point X) (weq_witness X tt).

  Definition pointedobjects_hom_of_pmap {X Y : pType} (f : X ->* Y)
    : WildEqualizerHom (fun _ : Type@{u} => (Unit : Type@{u})) idmap
        (pointedobjects_of_ptype X) (pointedobjects_of_ptype Y).
  Proof.
    snapply Build_WildEqualizerHom.
    - exact f.
    - intros [].
      exact (point_eq f).
  Defined.

  Definition pmap_of_pointedobjects_hom {X Y : PointedObjects}
    (f : WildEqualizerHom (fun _ : Type@{u} => (Unit : Type@{u})) idmap X Y)
    : ptype_of_pointedobjects X ->* ptype_of_pointedobjects Y.
  Proof.
    snapply Build_pMap.
    - exact (weq_hom (fun _ : Type@{u} => (Unit : Type@{u})) idmap X Y f).
    - exact (weq_hom_square
        (fun _ : Type@{u} => (Unit : Type@{u})) idmap X Y f tt).
  Defined.

  (** Thus the objects and morphisms of [pType] have the shape of the lax equalizer of the constant-[Unit] functor and the identity functor. *)

  (** ** Successor structures *)

  Definition SuccessorObjects
    := WildEqualizer (idmap : Type -> Type) idmap.

  Definition successorobjects_of_succstr (X : SuccStr) : SuccessorObjects.
  Proof.
    snapply Build_WildEqualizer.
    - exact X.
    - exact (@ss_succ X).
  Defined.

  Definition succstr_of_successorobjects (X : SuccessorObjects) : SuccStr
    := Build_SuccStr (weq_point X) (weq_witness X).

  Definition successorobjects_hom_of_ssmap {X Y : SuccStr} (f : X $-> Y)
    : WildEqualizerHom (idmap : Type -> Type) idmap
        (successorobjects_of_succstr X) (successorobjects_of_succstr Y).
  Proof.
    snapply Build_WildEqualizerHom.
    - exact f.
    - exact (ss_fun_succ f).
  Defined.

  Definition ssmap_of_successorobjects_hom {X Y : SuccessorObjects}
    (f : WildEqualizerHom (idmap : Type -> Type) idmap X Y)
    : succstr_of_successorobjects X $-> succstr_of_successorobjects Y.
  Proof.
    snapply Build_ssForall.
    - exact (weq_hom (idmap : Type -> Type) idmap X Y f).
    - exact (weq_hom_square (idmap : Type -> Type) idmap X Y f).
  Defined.

End StructuredObjectsAtUniverse.

(** The direct proofs of [Is21Cat Type] and [Is21Cat pType] share little beyond the hom-category and hom-groupoid interfaces already requested by [Build_Is21Cat].  The promising reuse has a different shape: first construct [Type], then derive structured-object categories such as [pType] and [SuccStr] from a generic lax-equalizer or higher displayed-category theorem.  [Type] is only the degenerate empty-signature case if one later generalizes from a single lax equation to arbitrary signatures. *)
