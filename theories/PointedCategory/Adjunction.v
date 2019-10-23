Require Import Basics.
Require Import Types.
Require Import Pointed.Core.
Require Import Pointed.pMap.
Require Import Pointed.pHomotopy.
Require Import Pointed.pEquiv.
Require Import PointedCategory.Functor.
Require Import PointedCategory.pFunctor.

Local Open Scope pointed_scope.
Declare Scope pointed_cat_scope.
Local Open Scope pointed_cat_scope.

Section Adjunction.

  Context (F G : Functor).
  Arguments F_functor _ {_ _ _}.
  
  (* Here is the data of an adjunction. *)
  Class Adjunction := {
    (* The unit of the adjunction. *)
    adj_unit X : X ->* G (F X);
    (* The counit of the adjunction *)
    adj_counit X : F (G X) ->* X;
    (** Naturality of the unit. *)
    adj_unit_nat {A B} (f : A ->* B)
      : adj_unit B o* f ==* F_functor G (F_functor F f) o* adj_unit A;
    (** Naturality of the counit. *)
    adj_counit_nat {A B} (f : A ->* B)
      : f o* adj_counit A ==* adj_counit B o* F_functor F (F_functor G f);
    (** The triangle identity for G. *)
    adj_zig X : F_functor G (adj_counit X) o* adj_unit (G X) ==* pmap_idmap;
    (** The triangle identity for F. *)
    adj_zag X : adj_counit (F X) o* F_functor F (adj_unit X) ==* pmap_idmap;
   }.

  Context `{Funext}.

  Theorem equiv_adjunction (adj : Adjunction) {X Y : pType}
    : (F X ->* Y) <~> (X ->* G Y).
  Proof.
    destruct adj as [unit counit unit_nat counit_nat zig zag].
    serapply equiv_adjointify.
    1: exact (fun f => F_functor G f o* unit X).
    1: exact (fun g => counit Y o* F_functor F g).
    { intro g.
      apply path_pmap.
      refine (pmap_prewhisker _ F_compose @* _).
      refine (pmap_compose_assoc _ _ _ @* _).
      refine (pmap_postwhisker _ (unit_nat _ _ _)^* @* _).
      refine ((pmap_compose_assoc _ _ _)^* @* _).
      refine (pmap_prewhisker _ (zig _) @* pmap_postcompose_idmap _). }
    { intros f.
      apply path_pmap.
      refine (pmap_postwhisker _ F_compose @* _).
      refine ((pmap_compose_assoc _ _ _)^* @* _).
      refine (pmap_prewhisker _ (counit_nat _ _ _)^* @* _).
      refine (pmap_compose_assoc _ _ _ @* _).
      refine (pmap_postwhisker _ (zag _) @* _).
      apply pmap_precompose_idmap. }
    Defined.

  Theorem pequiv_adjunction (adj : Adjunction) {X Y : pType}
    {h : IsPointedFunctor G}
    : (F X ->* Y) <~>* (X ->* G Y).
  Proof.
    serapply Build_pEquiv'.
    1: by apply equiv_adjunction.
    cbn; apply path_pmap.
    refine (pmap_prewhisker _ F_functor_zero @* _).
    apply pmap_postcompose_const.
  Defined.

  Definition equiv_adjunction_nat_r {A B B' : pType}
    (adj : Adjunction) (f : F A ->* B) (g : B ->* B')
    : equiv_adjunction _ (g o* f)
    ==* F_functor G g o* equiv_adjunction _ f.
  Proof.
    refine (_ @* pmap_compose_assoc _ _ _).
    apply pmap_prewhisker, F_compose.
  Defined.

Definition equiv_adjunction_nat_l {A A' B : pType}
  (adj : Adjunction) (f : A ->* G B) (g : A' ->* A)
  : (equiv_adjunction _)^-1 (f o* g)
  ==* (equiv_adjunction _)^-1 f o* F_functor F g.
Proof.
  refine (_ @* (pmap_compose_assoc _ _ _)^*).
  apply pmap_postwhisker, F_compose.
Defined.

End Adjunction.

