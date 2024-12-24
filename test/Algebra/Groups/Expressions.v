From HoTT Require Import Basics.Overture Groups.Group AbGroups.AbelianGroup.

Set Universe Minimization ToSet.

(** In this file, we test various aspects of writing group expressions. These kinds of expressions appear throughout the library, but since mathclasses is quite sensitive to subtle changes, we keep this file to document and enforce certain behaviours.

We use the [Type] vernacular command which is like [Check] but doesn't allow for evars. *)

Section Groups.

  (** We used a fixed universe of groups since the [Type] command doesn't work with polymorphic universes. *)
  Context {G : Group@{Set}} (x y : G).

  (** Without opening any scopes, the notation [x * y] will default to the one in [type_scope] which is the product type. In this case it will fail since Coq is expecting a type argument rather than [x : G]. *)
  Fail Type (x * y : G).
  
  (** [x^] will be interpreted as path inversion, therefore Coq will complain about its type. *)
  Fail Type (x^ * y : G).

  (** Opening [mc_scope] will mean notations such as [^] gain meaning whilst [_ * _] will specifically mean a multiplication. This means that for rings this notation has meaning, but for groups the meaning is still missing. *)
  Local Open Scope mc_scope.

  (** We fail saying that no [Mult] instance was found for [G] as expected. *)
  Fail Type (x * y : G).
  Fail Type (x^ * y : G).

  (** Finally, we can open [mc_mult_scope] which will mean [x * y] is [sg_op x y]. *)
  Local Open Scope mc_mult_scope.

  (** This gets correctly interpreted as the group operation. *)
  Succeed Type (x * y : G).
  (** So does the group inverse. *)
  Succeed Type (x^ * y : G).

End Groups.

Section AbGroups.

  Context {A : AbGroup@{Set}} (x y : A).

  (** Working with abelian groups can be confusing if the correct scopes are not open. We document the correct usage here. *)
  
  (** Similar to [*], without any scopes open, the following expression fails since Coq interprets it as the sum type. *)
  Fail Type (x + y : A).

  (** The [- _] notation doesn't have any meaning when the correct scope is not open. *)
  Fail Type (-x : A).

  (** Nor does the subtraction notation. *)
  Fail Type (x - y : A).

  (** Opening [mc_scope] will mean that:
    - [+] becomes the operation of a [Plus].
    - [- x] becomes a [Negate] operation.
    - [x - y] is interpreted as [x + (- y)] for a [Negate] and [Plus]. *)
  Local Open Scope mc_scope.

  (** Notably, even though these instances exist for [Ring]s, they do not in general for abelian groups as we treat those as groups with commutativity rather than a separate operation. This allows us to use group lemmas without deforming abelian group expressions. *)
  
  (** These fail due to a lack of [Plus]. *)
  Fail Type (x + y : A).
  Fail Type (x - y : A).

  (** However note that this does not fail since [Negation] is inferrable from [Inverse]. *)
  Succeed Type (-x : A).

  (** Opening [mc_add_scope] will make writing expressions of abelian groups possible. *)
  Local Open Scope mc_add_scope.

  Succeed Type (x + y : A).
  Succeed Type (-x : A).
  Succeed Type (-x + y : A).
  Succeed Type (x - y : A).
  
  Local Close Scope mc_add_scope.
  
  (** We can also work with the abelian group with a multiplicative notation. As we would for any group. *)
  Local Open Scope mc_mult_scope.
  
  Succeed Type (x * y : A).
  Succeed Type (-x : A).
  Succeed Type (x^ : A).
  Succeed Type (x^ * -y : A).
  
  (** This can get confusing if we further allow for additive notations to also be shown. *)
  
  Local Open Scope mc_add_scope.

  Succeed Type (-x * y + x^).
  Succeed Type (-x^ + --x^).

End AbGroups.
