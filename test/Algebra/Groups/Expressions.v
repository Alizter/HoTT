From HoTT Require Import Basics.Overture Algebra.Groups.Group.

Set Universe Minimization ToSet.

(** In this file, we test various aspects of writing group expressions. These kinds of expressions appear throughout the library, but since mathclasses is quite sensitive to subtle changes, we keep this file to document and enforce certain behaviours.

We use the [Type] vernacular command which is like [Check] but doesn't allow for evars. *)

Section Groups.

  (** We used a fixed universe of groups since the [Type] command doesn't work with polymorphic universes. *)
  Context {G : Group@{Set}} (x y : G).

  (** Without opening any scopes, the notation [x * y] will default to the one in [type_scope] which is the product type. In this case it will fail since Coq is expecting a type argument rather than [x : G]. *)
  Fail Type ((x * y) : G).
  
  (** [x^] will be interpreted as path inversion, therefore Coq will complain about its type. *)
  Fail Type (x^ * y : G).

  (** Opening [mc_scope] will mean notations such as [^] gain meaning whilst [_ * _] will specifically mean a multiplication. This means that for rings this notation has meaning, but for groups the meaning is still missing. *)
  Local Open Scope mc_scope.

  (** We fail saying that no [Mult] instance was found for [G] as expected. *)
  Fail Type ((x * y) : G).
  Fail Type (x^ * y : G).

  (** Finally, we can open [mc_mult_scope] which will mean [x * y] is [sg_op x y]. *)
  Local Open Scope mc_mult_scope.

  (** This gets correctly interpreted as the group operation. *)
  Succeed Type ((x * y) : G).
  (** So does the group inverse. *)
  Succeed Type (x^ * y : G).

End Groups.
