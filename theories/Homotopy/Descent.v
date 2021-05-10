Require Import Basics Types.
Require Import Colimits.Pushout.
Require Import Limits.Pullback.

(** * Homtopy descent *)

(** Currently our wildcat library doesn't have good support for higher cells. Therefore we stick to Type. It may be useful to generalize the statements here for a general wild category (for example for use with pType). *)

(** Prewhiskering homotopies is just regular composition. *)

(** We have to however define postwhiskering. *)
Definition pointwise_paths_postwhisker {A B C} {f g : A -> B} (h : B -> C)
  : f == g -> h o f == h o g
  := fun t x => ap _  (t x).


(** We locally override the wildcat notations so that the results can at least be easily stated. *)
Local Infix "$@R" := pointwise_paths_postwhisker.
Local Infix "$@" := pointwise_paths_concat.


Section Descent.

(** The diagram looks like this: *)
(*
                 A000
               /   |  \
           A100  A010  A001
             |  X     X |
           A110  A101  A011
               \   |  /
                 A111

With all arrows pointing downwards.
*)

  Context
    (** Vertices *)
    (A000 A001 A010 A011 A100 A101 A110 A111 : Type)
    (** Top square maps: *)
    (fx00 : A000 -> A100) (f00x : A000 -> A001)
    (f10x : A100 -> A101) (fx01 : A001 -> A101)
    (** Vertical maps *)
    (f0x0 : A000 -> A010) (f1x0 : A100 -> A110)
    (f0x1 : A001 -> A011) (f1x1 : A101 -> A111)
    (** Bottom square maps *)
    (fx10 : A010 -> A110) (f01x : A010 -> A011)
    (f11x : A110 -> A111) (fx11 : A011 -> A111)
    (** Faces *)
    (Hx0x : f10x o fx00 == fx01 o f00x)
    (Hxx0 : f1x0 o fx00 == fx10 o f0x0) (H0xx : f0x1 o f00x == f01x o f0x0)
    (H1xx : f1x1 o f10x == f11x o f1x0) (Hxx1 : f1x1 o fx01 == fx11 o f0x1)
    (Hx1x : f11x o fx10 == fx11 o f01x)
    (** Cube *)
    (** Note that if we were to generalize this to a wild category, we would need to annotate the compositions inside this cube with associativity terms. Since Type is definitionally associative, we get a much simpler cube. *)
    (cube : (f1x1 $@R Hx0x) $@ (Hxx1 o f00x) $@ (fx11 $@R H0xx)
      == (H1xx o fx00) $@ (f11x $@R Hxx0) $@ (Hx1x o f0x0))
    .

(** TODO: 
  1. Define IsPushout
  2. Define 
  3. 
  *)


  Context
    (H1 : IsPullback Hx01) (H2 : IsPullbak H0xx) (H3 : IsPushout

  Theorem descent
    : IsPullback 



