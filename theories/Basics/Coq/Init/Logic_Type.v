(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This module defines type constructors for types in [Type]
    ([Datatypes.v] and [Logic.v] defined them for types in [Set]) *)

Set Implicit Arguments.

Require Import Coq.Init.Datatypes.
Local Open Scope identity_scope.
Require Export Coq.Init.Logic.

(** Negation of a type in [Type] *)

Definition notT (A:Type) := A -> False.


