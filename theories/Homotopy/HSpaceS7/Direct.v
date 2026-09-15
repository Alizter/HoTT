Require Export HoTT.Homotopy.HSpaceS7.Direct.Core.
Require Export HoTT.Homotopy.HSpaceS7.Direct.Normalization.
Require Export HoTT.Homotopy.HSpaceS7.Direct.Comparison.

(** * Direct gluing of the first-left and first-right associators *)

(** Preserve the public module interface while the construction, normalization, and comparison compile separately. *)
Module S7DirectGluing := S7DirectComparison.
