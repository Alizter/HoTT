From HoTT Require Import Basics Homotopy.NullHomotopy.

Local Open Scope path_scope.

Section LoopClosing.
  Universe u v.
  Context {X : Type@{u}} {Y : Type@{v}} {f : X -> Y} {y : Y}
    (h : forall x, f x = y).

  (** The loop calculation needs no extensionality and preserves independent source and target universes. *)
  Check (@ap_loop_nullhomotopic@{u v} X Y f y h).

  (** Retain the actual closing witness used by the scalar-loop proofs. *)
  Example specified_closing {x : X} (p : x = x)
    : ap_loop_nullhomotopic h p
      = ap_homotopic h p
        @ (((1 @@ ap_const p y) @@ 1)
          @ ((concat_p1 (h x) @@ 1) @ concat_pV (h x)))
    := idpath.
End LoopClosing.
