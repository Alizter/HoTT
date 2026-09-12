From HoTT Require Import Basics.Overture Basics.PathGroupoids.

Local Open Scope path_scope.

Section Diagonal.
  Universe u v.
  Context {A : Type@{u}} {B : Type@{v}} (f : A -> A -> B).

  (** The diagonal rule works with independent source and target universes. *)
  Example ap011_diag_universes {x y : A} (p : x = y)
    : ap011 f p p = ap (fun a => f a a) p
    := ap011_diag@{u v} f p.

  Example ap011_diag_idpath (a : A)
    : ap011_diag f (idpath a) = idpath := idpath.

  (** It combines with the existing rule to compute one argument at a time. *)
  Example ap_diagonal_is_ap {x y : A} (p : x = y)
    : ap (fun a => f a a) p
      = ap (fun a => f a x) p @ ap (fun a => f y a) p
    := (ap011_diag f p)^ @ ap011_is_ap f p p.
End Diagonal.

(** Naturality computations allow three independent universes and no function extensionality. *)
Section Naturality.
  Universe u v w.
  Context {A : Type@{u}} {B : Type@{v}} {C : Type@{w}}.

  Example naturality_precompose_universes {f g : B -> C}
    (h : f == g) (k : A -> B) {x y : A} (p : x = y)
    : concat_Ap (h o k) p
      = naturality_change (ap_compose k f p) (ap_compose k g p)
          (concat_Ap h (ap k p))
    := concat_Ap_precompose@{u v w} h k p.

  Example naturality_postcompose_universes {f g : A -> B}
    (h : f == g) (k : B -> C) {x y : A} (p : x = y)
    : concat_Ap (fun z => ap k (h z)) p
      = naturality_change (ap_compose f k p) (ap_compose g k p)
          (ap_naturality k (concat_Ap h p))
    := concat_Ap_postcompose@{u v w} h k p.
  Example naturality_inverse_universes {f g : A -> B}
    (h : f == g) {x y : A} (p : x = y)
    : concat_Ap (fun z => (h z)^) p
      = (inverse_natural (ap f p) (ap g p) (concat_Ap h p))^
    := concat_Ap_inverse@{u v} h p.

  Example naturality_refl_universes (f : A -> B) {x y : A} (p : x = y)
    : concat_Ap (fun z => idpath (f z)) p
      = concat_p1 (ap f p) @ (concat_1p (ap f p))^
    := concat_Ap_refl@{u v} f p.
End Naturality.
