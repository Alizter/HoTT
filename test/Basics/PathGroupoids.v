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

Section FiberwiseComposition.
  Universe u v w.
  Context {A : Type@{u}} {P : A -> Type@{v}} {Q : A -> Type@{w}}
    (f : forall a, P a -> Q a) (s : forall a, P a).

  Example dependent_composition {x y : A} (p : x = y)
    : apD (fun a => f a (s a)) p = ap01D1 f p (apD s p)
    := apD_composeD@{u v w} f s p.

  Example dependent_composition_refl (x : A)
    : apD_composeD f s (idpath x) = idpath := idpath.
End FiberwiseComposition.

Section PathImageInverse.
  Universe u v.
  Context {A : Type@{u}} {B : Type@{v}} (f : A -> B).

  Example image_inverse {x y : A} {a b : B}
    (p : f x = a) (q : f y = b) (h : x = y)
    : (p^ @ (ap f h @ q))^ = q^ @ (ap f h^ @ p)
    := ap_path_image_V@{u v} f p q h.
End PathImageInverse.

Section InverseMixed.
  Universe u.
  Context {A : Type@{u}}.

  Check (@inverse_mixed_beta@{u} A).
  Example inverse_mixed_refl (x : A)
    : inverse_mixed_beta (q':=idpath x)
        (idpath (idpath x)) (idpath (idpath x))
        (idpath (idpath x)) (idpath (idpath x)) 1 1 1 = 1
    := idpath.
End InverseMixed.

Section PointwiseTransport.
  Universes u v w.
  Context {A : Type@{u}} {B : Type@{v}}
    (P : A -> B -> Type@{w}).

  Example pointwise_transport_application {x x' : A} (p : x = x')
    (f : forall y, P x y) {y y' : B} (q : y = y')
    : apD (fun z => transport (fun a => P a z) p (f z)) q
      = transport_transport P p q (f y)
        @ ap (transport (fun a => P a y') p) (apD f q)
    := apD_transport@{u v w} P p f q.
  Example pointwise_transport_refl (x : A) (f : forall y, P x y) (y : B)
    : apD_transport P (idpath x) f (idpath y) = 1 := idpath.
End PointwiseTransport.
