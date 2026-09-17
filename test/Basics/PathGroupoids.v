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

  Example application_square_transpose (f : A -> B -> C)
    {a a' : A} (p : a = a') {b b' : B} (q : b = b')
    : concat_Ap (fun a => ap (f a) q) p
      = (concat_Ap (fun b => ap (fun a => f a b) p) q)^
    := concat_Ap_ap@{u v w} f p q.
  Example application_square_transpose_refl (f : A -> B -> C) (a : A) (b : B)
    : concat_Ap_ap f (idpath a) (idpath b) = 1 := idpath.

  Example naturality_on_composite_path {f g : A -> B} (h : f == g)
    {x y z : A} (p : x = y) (q : y = z)
    : concat_Ap h (p @ q)
      = naturality_change (ap_pp f p q) (ap_pp g p q)
        (concat_pp_p (ap f p) (ap f q) (h z)
          @ whiskerL (ap f p) (concat_Ap h q)
          @ concat_p_pp (ap f p) (h y) (ap g q)
          @ whiskerR (concat_Ap h p) (ap g q)
          @ concat_pp_p (h x) (ap g p) (ap g q))
    := concat_Ap_pp@{u v} h p q.

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

Section FiberwiseBinaryComposition.
  Universes u v w z.
  Context {A : Type@{u}} {P : A -> Type@{v}}
    {Q : A -> Type@{w}} {R : A -> Type@{z}}
    (f : forall a, P a -> Q a -> R a).

  Example fiberwise_binary_paths {a b : A} (p : a = b)
    {x : P a} {x' : P b} {y : Q a} {y' : Q b}
    (q : transport P p x = x') (r : transport Q p y = y')
    : transport R p (f a x y) = f b x' y'
    := ap01D11@{u v w z} f p q r.
  Example fiberwise_binary_application
    (s : forall a, P a) (t : forall a, Q a) {a b : A} (p : a = b)
    : apD (fun a => f a (s a) (t a)) p
      = ap01D11 f p (apD s p) (apD t p)
    := apD_composeD2@{u v w z} f s t p.
  Example fiberwise_binary_refl
    (s : forall a, P a) (t : forall a, Q a) (a : A)
    : apD_composeD2 f s t (idpath a) = 1 := idpath.
End FiberwiseBinaryComposition.

Section CommonCenter.
  Universe u.
  Context {A : Type@{u}}.
  Example changing_zigzag_center {x y z w : A}
    (p : x = z) (q : y = z) (r : z = w)
    : (p @ r) @ (q @ r)^ = p @ q^
    := concat_pV_pp@{u} p q r.
  Example changing_zigzag_center_refl (x : A)
    : concat_pV_pp (idpath x) 1 1 = 1 := idpath.
End CommonCenter.

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

(** The zigzag-square computation permits arbitrary fibers, independent universes, and independently chosen endpoint adjustments. *)
Section AdjustedDependentSquare.
  Universes i j.
  Context {A : Type@{i}} {P : A -> Type@{j}} (f : forall x, P x).
  Context {x y z w : A}
    (p : x = z) (q : y = z) (r : x = w) (s : y = w)
    (h : p @ q^ = r @ s^) {u : P x} {v : P y}
    (cu : u = f x) (cv : v = f y)
    {fp : transport P p u = f z} {fq : transport P q v = f z}
    {fr : transport P r u = f w} {fs : transport P s v = f w}
    (bp : ap (transport P p) cu @ apD f p = fp)
    (bq : ap (transport P q) cv @ apD f q = fq)
    (br : ap (transport P r) cu @ apD f r = fr)
    (bs : ap (transport P s) cv @ apD f s = fs).

  Example specified_endpoint_square
    : (transport_pp P p q^ u @ ap (transport P q^) (fp @ fq^))
        @ transport_Vp P q v
      = transport2 P h u
        @ ((transport_pp P r s^ u @ ap (transport P s^) (fr @ fs^))
          @ transport_Vp P s v)
    := apD02_pV_beta@{i j} f p q r s h cu cv bp bq br bs.

  Example specified_endpoint_square_refl (a : A)
    : apD02_pV_beta f (idpath a) 1 1 1 1
        (idpath (f a)) (idpath (f a)) 1 1 1 1 = 1
    := idpath.
End AdjustedDependentSquare.
