From HoTT Require Import Basics Types.Paths.

Local Open Scope path_scope.

(** The source of transport and the target path type may live in independent universes. No extensionality hypothesis is present. *)
Section NaturalityUniverses.
  Universe u v.
  Context {A : Type@{u}} {B : Type@{v}}.

  Check (@equiv_naturality_transport2@{u v} A B).
  Check (@transport_translation_comparison@{u v} A B).
  Check (@transport_naturality_square@{u v} A B).
  Check (@transport_naturality_square_beta@{u v} A B).
  Check (@adjusted_naturality@{u v} A B).
  Check (@adjusted_naturality_homotopic@{u v} A B).
  Check (@transport_adjusted_naturality@{u u v} A A B).
  Check (@transport_adjusted_naturality_homotopic@{u u v} A A B).
  Check (@transport_rectangle_factor@{u u v} A A).
  Check (@transport_associator_normal_form@{u} A).
End NaturalityUniverses.

Section AssociatorTransport.
  Universe u.
  Context {A : Type@{u}} (mu : A -> A -> A)
    {z0 z1 : A} (p : z0 = z1) (r : A -> A)
    (rho : forall v, mu v z0 = r v)
    (E : forall x y, mu x (r y) = r (mu x y)).

  Example associator_transport_normal_form (x y : A)
    : let eta := fun v => (rho v)^ @ ap (mu v) p in
      transport (fun z => mu (mu x y) z = mu x (mu y z)) p
        ((rho (mu x y) @ (E x y)^) @ ap (mu x) (rho y)^)
      = ((eta (mu x y))^ @ (E x y)^) @ ap (mu x) (eta y)
    := transport_associator_normal_form@{u} mu p r rho E x y.
End AssociatorTransport.

(** Turns allow independent source, intermediate, and target universes. *)
Section TurnUniverses.
  Universe u v w.
  Context {A : Type@{u}} {B : Type@{v}} {C : Type@{w}}.
  Context (f : A -> B) (g : B -> C).

  Check (@turn_filler@{u v} A B f).
  Check (@turn_filler_beta@{u v} A B f).
  Check (@turn_filler_map@{u v w} A B C f g).

  Example turn_unit (x : A)
    : turn_filler f (idpath x) 1 1 1
        (p':=1) (q':=1) (r':=1) (s':=1) 1 1 1 1 1 = 1
    := idpath.
End TurnUniverses.

Section InverseCube.
  Universe u.
  Context {A : Type@{u}}.

  Check (@concat_pV_cube_unit_inverse@{u} A).
  Example inverse_cube_refl (x : A)
    : concat_pV_cube_unit_inverse (idpath x) 1 1 1 1 = 1 := idpath.
End InverseCube.

Section DependentNaturality.
  Universes u v.
  Context {A : Type@{u}} {B : A -> Type@{v}} (f g : forall x, B x).

  Example dependent_naturality_square {x y : A} (p : x = y)
    (h : f x = g x) (k : f y = g y)
    : (ap (transport B p) h @ apD g p = apD f p @ k)
      <~> (transport (fun z => f z = g z) p h = k)
    := dpath_path_FlFr_D@{u v} f g p h k.
  Example dependent_naturality_refl (x : A)
    : dpath_path_FlFr_D f f (idpath x) 1 1 1 = 1 := idpath.
End DependentNaturality.

Section PastingComparison.
  Universe u.
  Context {T : Type@{u}} {x0 x1 y0 y1 z0 z1 v0 v1 : T}
    (p : x0 = y0) (q : x1 = y1) (r : x0 = z0) (s : x1 = z1)
    (a : y0 = v0) (b : y1 = v0) (c : z0 = v1) (d : z1 = v1).

  Example different_centers
    : ((p @ a) @ (q @ b)^ = (r @ c) @ (s @ d)^)
      <~> ((p^ @ r) @ c = a @ ((b^ @ (q^ @ s)) @ d))
    := equiv_pasting_zigzags@{u} p q r s a b c d.
  Example pasting_roundtrip
    (h : (p @ a) @ (q @ b)^ = (r @ c) @ (s @ d)^)
    : different_centers^-1 (different_centers h) = h
    := eissect different_centers h.
End PastingComparison.

Section SquareTransport.
  Universes u v.
  Context {A : Type@{u}} {T : Type@{v}}
    {f0 f1 g0 g1 : A -> T}
    (u : f0 == f1) (v : g0 == g1) (h : f0 == g0) (k : f1 == g1).

  Example five_face_transport {x y : A} (p : x = y)
    (s : u x @ k x = h x @ v x)
    : transport (fun z => u z @ k z = h z @ v z) p s
      = naturality_square_filler (concat_Ap u p) (concat_Ap v p)
          (concat_Ap h p) (concat_Ap k p) s
    := transport_naturality_square_compute@{u v} u v h k p s.
End SquareTransport.

(** Even the constant-boundary case retains an arbitrary 2-loop. *)
Example square_transport_retains_loop {T : Type} (x : T)
  (s : idpath x = idpath x)
  : s = @naturality_square_filler T x x x x x x x x
      1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 s
  := transport_naturality_square_compute
    (fun _ : T => idpath x) (fun _ : T => idpath x)
    (fun _ : T => idpath x) (fun _ : T => idpath x) (idpath x) s.
Example square_transport_refl {T : Type} (x : T)
  : transport_naturality_square_compute
      (fun _ : T => idpath x) (fun _ : T => idpath x)
      (fun _ : T => idpath x) (fun _ : T => idpath x) (idpath x) 1 = 1
  := idpath.

(** Genuinely dependent target fibers and arbitrary selected cubes. *)
Section FiveFaceVariation.
  Universes i j.
  Context {A : Type@{i}} {T : A -> Type@{j}}
    {x0 x1 x2 x3 y0 y1 y2 y3 : forall a, T a}
    {p0 : x0 == y0} {p1 : x1 == y1} {p2 : x2 == y2} {p3 : x3 == y3}
    {u0 : x0 == x1} {u1 : y0 == y1} {v0 : x2 == x3} {v1 : y2 == y3}
    {h0 : x0 == x2} {h1 : y0 == y2} {k0 : x1 == x3} {k1 : y1 == y3}
    (nu : forall a, p0 a @ u1 a = u0 a @ p1 a)
    (nv : forall a, p2 a @ v1 a = v0 a @ p3 a)
    (nh : forall a, p0 a @ h1 a = h0 a @ p2 a)
    (nk : forall a, p1 a @ k1 a = k0 a @ p3 a)
    (s : forall a, u0 a @ k0 a = h0 a @ v0 a).
  Let fill a := naturality_square_filler@{j} (nu a) (nv a) (nh a) (nk a) (s a).

  Example chosen_five_cubes {a b : A} (p : a = b)
    (cu : transport _ p (nu a) = nu b)
    (cv : transport _ p (nv a) = nv b)
    (ch : transport _ p (nh a) = nh b)
    (ck : transport _ p (nk a) = nk b)
    (cs : transport _ p (s a) = s b)
    : transport (fun z => u1 z @ k1 z = h1 z @ v1 z) p (fill a) = fill b
    := naturality_square_filler_glue@{i j} nu nv nh nk s p cu cv ch ck cs.
  Example five_face_application {a b : A} (p : a = b)
    : apD fill p = naturality_square_filler_glue nu nv nh nk s p
        (apD nu p) (apD nv p) (apD nh p) (apD nk p) (apD s p)
    := apD_naturality_square_filler@{i j} nu nv nh nk s p.
  Example five_face_application_refl (a : A)
    : apD_naturality_square_filler nu nv nh nk s (idpath a) = 1 := idpath.
  Example chosen_five_cubes_refl (a : A)
    : naturality_square_filler_glue nu nv nh nk s (idpath a) 1 1 1 1 1 = 1
    := idpath.
End FiveFaceVariation.
