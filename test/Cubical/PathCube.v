From HoTT Require Import Basics Types.Paths.
From HoTT Require Import Cubical.DPath Cubical.PathSquare Cubical.PathCube.

Local Open Scope path_scope.

Section RelativeInduction.
  Universes u v.
  Context {A : Type@{u}}
    {x000 x010 x100 x110 x001 x011 x101 x111 : A}
    {p0i0 : x000 = x010} {p1i0 : x100 = x110}
    {pi00 : x000 = x100} {pi10 : x010 = x110}
    {p0i1 : x001 = x011} {p1i1 : x101 = x111}
    {pi01 : x001 = x101} {pi11 : x011 = x111}
    {p00i : x000 = x001} {p01i : x010 = x011}
    {p10i : x100 = x101} {p11i : x110 = x111}
    (s1ii : PathSquare p1i0 p1i1 p10i p11i)
    (sii0 : PathSquare p0i0 p1i0 pi00 pi10)
    (sii1 : PathSquare p0i1 p1i1 pi01 pi11)
    (si0i : PathSquare p00i p10i pi00 pi01)
    (si1i : PathSquare p01i p11i pi10 pi11).

  (** The comparison retains the entire chosen cube, not just its lid. *)
  Example retained_horn_filler
    (s0ii : PathSquare p0i0 p0i1 p00i p01i)
    (c : PathCube s0ii s1ii sii0 sii1 si0i si1i)
    : cu_fill_left s1ii sii0 sii1 si0i si1i = (s0ii; c)
    := @contr _ (cu_fill_left_contr s1ii sii0 sii1 si0i si1i) (s0ii; c).

  Example relative_cube_induction
    (P : forall (s0ii : PathSquare p0i0 p0i1 p00i p01i),
      PathCube s0ii s1ii sii0 sii1 si0i si1i -> Type@{v})
    (fill := cu_fill_left s1ii sii0 sii1 si0i si1i)
    (p : P fill.1 fill.2)
    : forall s0ii c, P s0ii c
    := pathcube_ind_left@{u v} s1ii sii0 sii1 si0i si1i P p.

  Example swapping_cube_axes
    (s0ii : PathSquare p0i0 p0i1 p00i p01i)
    (c : PathCube s0ii s1ii sii0 sii1 si0i si1i)
    : PathCube (sq_tr s0ii) (sq_tr s1ii) si0i si1i sii0 sii1
    := cu_swap_tb_fb@{u} c.

  Example changing_two_faces {T : Type@{v}}
    {l : T -> PathSquare p0i0 p0i1 p00i p01i}
    {r : T -> PathSquare p1i0 p1i1 p10i p11i}
    (c : forall t, PathCube (l t) (r t) sii0 sii1 si0i si1i)
    {x y : T} (p : x = y)
    : cu_GGcccc (ap l p) (ap r p) (c x) = c y
    := cu_GGcccc_natural@{u v} c p.
End RelativeInduction.

Section MappedSquare.
  Universes u v w.
  Context {A : Type@{u}} {B : Type@{v}} {C : Type@{w}}
    (f : C -> A -> B) {c c' : C} (p : c = c')
    {a00 a10 a01 a11 : A}
    {px0 : a00 = a10} {px1 : a01 = a11}
    {p0x : a00 = a01} {p1x : a10 = a11}
    (s : PathSquare px0 px1 p0x p1x).

  Example mapped_square_cube
    : cu_ccGGGG
        (sq_ap011_ap_nat (fun a c => f c a) px0 p)
        (sq_ap011_ap_nat (fun a c => f c a) px1 p)
        (sq_ap011_ap_nat (fun a c => f c a) p0x p)
        (sq_ap011_ap_nat (fun a c => f c a) p1x p)
        ((dp_cu (px0:=fun c => ap (f c) px0)
          (px1:=fun c => ap (f c) px1) (p0x:=fun c => ap (f c) p0x)
          (p1x:=fun c => ap (f c) p1x) (p:=p))^-1
          (apD (fun c => sq_ap (f c) s) p))
      = sq_ap_nat (f c) (f c') (fun a => ap (fun c => f c a) p) s
    := sq_ap_nat_apD@{u v w} f p s.

  Example mapped_filler (h : px0 @ p1x = p0x @ px1)
    : sq_ap (f c) (sq_path h) = sq_path (ap_naturality (f c) h)
    := sq_ap_path@{u v} (f c) h.

  Example transposed_mapped_square
    : sq_tr (sq_ap (f c) s) = sq_ap (f c) (sq_tr s)
    := sq_ap_tr@{u v} (f c) s.

  Example transposed_path_square (h : px0 @ p1x = p0x @ px1)
    : sq_tr (sq_path h) = sq_path h^
    := sq_tr_path@{u} h.

  Example transposed_naturality_cube
    (g : A -> B) (h : f c == g)
    : cu_GGcccc (sq_ap_tr (f c) s) (sq_ap_tr g s)
        (cu_swap_tb_fb (sq_ap_nat (f c) g h s))
      = sq_ap_nat (f c) g h (sq_tr s)
    := sq_ap_nat_tr (f c) g h s.

  Example mapped_path_cube_beta (h : px0 @ p1x = p0x @ px1)
    : ap_naturality_cube f p h
        (apD (fun z => ap_naturality (f z) h) p)
      = sq_ap_nat (f c) (f c') (fun a => ap (fun z => f z a) p)
          (sq_path h)
    := ap_naturality_cube_beta@{u v w} f p h.

  (** An arbitrary chosen 3-path is recovered, not identified with the canonical one. *)
  Example chosen_mapped_path_roundtrip (h : px0 @ p1x = p0x @ px1)
    (q : transport (fun z => ap (f z) px0 @ ap (f z) p1x
        = ap (f z) p0x @ ap (f z) px1) p
      (ap_naturality (f c) h) = ap_naturality (f c') h)
    : (equiv_ap_naturality_cube f p h)^-1
        (equiv_ap_naturality_cube f p h q) = q
    := eissect (equiv_ap_naturality_cube f p h) q.

  Example chosen_mapped_cube_roundtrip (h : px0 @ p1x = p0x @ px1)
    : forall q, equiv_ap_naturality_cube f p h
        ((equiv_ap_naturality_cube f p h)^-1 q) = q
    := eisretr (equiv_ap_naturality_cube f p h).
End MappedSquare.

Section NaturalityOnPaths.
  Universes u v w.
  Context {A : Type@{u}} {B : Type@{v}} {C : Type@{w}}
    {f g : A -> B} (h : f == g) {u0 u1 : C -> A} (k : u0 == u1)
    {c c' : C} (p : c = c')
    (s : ap u0 p @ k c' = k c @ ap u1 p)
    (beta : concat_Ap k p = s).

  Example path_naturality_cube_beta
    : equiv_concat_Ap_cube h k p beta
        (apD (fun z => concat_Ap h (k z)) p)
      = sq_ap_nat f g h (sq_path s)
    := equiv_concat_Ap_cube_beta@{u v w} h k p beta.

  Example chosen_path_naturality_roundtrip
    (q : transport (fun z => ap f (k z) @ h (u1 z)
        = h (u0 z) @ ap g (k z)) p
      (concat_Ap h (k c)) = concat_Ap h (k c'))
    : (equiv_concat_Ap_cube h k p beta)^-1
        (equiv_concat_Ap_cube h k p beta q) = q
    := eissect (equiv_concat_Ap_cube h k p beta) q.

  Example chosen_path_cube_roundtrip
    : forall q, equiv_concat_Ap_cube h k p beta
        ((equiv_concat_Ap_cube h k p beta)^-1 q) = q
    := eisretr (equiv_concat_Ap_cube h k p beta).
End NaturalityOnPaths.

Section CappedNaturality.
  Universes u v.
  Context {A : Type@{u}} {B : Type@{v}} {f g k : A -> B}
    (h : f == g) (l : f == k)
    {a00 a10 a01 a11 : A}
    {px0 : a00 = a10} {px1 : a01 = a11}
    {p0x : a00 = a01} {p1x : a10 = a11}
    (s : PathSquare px0 px1 p0x p1x).

  Example retained_cap_sides
    : sq_concat_h (sq_flip_h (ap_nat h px0)) (ap_nat l px0)
      = ap_nat (fun x => (h x)^ @ l x) px0
    := ap_nat_Vp@{u v} h l px0.
  Example retained_cap_cubes
    : cu_ccGGGG (ap_nat_Vp h l px0) (ap_nat_Vp h l px1)
        (ap_nat_Vp h l p0x) (ap_nat_Vp h l p1x)
        (cu_concat_lr (cu_flip_lr (sq_ap_nat f g h s))
          (sq_ap_nat f k l s))
      = sq_ap_nat g k (fun x => (h x)^ @ l x) s
    := sq_ap_nat_Vp@{u v} h l s.

  (** The source can carry an arbitrary 2-loop; no degeneracy or uniqueness of that filler is assumed. *)
  Example retained_cap_source_loop (a : A) (q : idpath a = idpath a)
    (s0 := sq_path (px0:=idpath a) (px1:=1) (p0x:=1) (p1x:=1) q)
    : cu_ccGGGG (ap_nat_Vp h l (idpath a)) (ap_nat_Vp h l (idpath a))
        (ap_nat_Vp h l (idpath a)) (ap_nat_Vp h l (idpath a))
        (cu_concat_lr (cu_flip_lr (sq_ap_nat f g h s0))
          (sq_ap_nat f k l s0))
      = sq_ap_nat g k (fun x => (h x)^ @ l x) s0
    := sq_ap_nat_Vp h l s0.
End CappedNaturality.

Section Computation.
  Universes u v w.
  Context {A : Type@{u}} {B : Type@{v}} {C : Type@{w}}
    (f : C -> A -> B) (a : A) (c : C).

  Example capped_naturality_square_refl
    : ap_nat_Vp (fun x => idpath (f c x)) (fun x => idpath (f c x))
        (idpath a) = 1 := idpath.
  Example capped_naturality_cube_refl
    : sq_ap_nat_Vp (fun x => idpath (f c x)) (fun x => idpath (f c x))
        (@sq_id A a) = 1 := idpath.

  Example natural_cube_refl
    : sq_ap_nat_apD f (idpath c) (@sq_id A a) = 1 := idpath.
  Example mapped_filler_refl
    : sq_ap_path (f c) (p:=idpath a) (q:=1) (r:=1) (s:=1) 1 = 1
    := idpath.
  Example mapped_path_cube_refl
    : ap_naturality_cube_beta f (idpath c)
        (px0:=idpath a) (px1:=1) (p0x:=1) (p1x:=1) 1 = 1
    := idpath.
  Example path_naturality_cube_refl
    : equiv_concat_Ap_cube_beta (fun x => idpath (f c x))
        (fun _ : C => idpath a) (idpath c) 1 = 1
    := idpath.
End Computation.
