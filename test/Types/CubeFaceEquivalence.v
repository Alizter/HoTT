From HoTT Require Import Basics Types.Paths.

Local Open Scope path_scope.

(** Reproduce the proposed composite independently of the library specialization. Its forward term must be the existing pasting, definitionally. *)
Section CubeFaceEquivalence.
  Universe u.
  Context {T : Type@{u}} {x0 x1 x2 x3 y0 y1 y2 y3 : T}
    {p0 : x0 = y0} {p1 : x1 = y1} {p2 : x2 = y2} {p3 : x3 = y3}
    {u0 : x0 = x1} {u1 : y0 = y1} {v0 : x2 = x3} {v1 : y2 = y3}
    {h0 : x0 = x2} {h1 : y0 = y2} {k0 : x1 = x3} {k1 : y1 = y3}
    (nu : p0 @ u1 = u0 @ p1) (nv : p2 @ v1 = v0 @ p3)
    (nh : p0 @ h1 = h0 @ p2) (nk : p1 @ k1 = k0 @ p3).

  Let L := concat_natural p0 p1 p3 u0 u1 k0 k1 nu nk.
  Let R := concat_natural p0 p2 p3 h0 h1 v0 v1 nh nv.
  Let proposed := equiv_cancelL p0 (u1 @ k1) (h1 @ v1)
    oE equiv_concat_lr L R^
    oE equiv_whiskerR (u0 @ k0) (h0 @ v0) p3.
  Let E := equiv_naturality_square_filler nu nv nh nk.

  Example proposed_forward (s : u0 @ k0 = h0 @ v0)
    : proposed s = naturality_square_filler nu nv nh nk s := idpath.

  Example equiv_naturality_square_filler_beta (s : u0 @ k0 = h0 @ v0)
    : E s = naturality_square_filler nu nv nh nk s := idpath.

  Example face_roundtrip (s : u0 @ k0 = h0 @ v0)
    : E^-1 (naturality_square_filler nu nv nh nk s) = s
    := eissect E s.

  Example opposite_face_roundtrip (s : u1 @ k1 = h1 @ v1)
    : naturality_square_filler nu nv nh nk (E^-1 s) = s
    := eisretr E s.

  Example cube_roundtrip {s t : u0 @ k0 = h0 @ v0} (q : s = t)
    : (equiv_ap E s t)^-1 (ap (naturality_square_filler nu nv nh nk) q) = q
    := eissect (equiv_ap E s t) q.

  Example opposite_cube_roundtrip {s t : u0 @ k0 = h0 @ v0}
    (q : E s = E t)
    : ap (naturality_square_filler nu nv nh nk) ((equiv_ap E s t)^-1 q) = q
    := eisretr (equiv_ap E s t) q.
End CubeFaceEquivalence.

(** All edge and mixed beta witnesses are arbitrary, and source and target universes remain independent. *)
Section TransportCubeEquivalence.
  Universes i j.
  Context {A : Type@{i}} {B : Type@{j}} {f0 f1 g0 g1 : A -> B}
    (u : f0 == f1) (v : g0 == g1) (h : f0 == g0) (k : f1 == g1)
    {x y : A} (p : x = y)
    {fh0 : f0 x = f0 y} {fh1 : f1 x = f1 y}
    {fv0 : f0 x = f1 x} {fv1 : f0 y = f1 y}
    {gh0 : g0 x = g0 y} {gh1 : g1 x = g1 y}
    {gv0 : g0 x = g1 x} {gv1 : g0 y = g1 y}
    (bfh0 : ap f0 p = fh0) (bfh1 : ap f1 p = fh1)
    (bfv0 : u x = fv0) (bfv1 : u y = fv1)
    (bgh0 : ap g0 p = gh0) (bgh1 : ap g1 p = gh1)
    (bgv0 : v x = gv0) (bgv1 : v y = gv1)
    (cf : fh0 @ fv1 = fv0 @ fh1)
    (cg : gh0 @ gv1 = gv0 @ gh1)
    (eh0 : fh0 @ h y = h x @ gh0)
    (eh1 : fh1 @ k y = k x @ gh1)
    (ev0 : fv0 @ k x = h x @ gv0)
    (ev1 : fv1 @ k y = h y @ gv1)
    (bf : concat_Ap u p @ (bfv0 @@ 1)
      = (1 @@ bfv1) @ naturality_change bfh0 bfh1 cf)
    (bg : concat_Ap v p @ (bgv0 @@ 1)
      = (1 @@ bgv1) @ naturality_change bgh0 bgh1 cg)
    (bh : concat_Ap h p = naturality_change bfh0 bgh0 eh0)
    (bk : concat_Ap k p = naturality_change bfh1 bgh1 eh1).

  Let Input :=
    concat_natural fh0 fh1 gh1 fv0 fv1 (k x) (k y) cf eh1 @ (ev0 @@ 1)
      = (1 @@ ev1) @ concat_natural fh0 gh0 gh1
          (h x) (h y) gv0 gv1 eh0 cg.
  Let convert := transport_naturality_square_beta@{i j} u v h k p
    bfh0 bfh1 bfv0 bfv1 bgh0 bgh1 bgv0 bgv1
    cf cg eh0 eh1 ev0 ev1 bf bg bh bk.
  Let E := Build_Equiv _ _ convert
    (isequiv_transport_naturality_square_beta@{i j} u v h k p
      bfh0 bfh1 bfv0 bfv1 bgh0 bgh1 bgv0 bgv1
      cf cg eh0 eh1 ev0 ev1 bf bg bh bk).

  Example transport_conversion_forward (c : Input)
    : E c = convert c := idpath.

  Example transport_conversion_roundtrip (c : Input)
    : E^-1 (convert c) = c := eissect E c.

  Example dependent_cube_roundtrip
    (c : transport (fun z => u z @ k z = h z @ v z) p
      (naturality_change bfv0 bgv0 ev0)
      = naturality_change bfv1 bgv1 ev1)
    : convert (E^-1 c) = c := eisretr E c.

  Example transport_comparison_roundtrip {c d : Input} (q : c = d)
    : (equiv_ap E c d)^-1 (ap convert q) = q
    := eissect (equiv_ap E c d) q.
End TransportCubeEquivalence.
