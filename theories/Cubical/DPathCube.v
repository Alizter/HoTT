Require Import Basics.
Require Import Cubical.DPath.
Require Import Cubical.PathSquare.
Require Import Cubical.DPathSquare.
Require Import Cubical.PathCube.

Declare Scope dcube_scope.
Delimit Scope dcube_scope with dcube.

(* In this file we define a dependent cube *)

(* Dependent cubes *)
Definition DPathCube {A} (B : A -> Type)
  {x000 x010 x100 x110 x001 x011 x101 x111 : A}
  {p0i0 : x000 = x010} {p1i0 : x100 = x110}
  {pi00 : x000 = x100} {pi10 : x010 = x110}
  {p0i1 : x001 = x011} {p1i1 : x101 = x111}
  {pi01 : x001 = x101} {pi11 : x011 = x111}
  {p00i : x000 = x001} {p01i : x010 = x011}
  {p10i : x100 = x101} {p11i : x110 = x111}
  {s0ii : PathSquare p0i0 p0i1 p00i p01i}
  {s1ii : PathSquare p1i0 p1i1 p10i p11i}
  {sii0 : PathSquare p0i0 p1i0 pi00 pi10}
  {sii1 : PathSquare p0i1 p1i1 pi01 pi11}
  {si0i : PathSquare p00i p10i pi00 pi01}
  {si1i : PathSquare p01i p11i pi10 pi11}
  (cube : PathCube s0ii s1ii sii0 sii1 si0i si1i)
  {b000 : B x000} {b010 : B x010} {b100 : B x100} {b110 : B x110}
  {b001 : B x001} {b011 : B x011} {b101 : B x101} {b111 : B x111 }
  {bp0i0 : DPath B p0i0 b000 b010} {bp1i0 : DPath B p1i0 b100 b110}
  {bpi00 : DPath B pi00 b000 b100} {bpi10 : DPath B pi10 b010 b110}
  {bp0i1 : DPath B p0i1 b001 b011} {bp1i1 : DPath B p1i1 b101 b111}
  {bpi01 : DPath B pi01 b001 b101} {bpi11 : DPath B pi11 b011 b111}
  {bp00i : DPath B p00i b000 b001} {bp01i : DPath B p01i b010 b011}
  {bp10i : DPath B p10i b100 b101} {bp11i : DPath B p11i b110 b111}
  (bs0ii : DPathSquare B s0ii bp0i0 bp0i1 bp00i bp01i)
  (bs1ii : DPathSquare B s1ii bp1i0 bp1i1 bp10i bp11i)
  (bsii0 : DPathSquare B sii0 bp0i0 bp1i0 bpi00 bpi10)
  (bsii1 : DPathSquare B sii1 bp0i1 bp1i1 bpi01 bpi11)
  (bsi0i : DPathSquare B si0i bp00i bp10i bpi00 bpi01)
  (bsi1i : DPathSquare B si1i bp01i bp11i bpi10 bpi11) : Type.
Proof.
  destruct cube.
  exact (PathCube bs0ii bs1ii bsii0 bsii1 bsi0i bsi1i).
Defined.

Definition equiv_dc_const' {A B : Type}
  {x000 x010 x100 x110 x001 x011 x101 x111 : A}
  {p0i0 : x000 = x010} {p1i0 : x100 = x110}
  {pi00 : x000 = x100} {pi10 : x010 = x110}
  {p0i1 : x001 = x011} {p1i1 : x101 = x111}
  {pi01 : x001 = x101} {pi11 : x011 = x111}
  {p00i : x000 = x001} {p01i : x010 = x011}
  {p10i : x100 = x101} {p11i : x110 = x111}
  {s0ii : PathSquare p0i0 p0i1 p00i p01i}
  {s1ii : PathSquare p1i0 p1i1 p10i p11i}
  {sii0 : PathSquare p0i0 p1i0 pi00 pi10}
  {sii1 : PathSquare p0i1 p1i1 pi01 pi11}
  {si0i : PathSquare p00i p10i pi00 pi01}
  {si1i : PathSquare p01i p11i pi10 pi11}
  {cube : PathCube s0ii s1ii sii0 sii1 si0i si1i}
  {b000 b010 b100 b110 b001 b011 b101 b111 : B}
  {bp0i0 : DPath (fun _ => B) p0i0 b000 b010}
  {bp1i0 : DPath (fun _ => B) p1i0 b100 b110}
  {bpi00 : DPath (fun _ => B) pi00 b000 b100}
  {bpi10 : DPath (fun _ => B) pi10 b010 b110}
  {bp0i1 : DPath (fun _ => B) p0i1 b001 b011}
  {bp1i1 : DPath (fun _ => B) p1i1 b101 b111}
  {bpi01 : DPath (fun _ => B) pi01 b001 b101}
  {bpi11 : DPath (fun _ => B) pi11 b011 b111}
  {bp00i : DPath (fun _ => B) p00i b000 b001}
  {bp01i : DPath (fun _ => B) p01i b010 b011}
  {bp10i : DPath (fun _ => B) p10i b100 b101}
  {bp11i : DPath (fun _ => B) p11i b110 b111}
  {bs0ii : DPathSquare (fun _ => B) s0ii bp0i0 bp0i1 bp00i bp01i}
  {bs1ii : DPathSquare (fun _ => B) s1ii bp1i0 bp1i1 bp10i bp11i}
  {bsii0 : DPathSquare (fun _ => B) sii0 bp0i0 bp1i0 bpi00 bpi10}
  {bsii1 : DPathSquare (fun _ => B) sii1 bp0i1 bp1i1 bpi01 bpi11}
  {bsi0i : DPathSquare (fun _ => B) si0i bp00i bp10i bpi00 bpi01}
  {bsi1i : DPathSquare (fun _ => B) si1i bp01i bp11i bpi10 bpi11}
  : PathCube
    (ds_const'^-1 bs0ii) (ds_const'^-1 bs1ii) (ds_const'^-1 bsii0)
    (ds_const'^-1 bsii1) (ds_const'^-1 bsi0i) (ds_const'^-1 bsi1i)
    <~> DPathCube (fun _ => B) cube bs0ii bs1ii bsii0 bsii1 bsi0i bsi1i.
Proof.
  by destruct cube.
Defined.

Notation dc_const' := equiv_dc_const'.

Definition equiv_dc_const {A B : Type}
  {x000 x010 x100 x110 x001 x011 x101 x111 : A}
  {p0i0 : x000 = x010} {p1i0 : x100 = x110}
  {pi00 : x000 = x100} {pi10 : x010 = x110}
  {p0i1 : x001 = x011} {p1i1 : x101 = x111}
  {pi01 : x001 = x101} {pi11 : x011 = x111}
  {p00i : x000 = x001} {p01i : x010 = x011}
  {p10i : x100 = x101} {p11i : x110 = x111}
  {s0ii : PathSquare p0i0 p0i1 p00i p01i}
  {s1ii : PathSquare p1i0 p1i1 p10i p11i}
  {sii0 : PathSquare p0i0 p1i0 pi00 pi10}
  {sii1 : PathSquare p0i1 p1i1 pi01 pi11}
  {si0i : PathSquare p00i p10i pi00 pi01}
  {si1i : PathSquare p01i p11i pi10 pi11}
  {cube : PathCube s0ii s1ii sii0 sii1 si0i si1i}
  {b000 b010 b100 b110 b001 b011 b101 b111 : B}
  {bp0i0 : b000 = b010} {bp1i0 : b100 = b110}
  {bpi00 : b000 = b100} {bpi10 : b010 = b110}
  {bp0i1 : b001 = b011} {bp1i1 : b101 = b111}
  {bpi01 : b001 = b101} {bpi11 : b011 = b111}
  {bp00i : b000 = b001} {bp01i : b010 = b011}
  {bp10i : b100 = b101} {bp11i : b110 = b111}
  {bs0ii : PathSquare bp0i0 bp0i1 bp00i bp01i}
  {bs1ii : PathSquare bp1i0 bp1i1 bp10i bp11i}
  {bsii0 : PathSquare bp0i0 bp1i0 bpi00 bpi10}
  {bsii1 : PathSquare bp0i1 bp1i1 bpi01 bpi11}
  {bsi0i : PathSquare bp00i bp10i bpi00 bpi01}
  {bsi1i : PathSquare bp01i bp11i bpi10 bpi11}
  : PathCube bs0ii bs1ii bsii0 bsii1 bsi0i bsi1i
  <~> DPathCube (fun _ => B) cube (ds_const bs0ii) (ds_const bs1ii) (ds_const bsii0)
     (ds_const bsii1) (ds_const bsi0i) (ds_const bsi1i).
Proof.
  by destruct cube.
Defined.

Notation dc_const := equiv_dc_const.

(** Dependent Kan fillers *)

Section Kan.
  Context {A} {x000 x010 x100 x110 x001 x011 x101 x111 : A}
    {p0i0 : x000 = x010} {p1i0 : x100 = x110} {pi00 : x000 = x100}
    {pi10 : x010 = x110} {p0i1 : x001 = x011} {p1i1 : x101 = x111}
    {pi01 : x001 = x101} {pi11 : x011 = x111} {p00i : x000 = x001}
    {p01i : x010 = x011} {p10i : x100 = x101} {p11i : x110 = x111}
    {s1ii : PathSquare p1i0 p1i1 p10i p11i} {s0ii : PathSquare p0i0 p0i1 p00i p01i}
    {sii0 : PathSquare p0i0 p1i0 pi00 pi10} {sii1 : PathSquare p0i1 p1i1 pi01 pi11}
    {si0i : PathSquare p00i p10i pi00 pi01} {si1i : PathSquare p01i p11i pi10 pi11}
    (c : PathCube s0ii s1ii sii0 sii1 si0i si1i)
    {P : A -> Type} {y000 y010 y100 y110 y001 y011 y101 y111}
    {q0i0 : DPath P p0i0 y000 y010} {q1i0 : DPath P p1i0 y100 y110} {qi00 : DPath P pi00 y000 y100}
    {qi10 : DPath P pi10 y010 y110} {q0i1 : DPath P p0i1 y001 y011} {q1i1 : DPath P p1i1 y101 y111}
    {qi01 : DPath P pi01 y001 y101} {qi11 : DPath P pi11 y011 y111} {q00i : DPath P p00i y000 y001}
    {q01i : DPath P p01i y010 y011} {q10i : DPath P p10i y100 y101} {q11i : DPath P p11i y110 y111}.

  Definition dc_fill_left
    (t1ii : DPathSquare P s1ii q1i0 q1i1 q10i q11i)
    (tii0 : DPathSquare P sii0 q0i0 q1i0 qi00 qi10) (tii1 : DPathSquare P sii1 q0i1 q1i1 qi01 qi11)
    (ti0i : DPathSquare P si0i q00i q10i qi00 qi01) (ti1i : DPathSquare P si1i q01i q11i qi10 qi11)
    : {t0ii : DPathSquare P s0ii q0i0 q0i1 q00i q01i & DPathCube P c t0ii t1ii tii0 tii1 ti0i ti1i}.
  Proof.
    destruct c.
    apply cu_fill_left.
  Defined.

  Definition dc_fill_right
    (t0ii : DPathSquare P s0ii q0i0 q0i1 q00i q01i)
    (tii0 : DPathSquare P sii0 q0i0 q1i0 qi00 qi10) (tii1 : DPathSquare P sii1 q0i1 q1i1 qi01 qi11)
    (ti0i : DPathSquare P si0i q00i q10i qi00 qi01) (ti1i : DPathSquare P si1i q01i q11i qi10 qi11)
    : {t1ii : DPathSquare P s1ii q1i0 q1i1 q10i q11i & DPathCube P c t0ii t1ii tii0 tii1 ti0i ti1i}.
  Proof.
    destruct c.
    apply cu_fill_right.
  Defined.

  Definition dc_fill_top
    (t0ii : DPathSquare P s0ii q0i0 q0i1 q00i q01i) (t1ii : DPathSquare P s1ii q1i0 q1i1 q10i q11i)
                                                    (tii1 : DPathSquare P sii1 q0i1 q1i1 qi01 qi11)
    (ti0i : DPathSquare P si0i q00i q10i qi00 qi01) (ti1i : DPathSquare P si1i q01i q11i qi10 qi11)
    : {tii0 : DPathSquare P sii0 q0i0 q1i0 qi00 qi10 & DPathCube P c t0ii t1ii tii0 tii1 ti0i ti1i}.
  Proof.
    destruct c.
    apply cu_fill_top.
  Defined.

  Definition dc_fill_bottom
    (t0ii : DPathSquare P s0ii q0i0 q0i1 q00i q01i) (t1ii : DPathSquare P s1ii q1i0 q1i1 q10i q11i)
    (tii0 : DPathSquare P sii0 q0i0 q1i0 qi00 qi10)
    (ti0i : DPathSquare P si0i q00i q10i qi00 qi01) (ti1i : DPathSquare P si1i q01i q11i qi10 qi11)
    : {tii1 : DPathSquare P sii1 q0i1 q1i1 qi01 qi11 & DPathCube P c t0ii t1ii tii0 tii1 ti0i ti1i}.
  Proof.
    destruct c.
    apply cu_fill_bottom.
  Defined.

  Definition dc_fill_front
    (t0ii : DPathSquare P s0ii q0i0 q0i1 q00i q01i) (t1ii : DPathSquare P s1ii q1i0 q1i1 q10i q11i)
    (tii0 : DPathSquare P sii0 q0i0 q1i0 qi00 qi10) (tii1 : DPathSquare P sii1 q0i1 q1i1 qi01 qi11)
                                                    (ti1i : DPathSquare P si1i q01i q11i qi10 qi11)
    : {ti0i : DPathSquare P si0i q00i q10i qi00 qi01 & DPathCube P c t0ii t1ii tii0 tii1 ti0i ti1i}.
  Proof.
    destruct c.
    apply cu_fill_front.
  Defined.

  Definition dc_fill_back
    (t0ii : DPathSquare P s0ii q0i0 q0i1 q00i q01i) (t1ii : DPathSquare P s1ii q1i0 q1i1 q10i q11i)
    (tii0 : DPathSquare P sii0 q0i0 q1i0 qi00 qi10) (tii1 : DPathSquare P sii1 q0i1 q1i1 qi01 qi11)
    (ti0i : DPathSquare P si0i q00i q10i qi00 qi01)
    : {ti1i : DPathSquare P si1i q01i q11i qi10 qi11 & DPathCube P c t0ii t1ii tii0 tii1 ti0i ti1i}.
  Proof.
    destruct c.
    apply cu_fill_back.
  Defined.

End Kan.

(* Lemmas for rewriting faces of dependent cubes *)
Section DPathCubeRewriting.

  Context {A B} {x000 x010 x100 x110 x001 x011 x101 x111 : A}
    {p0i0 : x000 = x010} {p1i0 : x100 = x110} {pi00 : x000 = x100}
    {pi10 : x010 = x110} {p0i1 : x001 = x011} {p1i1 : x101 = x111}
    {pi01 : x001 = x101} {pi11 : x011 = x111} {p00i : x000 = x001}
    {p01i : x010 = x011} {p10i : x100 = x101} {p11i : x110 = x111}
    {s0ii : PathSquare p0i0 p0i1 p00i p01i} {s1ii : PathSquare p1i0 p1i1 p10i p11i}
    {sii0 : PathSquare p0i0 p1i0 pi00 pi10} {sii1 : PathSquare p0i1 p1i1 pi01 pi11}
    {si0i : PathSquare p00i p10i pi00 pi01} {si1i : PathSquare p01i p11i pi10 pi11}
    {cube : PathCube s0ii s1ii sii0 sii1 si0i si1i}
    {b000 : B x000} {b010 : B x010} {b100 : B x100} {b110 : B x110}
    {b001 : B x001} {b011 : B x011} {b101 : B x101} {b111 : B x111}
    {bp0i0 : DPath B p0i0 b000 b010} {bp1i0 : DPath B p1i0 b100 b110}
    {bpi00 : DPath B pi00 b000 b100} {bpi10 : DPath B pi10 b010 b110}
    {bp0i1 : DPath B p0i1 b001 b011} {bp1i1 : DPath B p1i1 b101 b111}
    {bpi01 : DPath B pi01 b001 b101} {bpi11 : DPath B pi11 b011 b111}
    {bp00i : DPath B p00i b000 b001} {bp01i : DPath B p01i b010 b011}
    {bp10i : DPath B p10i b100 b101} {bp11i : DPath B p11i b110 b111}
    {bs0ii : DPathSquare B s0ii bp0i0 bp0i1 bp00i bp01i}
    {bs1ii : DPathSquare B s1ii bp1i0 bp1i1 bp10i bp11i}
    {bsii0 : DPathSquare B sii0 bp0i0 bp1i0 bpi00 bpi10}
    {bsii1 : DPathSquare B sii1 bp0i1 bp1i1 bpi01 bpi11}
    {bsi0i : DPathSquare B si0i bp00i bp10i bpi00 bpi01}
    {bsi1i : DPathSquare B si1i bp01i bp11i bpi10 bpi11}.

  (* We write the most general version and derive special cases from this *)
  Definition equiv_dc_GGGGGG {bs0ii' bs1ii' bsii0' bsii1' bsi0i' bsi1i'}
    (bt0ii : bs0ii = bs0ii') (bt1ii : bs1ii = bs1ii') (btii0 : bsii0 = bsii0')
    (btii1 : bsii1 = bsii1') (bti0i : bsi0i = bsi0i') (bti1i : bsi1i = bsi1i')
    : DPathCube B cube bs0ii bs1ii bsii0 bsii1 bsi0i bsi1i
    <~> DPathCube B cube bs0ii' bs1ii' bsii0' bsii1' bsi0i' bsi1i'.
  Proof.
    destruct cube.
    by apply equiv_cu_GGGGGG.
  Defined.

  Context {bs0ii' bs1ii' bsii0' bsii1' bsi0i' bsi1i'}
    (bt0ii : bs0ii = bs0ii') (bt1ii : bs1ii = bs1ii') (btii0 : bsii0 = bsii0')
    (btii1 : bsii1 = bsii1') (bti0i : bsi0i = bsi0i') (bti1i : bsi1i = bsi1i').

  Definition equiv_dc_Gccccc := equiv_dc_GGGGGG bt0ii 1 1 1 1 1.
  Definition equiv_dc_cGcccc := equiv_dc_GGGGGG 1 bt1ii 1 1 1 1.
  Definition equiv_dc_ccGccc := equiv_dc_GGGGGG 1 1 btii0 1 1 1.
  Definition equiv_dc_cccGcc := equiv_dc_GGGGGG 1 1 1 btii1 1 1.
  Definition equiv_dc_ccccGc := equiv_dc_GGGGGG 1 1 1 1 bti0i 1.
  Definition equiv_dc_cccccG := equiv_dc_GGGGGG 1 1 1 1 1 bti1i.
  Definition equiv_dc_ccGGGG := equiv_dc_GGGGGG 1 1 btii0 btii1 bti0i bti1i.
  Definition equiv_dc_GGGGcc := equiv_dc_GGGGGG bt0ii bt1ii btii0 btii1 1 1.
  Definition equiv_dc_GGcccc := equiv_dc_GGGGGG bt0ii bt1ii 1 1 1 1.
  Definition equiv_dc_ccGGcc := equiv_dc_GGGGGG 1 1 btii0 btii1 1 1.
  Definition equiv_dc_ccccGG := equiv_dc_GGGGGG 1 1 1 1 bti0i bti1i.

End DPathCubeRewriting.

Notation dc_GGGGGG := equiv_dc_GGGGGG.
Notation dc_Gccccc := equiv_dc_Gccccc.
Notation dc_cGcccc := equiv_dc_cGcccc.
Notation dc_ccGccc := equiv_dc_ccGccc.
Notation dc_cccGcc := equiv_dc_cccGcc.
Notation dc_ccccGc := equiv_dc_ccccGc.
Notation dc_cccccG := equiv_dc_cccccG.
Notation dc_ccGGGG := equiv_dc_ccGGGG.
Notation dc_GGGGcc := equiv_dc_GGGGcc.
Notation dc_GGcccc := equiv_dc_GGcccc.
Notation dc_ccGGcc := equiv_dc_ccGGcc.
Notation dc_ccccGG := equiv_dc_ccccGG.

(** Concatenations of DPathCube's *)
Section DPathCubeConcat.

  Context {A : Type} {B : A -> Type}
    {x000 x010 x100 x110 x001 x011 x101 x111 : A}
    {p0i0 : x000 = x010} {p1i0 : x100 = x110} {pi00 : x000 = x100}
    {pi10 : x010 = x110} {p0i1 : x001 = x011} {p1i1 : x101 = x111}
    {pi01 : x001 = x101} {pi11 : x011 = x111} {p00i : x000 = x001}
    {p01i : x010 = x011} {p10i : x100 = x101} {p11i : x110 = x111}
    {s0ii : PathSquare p0i0 p0i1 p00i p01i} {s1ii : PathSquare p1i0 p1i1 p10i p11i}
    {sii0 : PathSquare p0i0 p1i0 pi00 pi10} {sii1 : PathSquare p0i1 p1i1 pi01 pi11}
    {si0i : PathSquare p00i p10i pi00 pi01} {si1i : PathSquare p01i p11i pi10 pi11}
    {cube : PathCube s0ii s1ii sii0 sii1 si0i si1i}
    {b000 : B x000} {b010 : B x010} {b100 : B x100} {b110 : B x110}
    {b001 : B x001} {b011 : B x011} {b101 : B x101} {b111 : B x111}
    {bp0i0 : DPath B p0i0 b000 b010} {bp1i0 : DPath B p1i0 b100 b110}
    {bpi00 : DPath B pi00 b000 b100} {bpi10 : DPath B pi10 b010 b110}
    {bp0i1 : DPath B p0i1 b001 b011} {bp1i1 : DPath B p1i1 b101 b111}
    {bpi01 : DPath B pi01 b001 b101} {bpi11 : DPath B pi11 b011 b111}
    {bp00i : DPath B p00i b000 b001} {bp01i : DPath B p01i b010 b011}
    {bp10i : DPath B p10i b100 b101} {bp11i : DPath B p11i b110 b111}
    {bs0ii : DPathSquare B s0ii bp0i0 bp0i1 bp00i bp01i}
    {bs1ii : DPathSquare B s1ii bp1i0 bp1i1 bp10i bp11i}
    {bsii0 : DPathSquare B sii0 bp0i0 bp1i0 bpi00 bpi10}
    {bsii1 : DPathSquare B sii1 bp0i1 bp1i1 bpi01 bpi11}
    {bsi0i : DPathSquare B si0i bp00i bp10i bpi00 bpi01}
    {bsi1i : DPathSquare B si1i bp01i bp11i bpi10 bpi11}.

  (** Left-right concatenation *)
  Definition dc_concat_lr
    {x201 x200 x210 x211 : A}
    {pj01 : x101 = x201} {pj11 : x111 = x211} {pj10 : x110 = x210}
    {pj00 : x100 = x200} {p2i1 : x201 = x211} {p2i0 : x200 = x210}
    {p20i : x200 = x201} {p21i : x210 = x211}
    {sji0 : PathSquare p1i0 p2i0 pj00 pj10} {sji1 : PathSquare p1i1 p2i1 pj01 pj11}
    {sj0i : PathSquare p10i p20i pj00 pj01} {sj1i : PathSquare p11i p21i pj10 pj11}
    {s2ii : PathSquare p2i0 p2i1 p20i p21i}
    {cube2 : PathCube s1ii s2ii sji0 sji1 sj0i sj1i}
    {b201 b200 b210 b211}
    {bpj01 : DPath B pj01 b101 b201} {bpj11 : DPath B pj11 b111 b211}
    {bpj10 : DPath B pj10 b110 b210} {bpj00 : DPath B pj00 b100 b200}
    {bp2i1 : DPath B p2i1 b201 b211} {bp2i0 : DPath B p2i0 b200 b210}
    {bp20i : DPath B p20i b200 b201} {bp21i : DPath B p21i b210 b211}
    {bsji0 : DPathSquare B sji0 bp1i0 bp2i0 bpj00 bpj10}
    {bsji1 : DPathSquare B sji1 bp1i1 bp2i1 bpj01 bpj11}
    {bsj0i : DPathSquare B sj0i bp10i bp20i bpj00 bpj01}
    {bsj1i : DPathSquare B sj1i bp11i bp21i bpj10 bpj11}
    {bs2ii : DPathSquare B s2ii bp2i0 bp2i1 bp20i bp21i}
    : DPathCube B cube bs0ii bs1ii bsii0 bsii1 bsi0i bsi1i
    -> DPathCube B cube2 bs1ii bs2ii bsji0 bsji1 bsj0i bsj1i
    -> DPathCube B (cu_concat_lr cube cube2) bs0ii bs2ii
        (ds_concat_h bsii0 bsji0) (ds_concat_h bsii1 bsji1)
        (ds_concat_h bsi0i bsj0i) (ds_concat_h bsi1i bsj1i).
  Proof.
    intros a b.
    destruct cube2.
    destruct b.
    unfold ds_concat_h.
    destruct pi00.
    destruct pi10.
    destruct bpi00.
    destruct bpi10.
    destruct pi01.
    destruct pi11.
    destruct bpi01.
    destruct bpi11.
  Admitted.

End DPathCubeConcat.

(** ds_apD fits into a (degenerate) DPathCube relating it to ds_const applied to sq_ap *)
Definition ds_apD_const_dc {A B : Type} {a00 a10 a01 a11 : A} (f : A -> B) {px0 : a00 = a10} {px1 : a01 = a11} 
  {p0x : a00 = a01} {p1x : a10 = a11} (s : PathSquare px0 px1 p0x p1x)
  : DPathCube _ (cu_refl_lr s) (ds_const (sq_ap f s)) (ds_apD f s)
      (dp_apD_const_ds f px0) (dp_apD_const_ds f px1)
      (dp_apD_const_ds f p0x) (dp_apD_const_ds f p1x).
Proof.
  by destruct s.
Defined.


