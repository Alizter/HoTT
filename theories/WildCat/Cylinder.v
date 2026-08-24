Require Import Basics.Overture Basics.Tactics.
Require Import WildCat.Core WildCat.NatTrans WildCat.Square WildCat.TwoOneCat.

(** * Cylinders between squares *)

(** A cylinder compares two squares with the same horizontal edges.

<<
             f
       x00 ------> x20
        |           |
     u0 |           | v0
        |    s0     |
        v           v
       x02 ------> x22
             g

     p : u0 $== u1,    q : v0 $== v1

             f
       x00 ------> x20
        |           |
     u1 |           | v1
        |    s1     |
        v           v
       x02 ------> x22
             g
>>

    The cylinder is the 3-cell saying that the two evident pastings
    from [v0 $o f] to [g $o u1] agree.  It is a square in the relevant
    hom-category, but the displayed definition in terms of [$@] makes
    its orientation explicit. *)
Definition Cylinder
  {A : Type} `{Is21Cat A}
  {x00 x20 x02 x22 : A}
  {f : x00 $-> x20} {g : x02 $-> x22}
  {u0 u1 : x00 $-> x02} {v0 v1 : x20 $-> x22}
  (p : u0 $== u1) (q : v0 $== v1)
  (s0 : Square u0 v0 f g) (s1 : Square u1 v1 f g)
  : Type
  := Square (q $@R f) (g $@L p) s0 s1.

Section Cylinders.

  Context
    {A : Type} `{Is21Cat A}
    {x00 x20 x02 x22 : A}
    {f : x00 $-> x20} {g : x02 $-> x22}
    {u0 u1 u2 : x00 $-> x02}
    {v0 v1 v2 : x20 $-> x22}
    {p0 : u0 $== u1} {p1 : u1 $== u2}
    {q0 : v0 $== v1} {q1 : v1 $== v2}
    {s0 : Square u0 v0 f g}
    {s1 : Square u1 v1 f g}
    {s2 : Square u2 v2 f g}.

  Definition Build_Cylinder
    (c : s0 $@ (g $@L p0) $== (q0 $@R f) $@ s1)
    : Cylinder p0 q0 s0 s1
    := c.

  Definition gpdhom_cylinder (c : Cylinder p0 q0 s0 s1)
    : s0 $@ (g $@L p0) $== (q0 $@R f) $@ s1
    := c.

  (** A cylinder is a square in the relevant hom-category.  These named
      conversions let clients use that fact without unfolding [Cylinder]. *)
  Definition cylinder_of_square
    (c : Square (q0 $@R f) (g $@L p0) s0 s1)
    : Cylinder p0 q0 s0 s1
    := c.

  Definition square_of_cylinder
    (c : Cylinder p0 q0 s0 s1)
    : Square (q0 $@R f) (g $@L p0) s0 s1
    := c.


  Definition cylinder_refl (s : Square u0 v0 f g)
    : Cylinder (Id u0) (Id v0) s s.
  Proof.
    unfold Cylinder.
    rapply (hconcatL
      (fmap_id (cat_precomp _ f) v0) _).
    rapply (hconcatR _
      (fmap_id (cat_postcomp _ g) u0)).
    apply vrefl.
  Defined.

  Definition cylinder_comp
    (c0 : Cylinder p0 q0 s0 s1)
    (c1 : Cylinder p1 q1 s1 s2)
    : Cylinder (p0 $@ p1) (q0 $@ q1) s0 s2.
  Proof.
    unfold Cylinder in *.
    rapply (hconcatL
      (fmap_comp (cat_precomp _ f) q0 q1) _).
    rapply (hconcatR _
      (fmap_comp (cat_postcomp _ g) p0 p1)).
    exact (vconcat c0 c1).
  Defined.

  (** Changing any face of a cylinder by a 3-cell gives another
      cylinder with the corresponding boundary. *)
  Definition cylinder_rewrite_left
    {p0' : u0 $== u1} (h : p0' $== p0)
    (c : Cylinder p0 q0 s0 s1)
    : Cylinder p0' q0 s0 s1.
  Proof.
    unfold Cylinder in *.
    rapply (hconcatR c).
    exact (fmap2 (cat_postcomp _ g) h).
  Defined.

  Definition cylinder_rewrite_right
    {q0' : v0 $== v1} (h : q0' $== q0)
    (c : Cylinder p0 q0 s0 s1)
    : Cylinder p0 q0' s0 s1.
  Proof.
    unfold Cylinder in *.
    rapply (hconcatL _ c).
    exact (fmap2 (cat_precomp _ f) h).
  Defined.

  Definition cylinder_rewrite_front
    {s0' : Square u0 v0 f g} (h : s0' $== s0)
    (c : Cylinder p0 q0 s0 s1)
    : Cylinder p0 q0 s0' s1.
  Proof.
    exact (vconcatL h c).
  Defined.

  Definition cylinder_rewrite_back
    {s1' : Square u1 v1 f g} (h : s1' $== s1)
    (c : Cylinder p0 q0 s0 s1)
    : Cylinder p0 q0 s0 s1'.
  Proof.
    exact (vconcatR c h).
  Defined.

End Cylinders.

(** A cylinder whose side faces are identities determines a 3-cell between
    its front and back squares. *)
Definition cylinder_id_to_3cell
  {A : Type} `{Is21Cat A}
  {x00 x20 x02 x22 : A}
  {f : x00 $-> x20} {g : x02 $-> x22}
  {u : x00 $-> x02} {v : x20 $-> x22}
  {s t : Square u v f g}
  (c : Cylinder (Id u) (Id v) s t)
  : s $== t.
Proof.
  lhs' exact (cat_idl s)^$.
  lhs' exact ((fmap_id (cat_postcomp _ g) u)^$ $@R s).
  lhs' exact (gpdhom_cylinder c).
  lhs' exact (t $@L fmap_id (cat_precomp _ f) v).
  exact (cat_idr t).
Defined.

(** A 2-cell gives a cylinder between the horizontally degenerate
    squares at its source and target.  This is the horizontal pasting
    of the naturality squares for the two unitors. *)
Definition cylinder_hrefl
  {A : Type} `{Is21Cat A}
  {a b : A} {f g : a $-> b} (p : f $== g)
  : Cylinder p p (hrefl f) (hrefl g).
Proof.
  unfold Cylinder, hrefl.
  exact (hconcat
    (transpose (cat_idr_natural p))
    (hinverse_square_gpd (transpose (cat_idl_natural p)))).
Defined.

Definition cylinder_inverse
  {A : Type} `{Is21Cat A}
  {x00 x20 x02 x22 : A}
  {f : x00 $-> x20} {g : x02 $-> x22}
  {u0 u1 : x00 $-> x02} {v0 v1 : x20 $-> x22}
  {p : u0 $== u1} {q : v0 $== v1}
  {s0 : Square u0 v0 f g} {s1 : Square u1 v1 f g}
  (c : Cylinder p q s0 s1)
  : Cylinder p^$ q^$ s1 s0.
Proof.
  unfold Cylinder in *.
  rapply (hconcatL
    (gpd_1functor_V (cat_precomp _ f) q) _).
  rapply (hconcatR _
    (gpd_1functor_V (cat_postcomp _ g) p)).
  exact (vinverse_square_gpd c).
Defined.

(** A composite of chosen inverses is the inverse of the composite. *)
Local Definition gpd_rev_compose_alt
  {A : Type} `{Is1Gpd A}
  {x y z : A} {f : x $-> y} {g : y $-> z}
  {fi : y $-> x} (pf : fi $== f^$)
  {gi : z $-> y} (pg : gi $== g^$)
  : fi $o gi $== (g $o f)^$.
Proof.
  lhs' exact (pg $@@ pf).
  exact (gpd_rev_pp g f)^$.
Defined.

(** The forward associator is also the inverse of the separately
    stored reverse associator. *)
Local Definition cat_assoc_rev_opp
  {A : Type} `{Is21Cat A}
  {a b c d : A} (f : a $-> b) (g : b $-> c) (h : c $-> d)
  : cat_assoc f g h $== (cat_assoc_opp f g h)^$.
Proof.
  symmetry.
  lhs' exact (gpd_rev2 (cat_assoc_opp_is_rev a b c d f g h)).
  exact (gpd_rev_rev (cat_assoc f g h)).
Defined.

(** The two boundary calculations needed when a transposed square is
    vertically pasted. *)
Local Definition square_vconcat_transpose_first
  {A : Type} `{Is21Cat A}
  {x000 x100 x010 x110 x101 x111 : A}
  {u00 : x000 $-> x010} {u10 : x100 $-> x110}
  {v00 : x000 $-> x100} {v10 : x010 $-> x110}
  {w01 : x100 $-> x101} {w11 : x110 $-> x111}
  {u11 : x101 $-> x111}
  (r0 : Square u00 u10 v00 v10)
  (p1 : Square w01 w11 u10 u11)
  : transpose r0 $@v p1 $==
      cat_assoc v00 w01 u11 $o
        (p1 $@R v00 $o
          (cat_assoc v00 u10 w11 $@ (w11 $@L r0))^$ $o
          cat_assoc u00 v10 w11).
Proof.
  unfold vconcat, transpose.
  lhs' exact (cat_assoc_opp
    (cat_assoc u00 v10 w11)
    (w11 $@L r0^$)
    ((cat_assoc_opp v00 u10 w11 $@ (p1 $@R v00)) $@
      cat_assoc v00 w01 u11)).
  lhs' exact (cat_assoc
    (w11 $@L r0^$)
    ((p1 $@R v00) $o cat_assoc_opp v00 u10 w11)
    (cat_assoc v00 w01 u11)
    $@R cat_assoc u00 v10 w11).
  lhs' exact ((cat_assoc v00 w01 u11 $@L
    cat_assoc
      (w11 $@L r0^$)
      (cat_assoc_opp v00 u10 w11)
      (p1 $@R v00))
    $@R cat_assoc u00 v10 w11).
  lhs' exact ((cat_assoc v00 w01 u11 $@L
    ((p1 $@R v00) $@L
      gpd_rev_compose_alt
        (cat_assoc_opp_is_rev x000 x100 x110 x111
          v00 u10 w11)
        (gpd_1functor_V (cat_postcomp x000 w11) r0)))
    $@R cat_assoc u00 v10 w11).
  exact (cat_assoc
    (cat_assoc u00 v10 w11)
    ((p1 $@R v00) $o
      (cat_assoc v00 u10 w11 $@ (w11 $@L r0))^$)
    (cat_assoc v00 w01 u11)).
Defined.

Local Definition square_vconcat_transpose_second
  {A : Type} `{Is21Cat A}
  {x000 x010 x001 x011 x101 x111 : A}
  {u00 : x000 $-> x010} {u01 : x001 $-> x011}
  {w00 : x000 $-> x001} {w10 : x010 $-> x011}
  {v01 : x001 $-> x101} {v11 : x011 $-> x111}
  {u11 : x101 $-> x111}
  (p0 : Square w00 w10 u00 u01)
  (r1 : Square u01 u11 v01 v11)
  : p0 $@v transpose r1 $==
      ((cat_assoc_opp w00 v01 u11 $@ (r1 $@R w00)) $@
        cat_assoc w00 u01 v11)^$ $o
      (v11 $@L p0) $o cat_assoc u00 w10 v11.
Proof.
  unfold vconcat, transpose.
  lhs' exact (cat_assoc_opp
    (cat_assoc u00 w10 v11)
    (v11 $@L p0)
    ((cat_assoc_opp w00 u01 v11 $@ (r1^$ $@R w00)) $@
      cat_assoc w00 v01 u11)).
  napply (fun h => ((h $@R (v11 $@L p0))
    $@R cat_assoc u00 w10 v11)).
  lhs' exact (cat_assoc_opp
    (cat_assoc_opp w00 u01 v11)
    (r1^$ $@R w00)
    (cat_assoc w00 v01 u11)).
  rapply gpd_rev_compose_alt.
  { rapply gpd_rev_compose_alt.
    { exact (cat_assoc_rev_opp w00 v01 u11). }
    exact (gpd_1functor_V (cat_precomp x111 w00) r1). }
  exact (cat_assoc_opp_is_rev x000 x001 x011 x111
    w00 u01 v11).
Defined.

(** Rotate the axes of the cube presented as a cylinder:

<<
                         q1
                    * --------> *
                   /|           /|
                p0/ |r0      p1/ |r1
                 /  |         /  |
                * --------> *    |
                | q0         |   |
                |    * ------|-->*
                |   /        |  /
                |  /         | /
                | /          |/
                * --------> *
>>

    The original cylinder compares the front and back pastings; the
    result compares the left and right pastings. *)
Definition cylinder_rotate_vconcat
  {A : Type} `{Is21Cat A}
  {x000 x100 x010 x110 x001 x101 x011 x111 : A}
  {u00 : x000 $-> x010} {u10 : x100 $-> x110}
  {u01 : x001 $-> x011} {u11 : x101 $-> x111}
  {v00 : x000 $-> x100} {v10 : x010 $-> x110}
  {v01 : x001 $-> x101} {v11 : x011 $-> x111}
  {w00 : x000 $-> x001} {w10 : x010 $-> x011}
  {w01 : x100 $-> x101} {w11 : x110 $-> x111}
  {r0 : Square u00 u10 v00 v10}
  {r1 : Square u01 u11 v01 v11}
  {p0 : Square w00 w10 u00 u01}
  {p1 : Square w01 w11 u10 u11}
  {q0 : Square w00 w01 v00 v01}
  {q1 : Square w10 w11 v10 v11}
  (c : Cylinder p0 p1 (r0 $@v q1) (q0 $@v r1))
  : Cylinder q0 q1
      (transpose r0 $@v p1)
      (p0 $@v transpose r1).
Proof.
  unfold Cylinder in c |-.
  rapply (hconcatL (f01 :=
    (cat_assoc u00 w10 v11)^$ $o
      ((cat_assoc_opp u00 v10 w11 $@ (q1 $@R u00)) $@
        cat_assoc u00 w10 v11 $o cat_assoc u00 v10 w11)) _).
  { symmetry.
    rapply gpd_moveR_Vh.
    lhs' rapply cat_assoc.
    rapply cat_postwhisker.
    lhs' rapply cat_prewhisker.
    { rapply cat_postwhisker.
      exact (cat_assoc_opp_is_rev x000 x010 x110 x111
        u00 v10 w11). }
    exact (gpd_hV_h
      (q1 $@R u00) (cat_assoc u00 v10 w11)). }
  rapply (hconcatR _
    (gpd_hh_V (u11 $@L q0) (cat_assoc v00 w01 u11))^$).
  rapply (vconcatL (square_vconcat_transpose_first r0 p1)).
  rapply (vconcatR _ (square_vconcat_transpose_second p0 r1)).
  rapply (whiskerBL_gpd (A := x000 $-> x111)
    (cat_assoc u00 w10 v11)).
  rapply (whiskerTR_gpd (A := x000 $-> x111)
    (cat_assoc v00 w01 u11)).
  rapply (whiskerTL (A := x000 $-> x111)
    (f := cat_assoc u00 v10 w11)).
  rapply square_rotate_composites.
  exact c.
Defined.

(** If the first face is already transposed, the double transpose
    introduced by rotation can be removed. *)
Definition cylinder_rotate_vconcat_transpose_front
  {A : Type} `{Is21Cat A}
  {x000 x100 x010 x110 x001 x101 x011 x111 : A}
  {u00 : x000 $-> x010} {u10 : x100 $-> x110}
  {u01 : x001 $-> x011} {u11 : x101 $-> x111}
  {v00 : x000 $-> x100} {v10 : x010 $-> x110}
  {v01 : x001 $-> x101} {v11 : x011 $-> x111}
  {w00 : x000 $-> x001} {w10 : x010 $-> x011}
  {w01 : x100 $-> x101} {w11 : x110 $-> x111}
  {r0 : Square v00 v10 u00 u10}
  {r1 : Square u01 u11 v01 v11}
  {p0 : Square w00 w10 u00 u01}
  {p1 : Square w01 w11 u10 u11}
  {q0 : Square w00 w01 v00 v01}
  {q1 : Square w10 w11 v10 v11}
  (c : Cylinder p0 p1 (transpose r0 $@v q1) (q0 $@v r1))
  : Cylinder q0 q1
      (r0 $@v p1)
      (p0 $@v transpose r1).
Proof.
  rapply cylinder_rewrite_front.
  { unfold vconcat.
    rapply cat_postwhisker.
    rapply cat_prewhisker.
    rapply fmap2.
    exact (gpd_rev_rev r0)^$. }
  exact (cylinder_rotate_vconcat c).
Defined.

(** The corresponding rotation when the second face is already
    transposed. *)
Definition cylinder_rotate_vconcat_transpose_back
  {A : Type} `{Is21Cat A}
  {x000 x100 x010 x110 x001 x101 x011 x111 : A}
  {u00 : x000 $-> x010} {u10 : x100 $-> x110}
  {u01 : x001 $-> x011} {u11 : x101 $-> x111}
  {v00 : x000 $-> x100} {v10 : x010 $-> x110}
  {v01 : x001 $-> x101} {v11 : x011 $-> x111}
  {w00 : x000 $-> x001} {w10 : x010 $-> x011}
  {w01 : x100 $-> x101} {w11 : x110 $-> x111}
  {r0 : Square u00 u10 v00 v10}
  {r1 : Square v01 v11 u01 u11}
  {p0 : Square w00 w10 u00 u01}
  {p1 : Square w01 w11 u10 u11}
  {q0 : Square w00 w01 v00 v01}
  {q1 : Square w10 w11 v10 v11}
  (c : Cylinder p0 p1 (r0 $@v q1) (q0 $@v transpose r1))
  : Cylinder q0 q1
      (transpose r0 $@v p1)
      (p0 $@v r1).
Proof.
  rapply cylinder_rewrite_back.
  { unfold vconcat.
    rapply cat_prewhisker.
    rapply cat_postwhisker.
    rapply cat_prewhisker.
    rapply fmap2.
    exact (gpd_rev_rev r1)^$. }
  exact (cylinder_rotate_vconcat c).
Defined.

(** Naturality of the inverse associator is obtained by reversing and
    transposing the ordinary associator naturality square. *)
Definition cat_assoc_inverse_natural_r {A : Type} `{Is21Cat A}
  {a b c d : A} {f f' : a $-> b} (p : f $== f')
  (g : b $-> c) (h : c $-> d)
  : Square
      (h $@L (g $@L p)) ((h $o g) $@L p)
      (cat_assoc f g h)^$ (cat_assoc f' g h)^$.
Proof.
  exact (transpose (vinverse_square_gpd
    (cat_assoc_natural_r p g h))).
Defined.

Definition cat_assoc_inverse_natural_l {A : Type} `{Is21Cat A}
  {a b c d : A} (f : a $-> b) (g : b $-> c)
  {h h' : c $-> d} (p : h $== h')
  : Square
      (p $@R (g $o f)) ((p $@R g) $@R f)
      (cat_assoc f g h)^$ (cat_assoc f g h')^$.
Proof.
  exact (transpose (vinverse_square_gpd
    (cat_assoc_natural_l f g p))).
Defined.

(** The separately stored reverse associator has the same naturality
    squares, after changing their horizontal faces. *)
Definition cat_assoc_opp_natural_r {A : Type} `{Is21Cat A}
  {a b c d : A} {f f' : a $-> b} (p : f $== f')
  (g : b $-> c) (h : c $-> d)
  : Square
      (h $@L (g $@L p)) ((h $o g) $@L p)
      (cat_assoc_opp f g h) (cat_assoc_opp f' g h).
Proof.
  napply vconcatR.
  { napply vconcatL.
    { exact (cat_assoc_opp_is_rev a b c d f g h). }
    exact (cat_assoc_inverse_natural_r p g h). }
  exact (cat_assoc_opp_is_rev a b c d f' g h).
Defined.

Definition cat_assoc_opp_natural_m {A : Type} `{Is21Cat A}
  {a b c d : A} (f : a $-> b)
  {g g' : b $-> c} (p : g $== g') (h : c $-> d)
  : Square
      (h $@L (p $@R f))
      ((h $@L p) $@R f)
      (cat_assoc_opp f g h)
      (cat_assoc_opp f g' h).
Proof.
  napply vconcatR.
  { napply vconcatL.
    { exact (cat_assoc_opp_is_rev a b c d f g h). }
    exact (transpose (vinverse_square_gpd
      (cat_assoc_natural_m f p h))). }
  exact (cat_assoc_opp_is_rev a b c d f g' h).
Defined.

Definition cat_assoc_opp_natural_l {A : Type} `{Is21Cat A}
  {a b c d : A} (f : a $-> b) (g : b $-> c)
  {h h' : c $-> d} (p : h $== h')
  : Square
      (p $@R (g $o f)) ((p $@R g) $@R f)
      (cat_assoc_opp f g h) (cat_assoc_opp f g h').
Proof.
  napply vconcatR.
  { napply vconcatL.
    { exact (cat_assoc_opp_is_rev a b c d f g h). }
    exact (cat_assoc_inverse_natural_l f g p). }
  exact (cat_assoc_opp_is_rev a b c d f g h').
Defined.

(** Vertical pasting is natural in its upper square. *)
Definition square_vconcat_natural_above
  {A : Type} `{Is21Cat A}
  {x00 x20 x02 x22 x04 x24 : A}
  {f0 : x00 $-> x20} {f1 : x02 $-> x22}
  {f2 : x04 $-> x24}
  {u0 : x00 $-> x02} {v0 : x20 $-> x22}
  {s0 s0' : Square u0 v0 f0 f1}
  (p : s0 $== s0')
  {u1 : x02 $-> x04} {v1 : x22 $-> x24}
  (s1 : Square u1 v1 f1 f2)
  : s0 $@v s1 $== s0' $@v s1.
Proof.
  unfold vconcat.
  exact (((cat_assoc_opp u0 f1 v1 $@ (s1 $@R u0)) $@
      cat_assoc u0 u1 f2) $@L
    (fmap2 (cat_postcomp x00 v1) p $@R
      cat_assoc f0 v0 v1)).
Defined.

(** Vertical pasting is natural in its lower square. *)
Definition square_vconcat_natural_below
  {A : Type} `{Is21Cat A}
  {x00 x20 x02 x22 x04 x24 : A}
  {f0 : x00 $-> x20} {f1 : x02 $-> x22}
  {f2 : x04 $-> x24}
  {u0 : x00 $-> x02} {v0 : x20 $-> x22}
  (s0 : Square u0 v0 f0 f1)
  {u1 : x02 $-> x04} {v1 : x22 $-> x24}
  {s1 s1' : Square u1 v1 f1 f2}
  (p : s1 $== s1')
  : s0 $@v s1 $== s0 $@v s1'.
Proof.
  unfold vconcat.
  exact ((cat_assoc u0 u1 f2 $@L
      (fmap2 (cat_precomp x24 u0) p $@R
        cat_assoc_opp u0 f1 v1)) $@R
    (cat_assoc f0 v0 v1 $@ (v1 $@L s0))).
Defined.

(** ** Vertical concatenation of cylinders *)

(** Pasting the same square below both faces of a cylinder:

<<
       front face                 back face

            f0                         f0
       x00 ----> x20              x00 ----> x20
        |          |                |          |
     u0 |    s0    | v0          u1 |    s1    | v1
        v          v                v          v
       x02 ----> x22              x02 ----> x22
        |    f1    |                |    f1    |
     u2 |    s2    | v2          u2 |    s2    | v2
        v          v                v          v
       x04 ----> x24              x04 ----> x24
            f2                         f2

       p : u0 $== u1              q : v0 $== v1
>>

    The pasted cylinder has side faces [u2 $@L p] and [v2 $@L q].
    Keeping this calculation here means that clients need not expand
    either [Cylinder] or vertical concatenation. *)
Definition cylinder_vconcat_below
  {A : Type} `{Is21Cat A}
  {x00 x20 x02 x22 x04 x24 : A}
  {f0 : x00 $-> x20} {f1 : x02 $-> x22}
  {f2 : x04 $-> x24}
  {u0 u1 : x00 $-> x02} {v0 v1 : x20 $-> x22}
  {p : u0 $== u1} {q : v0 $== v1}
  {s0 : Square u0 v0 f0 f1} {s1 : Square u1 v1 f0 f1}
  {u2 : x02 $-> x04} {v2 : x22 $-> x24}
  (s2 : Square u2 v2 f1 f2)
  : Cylinder p q s0 s1
    -> Cylinder
      (u2 $@L p) (v2 $@L q)
      (s0 $@v s2) (s1 $@v s2).
Proof.
  intros c.
  unfold Cylinder in *.
  napply hconcat.
  { napply hconcat.
    { exact (isnat_tr
        (alnat := is1natural_cat_assoc_m _ _ _ _ f0 v2)
        (fun k => cat_assoc f0 k v2) q). }
    exact (fmap_square (cat_postcomp x00 v2) c). }
  napply hconcat.
  { napply hconcat.
    { exact (cat_assoc_opp_natural_r p f1 v2). }
    exact (bifunctor_coh_comp p s2). }
  exact (isnat_tr
    (alnat := is1natural_cat_assoc_r _ _ _ _ u2 f2)
    (fun k => cat_assoc k u2 f2) p).
Defined.

(** Pasting the same square above both faces of a cylinder:

<<
       front face                 back face

            f0                         f0
       x00 ----> x20              x00 ----> x20
        |          |                |          |
     u0 |    s0    | v0          u0 |    s0    | v0
        v          v                v          v
       x02 ----> x22              x02 ----> x22
        |    f1    |                |    f1    |
     u1 |    s1    | v1          u2 |    s2    | v2
        v          v                v          v
       x04 ----> x24              x04 ----> x24
            f2                         f2

       p : u1 $== u2              q : v1 $== v2
>>

    The pasted cylinder has side faces [p $@R u0] and [q $@R v0]. *)
Definition cylinder_vconcat_above
  {A : Type} `{Is21Cat A}
  {x00 x20 x02 x22 x04 x24 : A}
  {f0 : x00 $-> x20} {f1 : x02 $-> x22}
  {f2 : x04 $-> x24}
  {u0 : x00 $-> x02} {v0 : x20 $-> x22}
  (s0 : Square u0 v0 f0 f1)
  {u1 u2 : x02 $-> x04} {v1 v2 : x22 $-> x24}
  {p : u1 $== u2} {q : v1 $== v2}
  {s1 : Square u1 v1 f1 f2} {s2 : Square u2 v2 f1 f2}
  : Cylinder p q s1 s2
    -> Cylinder
      (p $@R u0) (q $@R v0)
      (s0 $@v s1) (s0 $@v s2).
Proof.
  intros c.
  unfold Cylinder in *.
  napply hconcat.
  { napply hconcat.
    { exact (isnat_tr
        (alnat := is1natural_cat_assoc_l _ _ _ _ f0 v0)
        (fun k => cat_assoc f0 v0 k) q). }
    exact (bifunctor_coh_comp s0 q)^$. }
  napply hconcat.
  { napply hconcat.
    { exact (cat_assoc_opp_natural_l u0 f1 q). }
    exact (fmap_square (cat_precomp x24 u0) c). }
  exact (isnat_tr
    (alnat := is1natural_cat_assoc_m _ _ _ _ u0 f2)
    (fun k => cat_assoc u0 k f2) p).
Defined.

(** Vertical concatenation pastes two cylinders along their common
    horizontal face.  Both the front and back square are concatenated
    by [$@v], while the side faces are horizontally composed. *)
Definition cylinder_vconcat
  {A : Type} `{Is21Cat A}
  {x00 x20 x02 x22 x04 x24 : A}
  {f0 : x00 $-> x20} {f1 : x02 $-> x22}
  {f2 : x04 $-> x24}
  {u0 u0' : x00 $-> x02} {v0 v0' : x20 $-> x22}
  {p0 : u0 $== u0'} {q0 : v0 $== v0'}
  {s00 : Square u0 v0 f0 f1} {s01 : Square u0' v0' f0 f1}
  {u1 u1' : x02 $-> x04} {v1 v1' : x22 $-> x24}
  {p1 : u1 $== u1'} {q1 : v1 $== v1'}
  {s10 : Square u1 v1 f1 f2} {s11 : Square u1' v1' f1 f2}
  (c0 : Cylinder p0 q0 s00 s01)
  (c1 : Cylinder p1 q1 s10 s11)
  : Cylinder
      (p0 $@@ p1) (q0 $@@ q1)
      (s00 $@v s10) (s01 $@v s11).
Proof.
  rapply (cylinder_rewrite_left (bifunctor_coh_comp p0 p1)).
  rapply (cylinder_rewrite_right (bifunctor_coh_comp q0 q1)).
  napply cylinder_comp.
  - exact (cylinder_vconcat_below s10 c0).
  - exact (cylinder_vconcat_above s01 c1).
Defined.

(** Horizontal concatenation is the third composition direction.  Two
    cylinders share a side face; their front and back squares are
    concatenated by [$@h]. *)
Definition cylinder_hconcat
  {A : Type} `{Is21Cat A}
  {x00 x20 x40 x02 x22 x42 : A}
  {f10 : x00 $-> x20} {f30 : x20 $-> x40}
  {f12 : x02 $-> x22} {f32 : x22 $-> x42}
  {u0 u1 : x00 $-> x02}
  {v0 v1 : x20 $-> x22}
  {w0 w1 : x40 $-> x42}
  {p : u0 $== u1} {q : v0 $== v1} {r : w0 $== w1}
  {s0 : Square u0 v0 f10 f12} {s1 : Square u1 v1 f10 f12}
  {t0 : Square v0 w0 f30 f32} {t1 : Square v1 w1 f30 f32}
  (c0 : Cylinder p q s0 s1)
  (c1 : Cylinder q r t0 t1)
  : Cylinder p r (s0 $@h t0) (s1 $@h t1).
Proof.
  unfold Cylinder in *.
  napply hconcat.
  2: exact (cat_assoc_inverse_natural_r p f12 f32).
  napply hconcat.
  2: exact (fmap_square (cat_postcomp x00 f32) c0).
  napply hconcat.
  - napply hconcat.
    + exact (cat_assoc_inverse_natural_l f10 f30 r).
    + exact (fmap_square (cat_precomp x42 f10) c1).
  - exact (isnat_tr
      (alnat := is1natural_cat_assoc_m _ _ _ _ f10 f32)
      (fun k => cat_assoc f10 k f32) q).
Defined.

(** One face of the pentagon, arranged as the square that compares
    postwhiskering past two different associations. *)
Definition cat_pentagon_square
  {A : Type} `{Is21Cat A}
  {a b c d e : A}
  (f : a $-> b) (g : b $-> c) (h : c $-> d) (k : d $-> e)
  : Square
      (cat_assoc g h k $@R f)
      (cat_assoc (g $o f) h k)
      (cat_assoc f g (k $o h))
      (cat_assoc f (h $o g) k $@ (k $@L cat_assoc f g h)).
Proof.
  unfold Square.
  exact (cat_pentagon a b c d e f g h k)^$.
Defined.

(** The next three lemmas expose the other pasting shapes obtained from
    a square whose bottom edge is composite.  They let the associativity
    proof below use differently oriented pentagon faces without expanding
    any square. *)
Local Lemma rotate_square_right
  {A : Type} `{Is1Gpd A}
  {x0 x1 x2 x3 x4 : A}
  {l : x0 $-> x1} {r : x2 $-> x3} {t : x0 $-> x2}
  {b0 : x1 $-> x4} {b1 : x4 $-> x3}
  (s : Square l r t (b1 $o b0))
  : Square r b0 (l $o t^$) b1^$.
Proof.
  unfold Square in *.
  apply gpd_moveL_Vh.
  lhs' exact (cat_assoc_opp _ _ _).
  lhs' exact (cat_assoc_opp _ _ _).
  exact (gpd_moveR_hV s^$).
Defined.

Local Lemma rotate_square_left
  {A : Type} `{Is1Gpd A}
  {x0 x1 x2 x3 x4 : A}
  {l : x0 $-> x1} {r : x2 $-> x3} {t : x0 $-> x2}
  {b0 : x1 $-> x4} {b1 : x4 $-> x3}
  (s : Square l r t (b1 $o b0))
  : Square b0 t l^$ (r^$ $o b1).
Proof.
  unfold Square in *.
  rhs' exact (cat_assoc b0 b1 r^$).
  apply gpd_moveL_Vh.
  lhs' exact (cat_assoc_opp _ _ _).
  exact (gpd_moveR_hV s).
Defined.

Local Lemma reassociate_square
  {A : Type} `{Is1Gpd A}
  {x0 x1 x2 x3 x4 : A}
  {l : x0 $-> x1} {r : x2 $-> x3} {t : x0 $-> x2}
  {b0 : x1 $-> x4} {b1 : x4 $-> x3}
  (s : Square l r t (b1 $o b0))
  : Square t b1 (b0 $o l) r.
Proof.
  unfold Square in *.
  exact (cat_assoc_opp _ _ _ $@ s^$).
Defined.

Lemma cat_pentagon_square_right
  {A : Type} `{Is21Cat A}
  {a b c d e : A}
  (f : a $-> b) (g : b $-> c) (h : c $-> d) (k : d $-> e)
  : Square
      (cat_assoc (g $o f) h k)
      (cat_assoc f (h $o g) k)
      ((cat_assoc g h k $@R f) $o cat_assoc_opp f g (k $o h))
      (k $@L cat_assoc_opp f g h).
Proof.
  napply vconcatR.
  { napply vconcatL.
    { exact ((cat_assoc g h k $@R f) $@L
        cat_assoc_opp_is_rev a b c e f g (k $o h)). }
    exact (rotate_square_right (cat_pentagon_square f g h k)). }
  exact (fmap2 (cat_postcomp a k)
      (cat_assoc_opp_is_rev a b c d f g h)
    $@ gpd_1functor_V (cat_postcomp a k) (cat_assoc f g h)).
Defined.

Lemma cat_pentagon_square_left
  {A : Type} `{Is21Cat A}
  {a b c d e : A}
  (f : a $-> b) (g : b $-> c) (h : c $-> d) (k : d $-> e)
  : Square
      (cat_assoc f (h $o g) k)
      (cat_assoc f g (k $o h))
      (cat_assoc_opp g h k $@R f)
      (cat_assoc_opp (g $o f) h k $o (k $@L cat_assoc f g h)).
Proof.
  napply vconcatR.
  { napply vconcatL.
    { exact (fmap2 (cat_precomp e f)
          (cat_assoc_opp_is_rev b c d e g h k)
        $@ gpd_1functor_V
          (cat_precomp e f) (cat_assoc g h k)). }
    exact (rotate_square_left (cat_pentagon_square f g h k)). }
  exact (cat_assoc_opp_is_rev a c d e (g $o f) h k
    $@R (k $@L cat_assoc f g h)).
Defined.

Lemma cat_pentagon_square_end
  {A : Type} `{Is21Cat A}
  {a b c d e : A}
  (f : a $-> b) (g : b $-> c) (h : c $-> d) (k : d $-> e)
  : Square
      (cat_assoc f g (k $o h))
      (k $@L cat_assoc f g h)
      (cat_assoc f (h $o g) k $o (cat_assoc g h k $@R f))
      (cat_assoc (g $o f) h k).
Proof.
  exact (reassociate_square (cat_pentagon_square f g h k)).
Defined.

(** Functoriality for the fivefold composite occurring in vertical
    concatenation.  Keeping its original bracketing makes it possible to
    distribute a whiskering without exposing the definition of a square. *)
Lemma fmap_vconcat_composite
  {A B : Type} `{Is1Cat A, Is1Cat B}
  (F : A -> B) `{!Is0Functor F, !Is1Functor F}
  {a0 a1 a2 a3 a4 a5 : A}
  (p0 : a0 $-> a1) (p1 : a1 $-> a2) (p2 : a2 $-> a3)
  (p3 : a3 $-> a4) (p4 : a4 $-> a5)
  : fmap F ((p4 $o (p3 $o p2)) $o (p1 $o p0))
    $== (fmap F p4 $o (fmap F p3 $o fmap F p2))
      $o (fmap F p1 $o fmap F p0).
Proof.
  lhs' exact (fmap_comp F (p1 $o p0) (p4 $o (p3 $o p2))).
  lhs' exact (fmap F (p4 $o (p3 $o p2)) $@L
    fmap_comp F p0 p1).
  lhs' exact (fmap_comp F (p3 $o p2) p4
    $@R (fmap F p1 $o fmap F p0)).
  exact ((fmap F p4 $@L fmap_comp F p2 p3)
    $@R (fmap F p1 $o fmap F p0)).
Defined.

Lemma fmap_Vpp
  {A B : Type} `{Is1Gpd A, Is1Gpd B}
  (F : A -> B) `{!Is0Functor F, !Is1Functor F}
  {x0 x1 x2 x3 : A}
  (p : x1 $-> x0) (q : x1 $-> x2) (r : x2 $-> x3)
  : fmap F (p^$ $@ q $@ r)
    $== (fmap F p)^$ $@ fmap F q $@ fmap F r.
Proof.
  lhs' exact (fmap_comp F (p^$ $@ q) r).
  lhs' exact (fmap F r $@L fmap_comp F p^$ q).
  exact (fmap F r $@L
    (fmap F q $@L gpd_1functor_V F p)).
Defined.

(** Whiskering distributes over the five constituent 2-cells of a
    vertical composite square. *)
Lemma square_vconcat_prewhisker
  {A : Type} `{Is21Cat A}
  {x x00 x20 x02 x22 x04 x24 : A}
  (k : x $-> x00)
  {f0 : x00 $-> x20} {f1 : x02 $-> x22}
  {f2 : x04 $-> x24}
  {u0 : x00 $-> x02} {v0 : x20 $-> x22}
  (s0 : Square u0 v0 f0 f1)
  {u1 : x02 $-> x04} {v1 : x22 $-> x24}
  (s1 : Square u1 v1 f1 f2)
  : (s0 $@v s1) $@R k
    $== ((cat_assoc f0 v0 v1 $@R k) $@ ((v1 $@L s0) $@R k))
      $@ (((cat_assoc_opp u0 f1 v1 $@R k) $@ ((s1 $@R u0) $@R k))
        $@ (cat_assoc u0 u1 f2 $@R k)).
Proof.
  unfold vconcat.
  exact (fmap_vconcat_composite (cat_precomp x24 k)
    (cat_assoc f0 v0 v1) (v1 $@L s0)
    (cat_assoc_opp u0 f1 v1) (s1 $@R u0)
    (cat_assoc u0 u1 f2)).
Defined.

Lemma square_vconcat_postwhisker
  {A : Type} `{Is21Cat A}
  {x00 x20 x02 x22 x04 x24 x : A}
  (k : x24 $-> x)
  {f0 : x00 $-> x20} {f1 : x02 $-> x22}
  {f2 : x04 $-> x24}
  {u0 : x00 $-> x02} {v0 : x20 $-> x22}
  (s0 : Square u0 v0 f0 f1)
  {u1 : x02 $-> x04} {v1 : x22 $-> x24}
  (s1 : Square u1 v1 f1 f2)
  : k $@L (s0 $@v s1)
    $== ((k $@L cat_assoc f0 v0 v1) $@ (k $@L (v1 $@L s0)))
      $@ (((k $@L cat_assoc_opp u0 f1 v1) $@ (k $@L (s1 $@R u0)))
        $@ (k $@L cat_assoc u0 u1 f2)).
Proof.
  unfold vconcat.
  exact (fmap_vconcat_composite (cat_postcomp x00 k)
    (cat_assoc f0 v0 v1) (v1 $@L s0)
    (cat_assoc_opp u0 f1 v1) (s1 $@R u0)
    (cat_assoc u0 u1 f2)).
Defined.

Local Lemma reassociate_vconcat_prewhisker
  {A : Type} `{Is1Cat A}
  {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : A}
  (p0 : x0 $-> x1) (p1 : x1 $-> x2) (p2 : x2 $-> x3)
  (p3 : x3 $-> x4) (p4 : x4 $-> x5) (p5 : x5 $-> x6)
  (p6 : x6 $-> x7) (p7 : x7 $-> x8) (p8 : x8 $-> x9)
  : (p8 $o (((p7 $o (p6 $o p5)) $o (p4 $o p3)) $o p2))
      $o (p1 $o p0)
    $== ((((p8 $o p7) $o (p6 $o p5)) $o (p4 $o (p3 $o p2)))
      $o (p1 $o p0)).
Proof.
  lhs' exact (cat_assoc_opp p2
    ((p7 $o (p6 $o p5)) $o (p4 $o p3)) p8
    $@R (p1 $o p0)).
  lhs' exact ((cat_assoc_opp (p4 $o p3)
      (p7 $o (p6 $o p5)) p8 $@R p2)
    $@R (p1 $o p0)).
  lhs' exact (((cat_assoc_opp (p6 $o p5) p7 p8
      $@R (p4 $o p3)) $@R p2)
    $@R (p1 $o p0)).
  lhs' exact (cat_assoc p2 (p4 $o p3)
    ((p8 $o p7) $o (p6 $o p5)) $@R (p1 $o p0)).
  exact (((p8 $o p7) $o (p6 $o p5)) $@L cat_assoc p2 p3 p4
    $@R (p1 $o p0)).
Defined.

Local Lemma reassociate_vconcat_postwhisker
  {A : Type} `{Is1Cat A}
  {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : A}
  (p0 : x0 $-> x1) (p1 : x1 $-> x2) (p2 : x2 $-> x3)
  (p3 : x3 $-> x4) (p4 : x4 $-> x5) (p5 : x5 $-> x6)
  (p6 : x6 $-> x7) (p7 : x7 $-> x8) (p8 : x8 $-> x9)
  : (p8 $o (p7 $o p6))
      $o (((p5 $o (p4 $o p3)) $o (p2 $o p1)) $o p0)
    $== ((p8 $o (p7 $o (p6 $o p5))) $o (p4 $o p3))
      $o (p2 $o (p1 $o p0)).
Proof.
  lhs' exact (cat_assoc_opp p0
    ((p5 $o (p4 $o p3)) $o (p2 $o p1))
    (p8 $o (p7 $o p6))).
  lhs' exact (cat_assoc_opp (p2 $o p1) (p5 $o (p4 $o p3))
    (p8 $o (p7 $o p6)) $@R p0).
  lhs' exact ((cat_assoc_opp (p4 $o p3) p5
      (p8 $o (p7 $o p6)) $@R (p2 $o p1)) $@R p0).
  lhs' exact ((((cat_assoc p5 (p7 $o p6) p8
      $@ (p8 $@L cat_assoc p5 p6 p7)) $@R (p4 $o p3))
    $@R (p2 $o p1)) $@R p0).
  lhs' exact (cat_assoc p0 (p2 $o p1)
    ((p8 $o (p7 $o (p6 $o p5))) $o (p4 $o p3))).
  exact (((p8 $o (p7 $o (p6 $o p5))) $o (p4 $o p3))
    $@L cat_assoc p0 p1 p2).
Defined.

Section SquareVconcatAssoc.

  Context
    {A : Type} `{Is21Cat A}
    {x00 x20 x02 x22 x04 x24 x06 x26 : A}
    {f0 : x00 $-> x20} {f1 : x02 $-> x22}
    {f2 : x04 $-> x24} {f3 : x06 $-> x26}
    {u0 : x00 $-> x02} {u1 : x02 $-> x04}
    {u2 : x04 $-> x06}
    {v0 : x20 $-> x22} {v1 : x22 $-> x24}
    {v2 : x24 $-> x26}
    (s0 : Square u0 v0 f0 f1)
    (s1 : Square u1 v1 f1 f2)
    (s2 : Square u2 v2 f2 f3).

  Local Lemma square_vconcat_assoc_front
    : s0 $@v (s1 $@v s2)
      $== cat_assoc u0 (u2 $o u1) f3 $o cat_assoc u1 u2 f3 $@R u0 $o
        ((s2 $@R u1) $@R u0 $o cat_assoc_opp u1 f2 v2 $@R u0) $o
        ((v2 $@L s1) $@R u0 $o
          (cat_assoc f1 v1 v2 $@R u0 $o cat_assoc_opp u0 f1 (v2 $o v1))) $o
        ((v2 $o v1) $@L s0 $o cat_assoc f0 v0 (v2 $o v1)).
  Proof.
    unfold vconcat.
    lhs' napply (fun p =>
      ((cat_assoc u0 (u2 $o u1) f3 $@L
          (p $@R cat_assoc_opp u0 f1 (v2 $o v1)))
        $@R ((v2 $o v1) $@L s0 $o cat_assoc f0 v0 (v2 $o v1)))).
    { exact (square_vconcat_prewhisker u0 s1 s2). }
    napply reassociate_vconcat_prewhisker.
  Defined.

  (** From left to right, this pastes a pentagon at each horizontal
      edge and an associator-naturality square at each [s0], [s1], and
      [s2].  Pairing each pentagon with the following naturality square
      minimizes the boundary reassociation needed above and below. *)
  Local Lemma square_vconcat_assoc_pasting
    : Square (cat_assoc v0 v1 v2 $@R f0) (f3 $@L cat_assoc u0 u1 u2)
      (cat_assoc u0 (u2 $o u1) f3 $o cat_assoc u1 u2 f3 $@R u0 $o
        ((s2 $@R u1) $@R u0 $o cat_assoc_opp u1 f2 v2 $@R u0) $o
        ((v2 $@L s1) $@R u0 $o
          (cat_assoc f1 v1 v2 $@R u0 $o cat_assoc_opp u0 f1 (v2 $o v1))) $o
        ((v2 $o v1) $@L s0 $o cat_assoc f0 v0 (v2 $o v1)))
      (cat_assoc (u1 $o u0) u2 f3 $o
        (s2 $@R (u1 $o u0) $o
          (cat_assoc_opp (u1 $o u0) f2 v2 $o v2 $@L cat_assoc u0 u1 f2)) $o
        (v2 $@L (s1 $@R u0) $o v2 $@L cat_assoc_opp u0 f1 v1) $o
        (v2 $@L (v1 $@L s0) $o
          cat_assoc f0 (v1 $o v0) v2 $@ (v2 $@L cat_assoc f0 v0 v1))).
  Proof.
    nrefine (hconcat
      (hconcat
        (cat_pentagon_square f0 v0 v1 v2)
        (cat_assoc_natural_r s0 v1 v2)) _).
    nrefine (hconcat
      (hconcat
        (cat_pentagon_square_right u0 f1 v1 v2)
        (cat_assoc_natural_m u0 s1 v2)) _).
    exact (hconcat
      (hconcat
        (cat_pentagon_square_left u0 u1 f2 v2)
        (cat_assoc_natural_l u0 u1 s2))
      (cat_pentagon_square_end u0 u1 u2 f3)).
  Defined.

  Local Lemma square_vconcat_assoc_back
    : (s0 $@v s1) $@v s2
      $== cat_assoc (u1 $o u0) u2 f3 $o
        (s2 $@R (u1 $o u0) $o
          (cat_assoc_opp (u1 $o u0) f2 v2 $o v2 $@L cat_assoc u0 u1 f2)) $o
        (v2 $@L (s1 $@R u0) $o v2 $@L cat_assoc_opp u0 f1 v1) $o
        (v2 $@L (v1 $@L s0) $o
          cat_assoc f0 (v1 $o v0) v2 $@ (v2 $@L cat_assoc f0 v0 v1)).
  Proof.
    unfold vconcat.
    lhs' napply (fun p =>
      (((cat_assoc_opp (u1 $o u0) f2 v2 $@ (s2 $@R (u1 $o u0)))
          $@ cat_assoc (u1 $o u0) u2 f3) $@L
        (p $@R cat_assoc f0 (v1 $o v0) v2))).
    { exact (square_vconcat_postwhisker v2 s0 s1). }
    napply reassociate_vconcat_postwhisker.
  Defined.

  Definition square_vconcat_assoc
    : Cylinder
      (cat_assoc u0 u1 u2)
      (cat_assoc v0 v1 v2)
      (s0 $@v (s1 $@v s2))
      ((s0 $@v s1) $@v s2).
  Proof.
    unfold Cylinder.
    nrefine (vconcatL (square_vconcat_assoc_front) _).
    nrefine (vconcatR square_vconcat_assoc_pasting _).
    exact (square_vconcat_assoc_back).
  Defined.

End SquareVconcatAssoc.

Local Lemma square_vconcat_idl_tail
  {A : Type} `{Is21Cat A}
  {a b c : A} (u : a $-> b) (g : b $-> c)
  : ((cat_assoc_opp u g (Id c) $@ (vrefl g $@R u))
      $@ cat_assoc u (Id b) g)
      $@ (g $@L cat_idl u)
    $== cat_idl (g $o u).
Proof.
  lhs' exact (cat_assoc_opp
    (cat_assoc_opp u g (Id c) $@ (vrefl g $@R u))
    (cat_assoc u (Id b) g)
    (g $@L cat_idl u)).
  lhs' exact (cat_prewhisker (A := a $-> c)
    (cat_tril (A := A) a b c u g)
    (cat_assoc_opp u g (Id c) $@ (vrefl g $@R u))).
  unfold vrefl.
  lhs' exact (cat_assoc_opp
    (cat_assoc_opp u g (Id c))
    ((cat_idl g $@ (cat_idr g)^$) $@R u)
    (cat_idr g $@R u)).
  lhs' exact (((cat_idr g $@R u) $@L
    cat_prewhisker_pp u (cat_idl g) (cat_idr g)^$)
    $@R cat_assoc_opp u g (Id c)).
  lhs' exact (cat_assoc_opp
      (cat_idl g $@R u)
      ((cat_idr g)^$ $@R u)
      (cat_idr g $@R u)
    $@R cat_assoc_opp u g (Id c)).
  lhs' exact ((((cat_idr g $@R u) $@L
      gpd_1functor_V (cat_precomp c u) (cat_idr g))
      $@R (cat_idl g $@R u))
    $@R cat_assoc_opp u g (Id c)).
  lhs' exact ((gpd_isretr (cat_idr g $@R u)
      $@R (cat_idl g $@R u))
    $@R cat_assoc_opp u g (Id c)).
  lhs' exact (cat_idl (cat_idl g $@R u)
    $@R cat_assoc_opp u g (Id c)).
  lhs' exact (cat_idl_assoc u g
    $@R cat_assoc_opp u g (Id c)).
  lhs' exact (cat_assoc
    (cat_assoc_opp u g (Id c))
    (cat_assoc u g (Id c))
    (cat_idl (g $o u))).
  lhs' exact (cat_idl (g $o u) $@L
    (cat_assoc u g (Id c) $@L
      cat_assoc_opp_is_rev a b c c u g (Id c))).
  lhs' exact (cat_idl (g $o u) $@L
    gpd_isretr (cat_assoc u g (Id c))).
  exact (cat_idr (cat_idl (g $o u))).
Defined.

Definition square_vconcat_idl
  {A : Type} `{Is21Cat A}
  {x00 x20 x02 x22 : A}
  {f : x00 $-> x20} {g : x02 $-> x22}
  {u : x00 $-> x02} {v : x20 $-> x22}
  (s : Square u v f g)
  : Cylinder
    (cat_idl u) (cat_idl v)
    (s $@v vrefl g) s.
Proof.
  unfold Cylinder.
  napply Build_Square.
  unfold vconcat.
  lhs' exact (cat_assoc_opp
    (cat_assoc f v (Id x22) $@ ((Id x22) $@L s))
    ((cat_assoc_opp u g (Id x22) $@ (vrefl g $@R u))
      $@ cat_assoc u (Id x02) g)
    (g $@L cat_idl u)).
  lhs' exact (square_vconcat_idl_tail u g
    $@R (cat_assoc f v (Id x22) $@ ((Id x22) $@L s))).
  lhs' exact (cat_assoc_opp
    (cat_assoc f v (Id x22))
    ((Id x22) $@L s)
    (cat_idl (g $o u))).
  lhs' exact (cat_idl_natural s
    $@R cat_assoc f v (Id x22)).
  lhs' exact (cat_assoc
    (cat_assoc f v (Id x22))
    (cat_idl (v $o f)) s).
  exact (s $@L (cat_idl_assoc f v)^$).
Defined.

Local Lemma square_vconcat_idr_tail
  {A : Type} `{Is21Cat A}
  {a b c : A} (u : a $-> b) (g : b $-> c)
  : cat_assoc (Id a) u g $@ (g $@L cat_idr u)
    $== cat_idr (g $o u).
Proof.
  lhs' exact (cat_idr_assoc u g
    $@R cat_assoc (Id a) u g).
  lhs' exact (cat_assoc
    (cat_assoc (Id a) u g)
    (cat_assoc_opp (Id a) u g)
    (cat_idr (g $o u))).
  lhs' exact (cat_idr (g $o u) $@L
    (cat_assoc_opp_is_rev a a b c (Id a) u g
      $@R cat_assoc (Id a) u g)).
  lhs' exact (cat_idr (g $o u) $@L
    gpd_issect (cat_assoc (Id a) u g)).
  exact (cat_idr (cat_idr (g $o u))).
Defined.

Local Lemma square_vconcat_idr_head
  {A : Type} `{Is21Cat A}
  {a b c : A} (f : a $-> b) (v : b $-> c)
  : ((cat_assoc f (Id b) v $@ (v $@L vrefl f))
      $@ cat_assoc_opp (Id a) f v)
      $@ cat_idr (v $o f)
    $== cat_idr v $@R f.
Proof.
  unfold vrefl.
  lhs' exact (cat_idr (v $o f) $@L
    (cat_assoc_opp (Id a) f v $@L
      ((cat_postwhisker_pp v (cat_idl f) (cat_idr f)^$)
        $@R cat_assoc f (Id b) v))).
  lhs' exact (cat_idr (v $o f) $@L
    (cat_assoc_opp (Id a) f v $@L
      cat_assoc
        (cat_assoc f (Id b) v)
        (v $@L cat_idl f)
        (v $@L (cat_idr f)^$))).
  lhs' exact (cat_idr (v $o f) $@L
    (cat_assoc_opp (Id a) f v $@L
      ((v $@L (cat_idr f)^$) $@L
        cat_tril (A := A) a b c f v))).
  lhs' exact (cat_assoc_opp
    ((cat_idr v $@R f) $@ (v $@L (cat_idr f)^$))
    (cat_assoc_opp (Id a) f v)
    (cat_idr (v $o f))).
  lhs' exact ((cat_idr_assoc f v)^$
    $@R ((cat_idr v $@R f) $@ (v $@L (cat_idr f)^$))).
  lhs' exact (cat_assoc_opp
    (cat_idr v $@R f)
    (v $@L (cat_idr f)^$)
    (v $@L cat_idr f)).
  lhs' exact (cat_assoc
    (cat_idr v $@R f)
    (v $@L (cat_idr f)^$)
    (v $@L cat_idr f)).
  lhs' exact ((v $@L cat_idr f) $@L
    ((gpd_1functor_V (cat_postcomp a v) (cat_idr f))
      $@R (cat_idr v $@R f))).
  lhs' exact (cat_assoc_opp
    (cat_idr v $@R f)
    (v $@L cat_idr f)^$
    (v $@L cat_idr f)).
  lhs' exact (gpd_isretr (v $@L cat_idr f)
    $@R (cat_idr v $@R f)).
  exact (cat_idl (cat_idr v $@R f)).
Defined.

Definition square_vconcat_idr
  {A : Type} `{Is21Cat A}
  {x00 x20 x02 x22 : A}
  {f : x00 $-> x20} {g : x02 $-> x22}
  {u : x00 $-> x02} {v : x20 $-> x22}
  (s : Square u v f g)
  : Cylinder
    (cat_idr u) (cat_idr v)
    (vrefl f $@v s) s.
Proof.
  unfold Cylinder.
  napply Build_Square.
  unfold vconcat.
  lhs' exact (cat_assoc_opp
    (cat_assoc f (Id x20) v $@ (v $@L vrefl f))
    ((cat_assoc_opp (Id x00) f v $@ (s $@R Id x00))
      $@ cat_assoc (Id x00) u g)
    (g $@L cat_idr u)).
  lhs' exact (cat_assoc_opp
    (cat_assoc_opp (Id x00) f v $@ (s $@R Id x00))
    (cat_assoc (Id x00) u g)
    (g $@L cat_idr u)
    $@R (cat_assoc f (Id x20) v $@ (v $@L vrefl f))).
  lhs' exact (cat_assoc
    (cat_assoc f (Id x20) v $@ (v $@L vrefl f))
    ((cat_assoc_opp (Id x00) f v) $@ (s $@R Id x00))
    ((cat_assoc (Id x00) u g) $@ (g $@L cat_idr u))).
  lhs' exact (square_vconcat_idr_tail u g
    $@R ((cat_assoc f (Id x20) v $@ (v $@L vrefl f))
      $@ (cat_assoc_opp (Id x00) f v $@ (s $@R Id x00)))).
  lhs' exact (cat_idr (g $o u) $@L
    cat_assoc
      (cat_assoc f (Id x20) v $@ (v $@L vrefl f))
      (cat_assoc_opp (Id x00) f v)
      (s $@R Id x00)).
  lhs' exact (cat_assoc_opp
    ((cat_assoc f (Id x20) v $@ (v $@L vrefl f))
      $@ cat_assoc_opp (Id x00) f v)
    (s $@R Id x00)
    (cat_idr (g $o u))).
  lhs' exact (cat_idr_natural s
    $@R ((cat_assoc f (Id x20) v $@ (v $@L vrefl f))
      $@ cat_assoc_opp (Id x00) f v)).
  lhs' exact (cat_assoc
    ((cat_assoc f (Id x20) v $@ (v $@L vrefl f))
      $@ cat_assoc_opp (Id x00) f v)
    (cat_idr (v $o f)) s).
  exact (s $@L square_vconcat_idr_head f v).
Defined.
