# S⁷: direct gluing and the remaining mixed comparison

The preferred route is now `S7DirectGluing` in
[`HSpaceS7/Direct.v`](../theories/Homotopy/HSpaceS7/Direct.v), followed by
`hspace_s7_from_direct_mixed` in
[`theories/Homotopy/HSpaceS7.v`](../theories/Homotopy/HSpaceS7.v).
It uses the existing `first_l`, `first_r`, `middle_l`, and their overlaps,
with the unchanged multiplication and canonical diamond. Two compatible
whole faces are proved; the remaining input is the explicit **4-path
`S7DirectGluing.Mixed`**. It has not been proved in general.

The earlier scalar-loop assembly remains available separately as
`S7ProofOutline`. Its sole remaining hypothesis is **OPEN 5**. Former
OPEN 1, OPEN 2, and OPEN 3 are supplied by `S7LeftScalar.loop_y_joinl`,
`S7RightScalar.loop_y_joinr`, and `S7MiddleScalar.loop_x_joinl`; former OPEN 4
is constructed by transport. The new `Mixed` is not asserted to equal this
older loop-family obligation.

The associativity required here is that of the **circle double**, which is
pointedly equivalent to S³. The resulting structure on S⁷ only needs to be an
H-space. No associator pentagon is required for the second doubling.

## Direct gluing

### File layout

[`HSpaceS7/Direct.v`](../theories/Homotopy/HSpaceS7/Direct.v) is a
compatibility facade: importing it still exposes `S7DirectGluing`.
The implementation is split into separately compiled files:

- [`Direct/Core.v`](../theories/Homotopy/HSpaceS7/Direct/Core.v): the chosen
  faces and overlap, original `Mixed`, and conditional associator assembly.
- [`Direct/Normalization.v`](../theories/Homotopy/HSpaceS7/Direct/Normalization.v):
  the prescribed cubes, whole-face η calculation, and factorization of the
  existing `computed_pasting`.
- [`Direct/Comparison.v`](../theories/Homotopy/HSpaceS7/Direct/Comparison.v):
  the edge-ratio equivalence and the sufficient section-comparison criterion.
- [`Direct/RightRightScalars.v`](../theories/Homotopy/HSpaceS7/Direct/RightRightScalars.v):
  the reciprocal-parameter and scalar-map comparisons for the right–right case.
- [`Direct/RightRight.v`](../theories/Homotopy/HSpaceS7/Direct/RightRight.v):
  rotation of the actual canonical circle diamond, with its pole computations
  and meridian coherence.
- [`Direct/RightRightMiddle.v`](../theories/Homotopy/HSpaceS7/Direct/RightRightMiddle.v):
  the mapped multiplication-diamond comparison, its four original scalar
  boundaries, and the middle-right associator with its last-left overlap.
- [`Direct/RightRightComparison.v`](../theories/Homotopy/HSpaceS7/Direct/RightRightComparison.v):
  the proved `eta_associator_rr`, with exactly the prescribed
  `eta_overlap_l/r` constructor computations.
- [`Direct/MiddleComparison.v`](../theories/Homotopy/HSpaceS7/Direct/MiddleComparison.v):
  transport compatibility for the whole right-middle face, its attachment
  to the original `computed_pasting`, and an equivalent remaining equation
  retaining both computed middle cubes.

The existing η associator and its three overlap witnesses are exposed for
cross-file comparison proofs; their defining terms are unchanged.

### The chosen faces

Write `P(x,y,z) := (mu (mu x y) z = mu x (mu y z))`, and let `BL`, `BR`, and
`BM` be the existing first-left, first-right, and middle-left associators.
For fixed `y,z`, put `F(x) := mu (mu x y) z` and
`G(x) := mu x (mu y z)`. The first-argument join glue requires

```text
Gamma a b y z := ap F (jglue a b) @ BR b y z
                = BL a y z @ ap G (jglue a b).
```

The following constructions are checked:

- `face_y a b s z` is `concat_Ap (fun x => BM s x z) (jglue a b)`.
  Its endpoints are definitionally the original `BL` and `BR` rows.
- `face_z a b y c` is naturality of `AL (-) y c`, with its endpoints
  replaced using the original left and right overlaps.
- `face_overlap a b s c` identifies `face_z a b (joinl s) c` with
  `face_y a b s (joinl c)`. It is obtained from
  `concat_Ap_homotopic` applied to the middle overlap, whose endpoint
  components are precisely the two overlaps used by `face_z`.

### The exact remaining extension

The general dependent construction `Join_ind2_from_left` in
[`Join/Rec2.v`](../theories/Homotopy/Join/Rec2.v) extends two compatible
left faces, with right-constructor data chosen by transport. It works for
arbitrary dependent families and independent source and fiber universes;
it does not assume truncation or extensionality.

For `Gamma a b`, abbreviate its chosen right row and remaining y-glue family
by

```text
R t z   := transport (fun y => Gamma a b y z) (jglue North t)
             (face_y a b North z)
E s t z := transport (fun y => Gamma a b y z) (jglue s t)
             (face_y a b s z) = R t z.
```

The known last-left face and intersection comparison supply
`el s t c : E s t (joinl c)`. Explicitly, with

```text
h s t c := (apD (fun y => face_z a b y c) (jglue s t))^
             @ ap (transport (fun y => Gamma a b y (joinl c))
                    (jglue s t)) (face_overlap a b s c),
```

we use `el s t c := (h s t c)^ @ h North t c`. Choose

```text
er s t d := transport (E s t) (jglue North d) (el s t North).
```

Then **`Mixed a b s t c d`** is exactly

```text
transport (E s t) (jglue c d) (el s t c) = er s t d.
```

`Gamma` is a 2-path in the join, `E` a 3-path, and `Mixed` a 4-path.
Two unit cases are already checked: `s = North` follows by canonical
cancellation (`Join_ind2_from_left_mixed_base`), and `c = North` is reflexivity. The general
mixed filler remains open; matching boundaries do not supply it.

Given this one input, `first_glue` extends `Gamma` to arbitrary `y,z`.
It retains `face_y` definitionally and `face_z` by a comparison whose
left-constructor value is the actual `face_overlap`. Finally,

```text
associator x y z := Join_ind_FlFr F G
  (fun a => BL a y z) (fun b => BR b y z)
  (fun a b => first_glue a b y z) x.
```

Reversing this path gives `Associative mu`; second doubling and sphere
transfer give `hspace_s7_from_direct_mixed`. This route uses no `T`, `M`,
`ap_loop_nullhomotopic`, or circle induction on the last scalar. It does not
require prescribed last-argument computation rules for the associator.

### Checked normalization of the mixed boundary

`equiv_mixed_normalize` now proves an equivalence

```text
NormalizedMixed a b s t c d <~> Mixed a b s t c d.
```

It preserves the chosen sides, not just existence of some extension.
For fixed `a,b,t`, write

```text
U_s(z) := transport (fun y => Gamma a b y z) (jglue s t)
            (face_y a b s z)
Q(z)   := Gamma a b (joinr t) z.
```

First, `dpath_path_FlFr_D` converts the original obligation into

```text
ap (transport Q (jglue c d)) (el s t c) @ apD U_North (jglue c d)
  = apD U_s (jglue c d) @ er s t d.
```

The two dependent applications are computed, rather than left abstract:

- `Join_ind_FlFr_ind_beta_jglue_jglue` keeps both outer join beta paths and
  the specified inner mixed computation. Its specialization `face_y_glue`
  computes the middle face using the original
  `S7MiddleScalar.middle_l_glue_glue`. The analogous first-left and
  first-right specializations are regression-checked too.
- `apD_transport` gives `transported_face_glue`: its computed side `Z_s(c,d)`
  is transport interchange in `Gamma`, followed by the transported middle
  cell. The actual middle cell includes both outer beta paths.
- The transported edge `er` is also expanded using
  `transport_paths_FlFr_D`. No transport in a family of 3-paths is left.

With the previously specified `h s t c`, set

```text
K_s(c,d) := ap (transport Q (jglue c d)) (h s t c) @ Z_s(c,d).
```

The checked normalized goal is exactly

```text
K_s(c,d) @ K_s(North,d)^
  = K_North(c,d) @ K_North(North,d)^.
```

Both sides start at `transport Q (jglue c d) (face_z a b (joinr t) c)`
and end at `transport Q (jglue North d) (face_z a b (joinr t) North)`.
Their different intermediate endpoints `U_s (joinr d)` have been removed
by the general equivalence `equiv_pasting_zigzags`, not by identifying
arbitrary fillers. This remains a 4-path in the join.

The unit cases and both round trips of the equivalence are checked, and a
normalized filler family can already be passed through it to the direct S⁷
assembly. The further expansion below computes the previously abstract
transport-interchange side and last-face variation. Neither calculation
proves the general mixed filler.

### Expansion into the specified cubes

The reusable `naturality_square_filler` in `Types/Paths.v` fills one face
of a cube by pasting its other five specified faces. In terms of the two
composite naturality squares `nL,nR`, its expression is

```text
cancelL p0 _ _ ((nL @ (source_face @@ 1)) @ nR^).
```

`transport_naturality_square_compute` identifies square transport with
this expression. `naturality_square_filler_glue` pastes the five chosen
cubes describing variation of the input faces, and
`apD_naturality_square_filler` proves that this computes the variation of
the filler. This works even when the ambient target type depends on the
parameter, with independent source and fiber universes.

For `Gamma`, the resulting `transported_face a b s t z` is a path-algebra
expression in the four y-naturality squares and `face_y a b s z`. Write
`theta_s(z) : U_s(z) = transported_face a b s t z` for its transport
computation. The checked `transported_face_cell` uses exactly:

1. `left_product_cell`, using `sq_ap_nat` on the specified inner
   multiplication square;
2. `right_product_cell`, applying the first multiplication homotopy to the
   specified inner multiplication square;
3. `S7LeftScalar.first_l_glue_glue`;
4. `S7RightScalar.first_r_glue_glue`;
5. `S7MiddleScalar.middle_l_glue_glue`.

The first two retain all four inner multiplication edge computations and
`Join_rec2_beta_jglue_jglue`. The right product rewrites both mapped faces
of the naturality cube using that beta witness, retaining the other four
faces. Their individual beta proofs compare them to the original
xyz-dependent applications. The last three retain both outer beta paths. `transported_face_cell_beta` proves that this is the actual
dependent application of `transported_face`,
and `transported_face_glue_expansion` compares it with the old interchange
side, including both `theta` endpoint adjustments.

Similarly, `last_face_cell` expands the y-variation of `face_z` into
`last_associator_cell` and the two specified overlap cubes. The latter are
the original `overlap_glue` proofs converted by `equiv_naturality_transport2`,
with their first-associator beta adjustments. `last_face_cell_beta` checks
the result against `apD face_z`; no replacement overlap is used.

`last_associator_cell` computes all three factors of the original `AL`:

```text
rho_c(mu x y) @ (diagonal_equivariance_c x y)^ @ ap (mu x) (rho_c(y))^.
```

Its first cube is `sq_ap_nat` for `rho_c` on the specified multiplication
square. Its second is the original
`cd_op_diagonal_equivariance_glue_glue`, with both outer beta paths and the
inverse-naturality conversion. Its third is `sq_ap_nat` for the first
multiplication homotopy on the inverse right-translation square. That
square retains the original `join_natsq 1 (comm c t)` and both recursor
computations. `concat_Ap_ap` accounts for the reversed orientation of the
third factor. The three cubes are pasted, and `last_associator_cell_beta`
compares the result with the original dependent application.

The resulting `computed_pasting` satisfies the checked equality

```text
K_s(c,d) @ theta_s(joinr d) = computed_pasting a b s t c d.
```

Cancelling this common change of center using `concat_pV_pp` gives
`equiv_mixed_expansion`:

```text
(computed_pasting a b s t c d @ (computed_pasting a b s t North d)^
   = computed_pasting a b North t c d @ (computed_pasting a b North t North d)^)
  <~> Mixed a b s t c d.
```

There is no `transport_transport (Gamma a b)` in the expanded pasting.
Ordinary path transports and their specified endpoint adjustments remain;
this is not yet a completely transport-free multiplication-diamond diagram.
No extra proof universes are introduced. Regression checks cover the exact
five-face expression, both computed product cubes, original side and pasting
comparisons, both unit cases, round trips, and conditional small S⁷ assembly.

The cubical interface makes the left product's geometric cube explicit.
`sq_ap_path` preserves the specified path-algebra filler when mapping a
square. `sq_ap_nat_apD` identifies variation of that mapped square with
`sq_ap_nat`, retaining all four side-face computations.
`equiv_ap_naturality_cube` converts between dependent paths of mapped
path-algebra fillers and these cubes; `ap_naturality_cube_beta` computes the
image of the original dependent application. `left_product_cell` uses its
inverse on the actual naturality cube, not on an arbitrarily chosen cube.

`equiv_concat_Ap_cube` provides the complementary conversion for applying
a fixed homotopy to a varying path. It accepts a specified source square
and its beta witness. Its beta rule identifies the original dependent
application with `sq_ap_nat` on that square, using `cu_GGcccc_natural` to
retain both mapped-face comparisons. `right_product_cell` uses this inverse
with the actual multiplication square and mixed beta path. Thus both composite-product cubes
are now expressed using actual cubical naturality, with the original
composition adjustments still retained.

### First shared-face comparison

`left_product_cap_comparison` proves a 4-path for the geometric part of the
left product paired with the inverse right-translation part of `AL`. Both
use the same specified multiplication square `S = multiplication_square a b s t`.
Writing `V_cd(v) := ap (mu v) (jglue c d)`, it compares

```text
flip_lr (sq_ap_nat rho_c S) @lr sq_ap_nat V_cd S
```

with the naturality cube of `fun v => (rho_c v)^ @ V_cd(v)`. The expression
above suppresses the endpoint maps. The checked theorem retains both actual
converted cube inhabitants, the multiplication mixed beta witness, and all
four side-face adjustments supplied by `ap_nat_Vp`. Its generic 4-dimensional
pasting law is `sq_ap_nat_Vp` in `Cubical/PathCube.v`.

The two translation corrections can now be combined before taking any
further naturality.  Put

```text
eta_c,d(v) := (rho_c(v))^ @ ap (mu v) (jglue c d).
```

The generic lemma `transport_associator_normal_form` proves that transport of
`AL(x,y,c)` along `jglue c d` is

```text
(eta_c,d(mu x y))^ @ (E_c(x,y))^ @ ap (mu x) (eta_c,d(y)).
```

This is path induction on the free last-input path, not a diamond
comparison.  The checked `eta_square_beta` computes naturality of `eta` as
the horizontal pasting of inverse-translation naturality and the **transpose**
of `multiplication_square s t c d`.  Thus the inverse orientation is part of
the statement rather than silently corrected later.

The cubical operation `cu_swap_tb_fb` transposes that right-product cube,
and `sq_ap_nat_tr` computes the result on an actual naturality cube.
`right_product_cap_comparison` then combines this transposed cube with the
last inverse-translation cube using `concat_Ap_pp`.  Together with the
existing `left_product_cap_comparison`, both product--translation pairs are
identified with the two naturality cubes involving `eta`, retaining their
actual source squares and beta paths.  Finally,
`last_middle_transport_normal_form` applies the transport normal form before
naturality in the first input, and
`last_middle_transport_cell_normal_form` takes its actual dependent
naturality in the middle input.  This combines both pairs at the homotopy
level and leaves the diagonal-equivariance contribution between them.

The homotopy-first cancellation now also reaches the whole last face.
`transport_adjusted_naturality` is a generic path-inductive calculation:
it transports a naturality square while replacing its underlying homotopy
at the target, retaining the two endpoint homotopies and their dependent
paths.  Applying it to `AL`, `BL`, and `BR` gives

```text
eta_face_transport :
  transport (Gamma a b y) (jglue c d) (face_z a b y c)
  = eta_face a b c d y.
```

Here `eta_face` pastes `eta_last_middle` with the transported left and right
overlaps.  Its middle-input restriction is already the existing chosen
middle face:

```text
eta_face_middle :
  eta_face a b c d (joinl s) = face_y a b s (joinr d).
```

This proof uses the same `S7MiddleScalar.overlap` at both first-input
endpoints.  `eta_face_cell_beta` also computes middle-input naturality of
the complete `eta_face`; its center is `eta_last_associator_cell`, while its
outer cells are the actual dependent naturalities of the transported left
and right overlaps.  Thus the first-left and first-right adjustments are no
longer lifted manually through the whole pasting.

Following the relative-induction pattern used for join associativity,
`pathcube_ind_left` allows five faces to stay fixed while the sixth face
and its cube vary together. The contractible object is the pair of a lid
and its filling cube, not the type of cubes with all six faces fixed.
This is available for the remaining pasting calculations, not a proof of
`Mixed` by filler uniqueness.

The generic 4-dimensional theorem
`transport_adjusted_naturality_homotopic` now proves that compatibility,
including its proof term:

```text
eta_face_middle_transport :
  eta_face_middle
  = eta_face_transport^-1
      @ (map face_overlap @ apD face_y (jglue c d)).
```

Thus the transported first-left, first-right, middle, and overlap choices
have all reached the same whole-face normal form; no second `Mixed`
interface was introduced.

The whole-face calculation factors the original pasting, not a replacement
boundary. Suppress `a,b,t,d` and write

```text
e_s(c) := eta_edge a b s t c d : U_s = Phi_c
Phi_c  := eta_face a b c d (joinr t)
h(c)   := eta_face_transport a b c d (joinr t).
```

`pasting_eta_factor` proves `p_s(c) @ e_s(c) = h(c)`, where `h(c)`
is independent of `s`. `computed_pasting_eta_factor` proves the same
factorization for the existing `computed_pasting` and `eta_computed_edge`.
The latter edge's extra source adjustment cancels in each ratio, as checked
by `eta_computed_edge_ratio`.

**Endpoint independence is already available.** The 3-path

```text
r_c := (e_North(c))^ @ e_North(North) : Phi_c = Phi_North
```

uses only the existing unit-labelled edges. It is not sufficient to finish
`Mixed`: it identifies the endpoint faces, not the paths to those faces.

**The immediate open target is edge compatibility**, the 4-path

```text
e_s(c) @ r_c = e_s(North).                            (dagger)
```

The `s = North` case follows by cancellation. For arbitrary `s`, this says
that the comparison chosen using the unit-labelled edge agrees with the
comparison induced by the `s`-labelled edge. Equivalently, by `equiv_moveL_Vp` and
path inversion, the target is

```text
(e_s(c))^ @ e_s(North)
  = (e_North(c))^ @ e_North(North).                   (edge ratios)
```

`equiv_mixed_eta` is the checked equivalence from this edge-ratio equation
to the original `Mixed`. Its proof uses `equiv_pasting_factors` to cancel
the common `h(c)` and `h(North)` in the existing expanded equation, using
all four `computed_pasting_eta_factor` witnesses. No further expansion of
the five-cube pasting is needed for this reduction.

A sufficient geometric construction is a comparison of the whole sections

```text
K(y) : eta_face a b c d y = eta_face a b North d y
```

with the **specified** left-boundary computation

```text
K(joinl s)
  = eta_face_middle a b s c d @ (eta_face_middle a b s North d)^.
```

`eta_edge_comparison_of_section` checks that these two inputs imply
(dagger), by dependent naturality along `jglue s t`. Naturality for
`s = North` identifies `K(joinr t)` with the already chosen `r_c`.
An arbitrary section comparison without this left-boundary computation
would not suffice. The required compatible section is still not constructed.

A comparison with naturality of `cd_assoc_rr t d` may help construct it,
but must retain compatibility with the chosen middle-face witnesses; an
isolated equality at `joinr t` is not an equivalent substitute.

Two reusable pieces of this comparison work are now checked:

- `adjusted_naturality_comparison` and
  `adjusted_naturality_comparison_homotopic` in
  [`Types/Paths.v`](../theories/Types/Paths.v) compare the central homotopies
  while retaining the endpoint adjustments, and compute the resulting
  comparison against the ratio of the two specified overlap witnesses.
  Neither lemma requires function extensionality.
- `diamond_susp_functor` in
  [`Join/SuspDiamond.v`](../theories/Homotopy/Join/SuspDiamond.v) proves that
  a suspension map preserves the actual canonical diamond, including its
  pole computations and meridian twist. This applies to suspension
  conjugation and complements `diamond_susp_turn`; it does not by itself
  compare the selected diagonal-equivariance homotopies.

The actual right–right diamond rotation is now checked in
[`Direct/RightRight.v`](../theories/Homotopy/HSpaceS7/Direct/RightRight.v).
For a circle scalar `u`, put `L_u(z) = (-u)*z` and `R_u(z) = u*z`.
`S7RightRight.rotation` proves

```text
join_zigzag_filler L_u R_u (rot_p u) (rot_q u) (rot_r u) (rot_s u)
  (diamond_susp (conj u))
  = join_diamond_rotate (diamond_susp u).
```

The four boundary paths have types `L_u South = u`, `L_u (conj u) = South`,
`R_u North = u`, and `R_u (conj u) = North`. The rotation reverses both
vertex pairs. The proof retains the actual North and South computations;
at South, it explicitly computes `rot_p South = rot_q South = 1`, using
the chosen inverse and sign laws. The meridian case uses the general
`join_zigzag_filler_rotate_twist`, which eliminates a **free parameter
path**, not a fixed join glue or chosen filler. That lemma has independent
parameter/source/target universes and requires no function extensionality.

The rotation has now been applied to the two actual multiplication fillers.
`S7RightRightMiddle.diamond_standard` retains the four original scalar
associator witnesses. `middle_r_glue_glue` converts this comparison using
both mixed beta rules, the inverse-path computations, and all four chosen
side faces. It constructs

```text
middle_r t x z : mu (mu x (joinr t)) z = mu x (mu (joinr t) z).
```

Its first-input constructors are the original `cd_assoc_first_lr/rr`.
Its two last-input columns are compared with `cd_assoc_rl/rr`, with
reflexive first-input constructor computations. The overlap with `AL`
retains exactly `cd_assoc_last_joinl_first_lr/rr`; the generic
`translated_turn_parameter_comparison` supplies its glue without changing
those triangle witnesses.

Transporting that overlap through `jglue c d` and using the computed right
column now proves

```text
S7DirectGluing.eta_associator_rr c d t x :
  eta_associator c d x (joinr t) = cd_assoc_rr t d x.
```

The final join induction uses `eta_overlap_l/r` themselves as its point
clauses. Consequently `eta_associator_rr_beta_joinl` and
`eta_associator_rr_beta_joinr` are both `idpath`. The spheres stay small,
and the comparison shares the existing proof universe `u`.

This completes the right-middle comparison, **not** the general `Mixed`
filler. Compatibility across the middle-input glue, with the selected
middle-left comparison and corner proof terms, remains open.

### Retaining both computed middle faces

`Direct/MiddleComparison.v` now carries the whole `middle_r` section
through the transport calculation. Its `eta_overlap_mr` has the original
`eta_overlap_l/r` point clauses without replacing the last-right column
by `cd_assoc_rr`. The proved `eta_right_transport` retains its specified
last-left overlap and the dependent path of the right-middle face.

Write `M(s,c)` for `middle_pasting a b s t c d`, with the other labels
fixed. This transports the last-left rectangle between `middle_l` and
`middle_r` through `jglue c d`. `middle_pasting_compute` expands it as

```text
left_middle_cell^ @ transport(last_left_rectangle) @ right_middle_cell.
```

Both cells include their original outer recursor beta paths; the right
cell contains `middle_r_glue_glue` and hence the actual rotated
multiplication diamond. The four-dimensional
`computed_pasting_right_factor` attaches this rectangle to the **original**
`computed_pasting`, retaining its source adjustment, and identifies the
result with the transported right overlap followed by that right cell.

The remaining equation is now also expressed as

```text
M(s,c)^ @ M(s,North) = M(North,c)^ @ M(North,North).
```

`equiv_mixed_middle_pasting` proves that this is equivalent to the original
`Mixed`. The equation itself is still open. In particular, neither
`M(s,c) = M(s,North)` nor uniqueness of the join-valued cells is assumed.
All these comparisons retain the shared proof universe `u`.

The proof of the existing `equiv_mixed_middle_pasting` now cancels both
common right factors before doing any further geometry. With

```text
P_s(c) = transport(cap_s(c)) @ left_cell_s(c)
R(c)   = transport(right_overlap(c)) @ right_cell(c),
```

`middle_pasting_compute` gives `M(s,c) = P_s(c)^ @ R(c)`. The proof keeps
`right_cell` and `right_overlap` opaque, cancels the common `R(c)^` and
`R(North)`, and uses the existing `pasting_expansion` to return to the
original `computed_pasting`. There is no new public `Mixed` interface.
The right-middle rotation is therefore not expanded again.

The surviving left-middle cell now exposes its geometric input through
`S7MiddleScalar.middle_l_glue_glue_from_diamond`; the original
`middle_l_glue_glue` still supplies exactly `S7MiddleScalar.diamond`, with
unchanged side computations.

New scalar coherence lemmas compare balancing followed by diagonal
translation with the reverse order, including the required reassociations.
`join_zigzag_filler_change_square` lifts these commuting scalar squares to
the **complete** filler data: a dependent sum of the four vertices and the
chosen filler. It does not truncate the join or eliminate its fixed filler.
This gives `S7MiddleScalar.diamond_translate_square` for any supplied circle
diamond.

The balanced and diagonal comparisons now form a completed square.
`diamond_path_change` retains the original standard balanced boundaries;
`diagonal_path_translate` retains the parameter-independent diagonal
boundaries; and `translate_path_change` retains the actual postcomposition
beta path. The intermediate `diamond_translate_square_normalized` still
has one elementary edge and two explicit composition adjustments.

`diamond_postcompose_change` identifies that fourth edge with actual
postcomposition of the original balanced comparison, using naturality of
`join_zigzag_filler_compose` on complete input data. Cancelling the
composition adjustments gives `diamond_translate_square_postcompose`:

```text
diagonal_top @ ap Post_r balanced
  = (balanced_scaled @ reassociation) @ diagonal_bottom.
```

Here `Post_r` is `functor_join_filler_data (.*r) (.*r)`, which maps both
vertices and fillers. There is no elementary surrogate edge or leftover
composition-beta endpoint in this equation. It holds for any supplied
circle diamond, and needs no new diamond symmetry.

The input-data computation retains the original recursor homotopy and
its zigzag beta paths. `equiv_naturality_loop` and
`naturality_path_image_loop_compute` give the higher compatibility of its
nullhomotopy with those specified edge computations. Consequently,
`join_zigzag_filler_homotopic_refl` proves the identity law for the **whole
filler comparison**, not merely its underlying homotopy.
`join_zigzag_filler_change_path_refl` and
`join_zigzag_filler_change_path_ap` compute the complete-data path.
`join_zigzag_filler_change_path_compose` proves composition naturality by
induction on the free map homotopies, parameter, and boundary paths, while
keeping the actual composition witness opaque. The arbitrary supplied
diamond family is never eliminated. The regression
`filler_witness_unchanged` still proves by `idpath` that the original
filler-comparison witness has not been replaced.

`Types.Sigma.path_sigma_fiber_square` extracts the fiber comparison over a
prescribed scalar square, assuming only that comparisons of the two base
paths form a proposition. `middle_l_glue_glue_diagonal` now applies this
to the completed total-data square, cancels its diagonal/reassociation
suffix, and lifts the resulting comparison through
`middle_l_glue_glue_from_diamond`. Thus its target is the **original
middle-left cube**, with all its side computations retained. Only the
scalar squares are identified using 1-truncation; no join-valued filler
or higher filler comparison is truncated.

The diagonal edge now also attaches to the selected `AL` cap inside the
original expanded pasting. `cd_op_diagonal_equivariance_glue_glue_from_diamond`
exposes the geometric input of the existing diagonal cube, without changing
its four sides or mixed beta computations. The original wrapper still
supplies exactly `cd_op_diamond_diagonal`; the full historical proof body
is checked against it by `idpath` in `S7DiagonalWitnessCheck.v`.

`last_associator_cell_from_diagonal`, `last_face_cell_from_diagonal`, and
`computed_pasting_from_diagonal` expose this same input through the existing
normalization. Both specified `AL` overlap eliminators, the middle overlap,
all outer beta paths, and the transport-interchange expansion remain fixed.
The old definitions supply the original diagonal comparison, with no
change of their chosen witnesses.

`computed_pasting_balanced_diagonal` uses the actual total-data square to
replace its bottom diagonal edge by

```text
(balanced_scaled @ reassociation)^ @ (diagonal_top @ ap Post_r balanced).
```

It extracts the fiber comparison over a prescribed scalar square and maps
it through the entire cap construction to obtain an equality with the
**original `computed_pasting`**, for any final right label. This is a checked
attachment to that cap, not merely an equality of its geometric endpoints.

The arbitrary final-right label now has a checked geometric comparison.
For fixed `s,t,c,d`, put

```text
c' := conj s * ((-d) * conj t)
e  := (s*t)*c.
```

`cd_op_diamond_pullback` applies the inverse left-scalar action to the
**original inner multiplication diamond** and retains its scalar boundary
corrections. It gives the actual filler

```text
H : zigzag c c' d = zigzag c c' e.
```

This holds for any associative commutative spheroid with a supplied
diamond; it needs no truncation, function extensionality, or new diamond
symmetry. In particular, it does not invent a scalar path `d = e`.

`computed_pasting_inner_diamond` applies dependent naturality to this
square, using the existing `transported_face_cell_beta` on all four edges.
For any selected middle row `v`, let `S_v(z)` be the ratio

```text
computed_pasting a b v t c z @ (computed_pasting a b v t c' z)^
```

transported back along `(jglue c' z)^`, with its specified `transport_pp`
and `transport_Vp` corrections. The theorem proves

```text
S_v(d) = transport2 (Gamma a b (joinr t)) H (face_z a b (joinr t) c)
           @ S_v(e).
```

The cap adjustments, all five computed side cells, and the original
transport-interchange computation remain present. The underlying generic
`apD02_pV_beta` permits arbitrary dependent fibers and both specified
endpoint adjustments. It retains the supplied source square rather than
identifying fillers by truncation.

Since the correction is independent of `v`,
`computed_pasting_inner_diamond_difference` cancels it and proves

```text
S_s(d)^ @ S_North(d) = S_s(e)^ @ S_North(e).
```

The full surviving pasting-ratio equality is still open. The remaining
difference at the aligned right label `e` has not been shown to vanish,
and the additional left vertex `c'` has not been replaced by the original
unit anchor. Those comparisons must still retain the selected balanced
cells, cap witnesses, and beta paths. Neither the cap identity nor this
transfer identity alone establishes `Mixed` or unconditional S7.

For one **stronger, sufficient strategy**, a comparison
`Q x y : eta_associator c d x y = eta_associator North d x y`
would induce `K` using `adjusted_naturality_comparison`. It must come with
left, right, and middle computations `Ql`, `Qr`, `Qm` equal to the
corresponding ratios of `eta_overlap_l`, `eta_overlap_r`, `eta_overlap_m`.
The corner proof terms must also agree:

```text
Ql a (joinl s) = Qm s (joinl a)
Qr b (joinl s) = Qm s (joinr b).
```

These are not consequences of merely having matching endpoint types.
[`test/Homotopy/HSpaceS7DirectMiddle.v`](../test/Homotopy/HSpaceS7DirectMiddle.v)
checks that these explicitly supplied data give the **chosen** `K` left
boundary and then the original `Mixed`. The whole relative geometric data
`Q, Ql, Qr, Qm` and the two corner coherences have not been constructed.
The right-middle restriction of `Q` is now available as the ratio of the
two `eta_associator_rr` comparisons, but its compatibility with the
left-middle restriction across the join glue is still missing. This
strategy has not been proved equivalent to the original edge goal.

There is still no checked reduction of the remaining compatibility to
`eh_V_gen` or another existing cubical law. In particular, applying
`eh_V_gen` would require identifying its specific interchange and
unitor-naturality inputs with the retained diagonal/η/overlap cells, not
merely matching their boundaries.

This is the genuinely new iteration problem: the original
Buchholtz--Rijke Cayley--Dickson development constructs the H-space on S3
and explicitly leaves iteration toward S7 to additional coherent
imaginaroid data.  Consequently the remaining equation should not be
expected to follow from the ordinary H-space or scalar laws alone.
Moreover, `Mixed` asks to extend the **particular** `BL`, `BR`, `BM`, `AL`,
and overlap witnesses retained here.  Bare existence of some associator
would not automatically imply this prescribed filler without comparisons
to those choices; failure of the current boundary calculation would not
by itself prove that the multiplication is nonassociative.

## 1. Earlier scalar-loop proof structure

```text
m_ll, m_lr, m_rl, m_rr                                  proved
        │
        ├── loop_row_l, loop_row_r                     existing row_loop families
        │       └── loop_y_joinl, loop_y_joinr          dependent glue comparisons
        │
        ├── loop_x_joinl                               proved
        ├── loop_x_joinr                               transported from proved sides
        │
        └── loop_mixed                                 OPEN 5
                │
          loop_column; all_scalar_loops                join induction in x,y
                │
             last_glue                                 circle induction in c
                │
             associator                                join induction in z
                │
      associative_cd_s1_from_gaps                       reverse paths
                │
          hspace_s7_from_gaps                           double and transfer
```

All assembly steps after the remaining hypothesis are implemented. This is still a
**conditional** construction, not an unconditional `hspace_s7` instance.

The notation in the outline is:

```text
C           = Sphere 1
J           = Join C C
mu          = the existing cd_op on J
P(x,y,z)    = (mu (mu x y) z = mu x (mu y z))
AL x y c    = cd_assoc_last_joinl x y c
T x y d c   = transport (P x y) (jglue c d) (AL x y c)
AR x y d    = T x y d North
ell         = merid North @ (merid South)^
M x y d     = (ap (T x y d) ell = 1)
```

`loop_row_l` and `loop_row_r` directly specialize the `row_loop` families in
`S7LeftScalar` and `S7RightScalar` to `ell`, with the canonical diamond.
They are not reconstructed by join induction. Their constructor values are
still definitionally `m_ll`, `m_lr`, `m_rl`, and `m_rr`. The right row's glue
comparison is definitionally `loop_y_joinr`; the left agrees with
`loop_y_joinl` after cancelling its reflexive endpoint adjustments.

`AR` is the transported right choice, not the older symmetry-based
`cd_assoc_last_joinr`. This makes the whole `jglue North d` boundary
reflexivity. There is no obligation to identify these two right choices for
arbitrary `d`.

The remaining hypothesis is a family in `d`. Consequently, once it
is proved, the second-circle coherence is simply
`apD (all_scalar_loops x y) ell`; it is not an additional missing input.

## 2. Reusable proof machinery

### Double-join homotopies

[`Homotopy/Join/Rec2.v`](../theories/Homotopy/Join/Rec2.v) provides
`Join_ind2_FlFr`. For arbitrary maps

```text
f,g : Join A B -> Join C D -> P
```

its inputs are four vertex homotopies, four edge squares, and their mixed
cube. It assembles a homotopy while retaining the selected vertex and edge
computations. The cube is a genuine hypothesis: four sides alone do not
supply it. The construction requires neither truncation nor extensionality.

This is an induction/comparison interface, not yet a bundled recursion-data
category or a framework of twist operations. It is already used by the
balanced scalar law below.

### Converting geometric cubes to dependent transport

`transport_naturality_square` and `transport_naturality_square_beta` in
[`Types/Paths.v`](../theories/Types/Paths.v) handle arbitrary squares of
homotopies. The latter separates:

- the eight selected edge computations;
- the two mixed computations;
- the two homotopy computations;
- the actual geometric cube.

It handles the final bookkeeping in `cd_op_diagonal_equivariance_glue_glue`,
`S7LeftScalar.first_l_glue_glue`, `S7MiddleScalar.middle_l_glue_glue`, and
`S7RightScalar.first_r_glue_glue`. The existing side witnesses are retained.
The right row additionally uses `inverse_mixed_beta`,
`concat_pV_cube_unit_inverse`, and `join_zigzag_filler_cube_inverse` to keep
the reversed direction and double-inverse computations explicit.

### Comparing composites of join maps

`JoinMapCoherence.translated_composite_comparison` compares a translated
composite with a single join map. Its input comparisons are scalar paths;
its output retains the specified join triangles at the corners. The
`combine` and `split` templates retain the existing beta computations.
This supplies the overlap for the middle-left associator.

`JoinMapCoherence.translation_turn_comparison` supplies the corresponding
comparison when a map exchanges the join factors. Its `turn_commute` and
`commute_turn` templates retain the original reversed-glue computations;
`compare_turn_l` retains the chosen left-copy triangle. This supplies the
right-row overlap with exactly the original `rl` and `rr` comparisons.

### Closing nullhomotopies around loops

`ap_loop_nullhomotopic` in
[`Homotopy/NullHomotopy.v`](../theories/Homotopy/NullHomotopy.v) extracts the
common loop-closing calculation. The four original corner witnesses, the
two rows, and the left column all use it. This avoids repeatedly unfolding
that calculation when comparing their values.

## 3. Former OPEN 1 is proved

[`HSpaceS7/LeftScalar.v`](../theories/Homotopy/HSpaceS7/LeftScalar.v) constructs
`first_l D s y z`, an associator with first argument `joinl s` and both later
arguments arbitrary. It works for any supplied circle diamond `D`.

Its constructor rows are the original `cd_assoc_first_ll` and
`cd_assoc_first_lr`. The development proves:

1. left translation of the actual diamond, including its four boundaries;
2. agreement of the induced scalar boundaries with the selected corner paths;
3. the two mixed beta equations and the four selected side comparisons;
4. the double-join assembly;
5. the overlap with the fixed last-left associator.

The overlap is

```text
Q s y c : AL (joinl s) y c = first_l D s y (joinl c).
```

On constructors it is exactly the original
`cd_assoc_last_joinl_first_ll` and `cd_assoc_last_joinl_first_lr`.
`JoinMapCoherence.translation_comparison` supplies its glue calculation from
comparisons of scalar paths, without comparing arbitrary join fillers.

The resulting nullhomotopy is

```text
K s y d c := ap (transport (P (joinl s) y) (jglue c d)) (Q s y c)
              @ apD (first_l D s y) (jglue c d).
```

Closing `K` around a scalar loop gives `row_loop`. Its constructor values are
definitionally the original `ll` and `lr` loop witnesses. Applying `apD` in
`y` gives `loop_y_joinl` for every scalar loop, not just `ell`.

The outline and its tests share the circle witnesses used by this result.
The tests also check that these are definitionally the usual circle data.
Sharing their universe instances avoids expensive conversions between
independently instantiated truncation proofs.

## 4. The balanced scalar law is proved

[`HSpaceS7/Balanced.v`](../theories/Homotopy/HSpaceS7/Balanced.v) develops a
second full scalar-action comparison. Write

```text
L_s = functor_join (s *.) (conj s *.)
R_s = functor_join (.* s) (.* s).
```

Then `cd_op_balanced` proves

```text
mu (R_s x) y = mu x (L_s y).
```

The theorem is general: for any truncation level `n`, it takes an associative,
commutative scalar spheroid, a chosen diamond, `n`-connectedness, and
`(n+1)`-truncation of the scalars. The circle uses `n = 0`. It requires no
additional diamond coherence and no extensionality. It is polymorphic in one
universe, with the double in that same universe.

The key parameter calculation is

```text
cd_diamond_parameter (a*s) (b*s) c d
  = cd_diamond_parameter a b (s*c) (conj s*d).
```

Together with comparisons of the two diamond mapping functions, this lets
`join_zigzag_filler_change` compare the actual fillers. There is no reflected
diamond. The scalar path families are `n`-truncated, so `n`-connectedness
removes irrelevant labels from the scalar boundary paths. `Join_ind2_FlFr` then assembles the
homotopy from those boundaries and the filler comparison.

Combining this with right scalar translation gives

```text
cd_assoc_middle_joinl n x s y
  : mu (mu x (joinl s)) y = mu x (mu (joinl s) y).
```

Both outer arguments are arbitrary. The circle construction below chooses
its rows separately, rather than assuming that this general homotopy has
the original scalar-corner computations.

## 5. Completing boundary comparisons

### Former OPEN 3 is proved

[`HSpaceS7/MiddleScalar.v`](../theories/Homotopy/HSpaceS7/MiddleScalar.v)
constructs `middle_l D s x z` with arbitrary outer arguments and exactly the
original `cd_assoc_first_ll` and `cd_assoc_first_rl` rows.

It uses the raw right translation, with labels `(a*s,s*b)`, and the balanced
parameter comparison. The induced boundary paths are identified with the
old scalar associativity paths. The actual mixed comparison is then
converted using all four specified side computations.

`overlap D s x c` identifies its last-left restriction with
`AL x (joinl s) c`. Its constructors are definitionally the original
`cd_assoc_last_joinl_first_ll` and `cd_assoc_last_joinl_first_rl`.
`JoinMapCoherence.translated_composite_comparison` supplies the glue.

Closing the resulting nullhomotopy gives `column_loop`. Its constructor
values are definitionally `m_ll` and `m_rl`, so dependent application in `x`
gives `loop_x_joinl`. This works for every scalar loop and every supplied
circle diamond, not just the canonical one.

### Former OPEN 4 is obtained by transport

After the two rows are assembled, `XGlue a a' d y` is the family of
comparisons between their transported values. Choose

```text
loop_x_joinr a a' b d
  := transport (XGlue a a' d) (jglue North b)
       (loop_x_joinl a a' North d).
```

This has precisely the required `lr` and `rr` endpoints. Both rows are now
proved, so this construction has no missing-proof parameter. No separate
right-middle associator is needed for this transported choice; the new
right-middle associator above is used for the direct η comparison. The `b = North` case of
OPEN 5 is reflexivity.

### Former OPEN 2 is proved

A geometric ingredient is now proved in
[`Join/SuspDiamond.v`](../theories/Homotopy/Join/SuspDiamond.v).
`diamond_susp_turn` compares the actual suspension diamond after turning
its two join factors and reversing the suspension poles. It works for any
map between the suspension bases and requires no extensionality.
Specialized to suspension negation, it gives

```text
join_diamond_turn (-) (-) (cd_diamond_susp t) = cd_diamond_susp (-t).
```

The vertical and horizontal pole fillers are interchanged, and
`join_diamond_turn_twist` proves compatibility with the specified meridian
computation. The canonical diamond's definition has moved into this
geometric file; the Cayley-Dickson instance still uses exactly that filler.
`apD_composeD` supplies the reusable fiberwise dependent-application rule.

The comparison with the **actual multiplication filler** is now proved in
[`HSpaceS7/RightScalar.v`](../theories/Homotopy/HSpaceS7/RightScalar.v).
Write `L_s(t) = t*s`, `R_s(t) = (-t)*conj s`, and
`D(a,b,c,d) = cd_op_diamond a b c d`. Left multiplication by `joinr s`
is the turn with these two maps. Its parameter identity is

```text
cd_diamond_parameter ((-b)*conj s) (a*s) c d
  = -cd_diamond_parameter a b c d.
```

`map_l` and `map_r` compare the complete mapping functions after negation.
Together with the canonical turn law they give `S7RightScalar.diamond`:

```text
transport (e10,e01; e00,e11)
  (join_diamond_turn L_s R_s (D(a,b,c,d)^))
  = D((-b)*conj s, a*s, c,d)^.
```

All four boundary paths are defined explicitly. They run from the
translated output vertices to the new multiplication vertices, opposite
to the desired associator's orientation. The theorem works for any
suspension of an imaginaroid with associative, commutative scalar
multiplication; it needs neither extensionality nor scalar truncation.
It uses the canonical diamond, not an unproved symmetry of an arbitrary
supplied diamond.

The supporting comparisons are reusable:

- `join_turn` and `join_diamond_turn` now take two independent scalar maps;
- `Join_rec_postcompose_filler` works for arbitrary intermediate recursor
  edges, including reversed glues, and also replaces the specialized proof
  of `join_zigzag_filler_compose`;
- `join_diamond_turn_map`, `join_diamond_map_turn`, and
  `join_diamond_turn_homotopic` commute turns with maps and map homotopies;
- `join_diamond_turn_compare` retains all eight chosen boundary
  identifications and the actual target-filler comparison;
- `turn_filler_beta` computes the inverted filler after a turn, retaining
  `ap_V`, `inv_V`, and the required `inverse_natural` orientation;
- `join_zigzag_filler_V` and `cd_op_diamond_V` retain the specified boundaries
  when switching the filler orientation.

The circle-specific assembly is now complete:

1. `standard_00`, `standard_01`, `standard_10`, and `standard_11` compare the
   induced boundaries with the original scalar witnesses. These are
   equalities of scalar paths, not assertions that join fillers are unique.
   The unit calculations retain
   `rightidentity_s1 South = merid South` and
   `parameter North North North North North = merid North`.
   Negation and the mixed boundary computations then give the required
   cancellations; they are not all reflexivity.
2. `diamond_standard` reverses and reindexes the actual filler comparison.
   `first_r_glue_glue` converts it using the two actual mixed beta rules and
   all four specified side faces, including `ap_V`, `inv_V`, and
   `inverse_natural`.
3. `first_r s y z` assembles the right-copy associator with both later
   arguments arbitrary. Its constructor rows are definitionally the original
   `cd_assoc_first_rl` and `cd_assoc_first_rr`.
4. `overlap s y c` compares `AL (joinr s) y c` with
   `first_r s y (joinl c)`. The general turn-composite comparison supplies
   its glue, while its constructors are exactly
   `cd_assoc_last_joinl_first_rl` and `cd_assoc_last_joinl_first_rr`.
5. Closing the resulting nullhomotopy gives `row_loop`. Its constructor
   values are definitionally `m_rl` and `m_rr`. Dependent application in `y`
   gives **`loop_y_joinr`**, for every scalar loop `p : c = c`.

The old scalar witnesses are now named `cd_assoc_ll_scalar_r`,
`cd_assoc_lr_scalar_r`, `cd_assoc_rl_scalar_r`, and `cd_assoc_rr_scalar_r`
in `CayleyDickson.v`. Their proof expressions are unchanged; sharing those
terms avoids duplicating long boundary calculations during conversion.
The right-row constructions, including the mixed comparison, are
transparent (`Defined`), and the regression tests check transparency as
well as the constructor and glue computations.

Unlike the left and middle-left rows, this proof uses a turn law of the
**canonical** diamond. It does not assert the result for an arbitrary
supplied diamond. Nor does it infer the chosen coherence from
`cd_chi ~ id`.

### OPEN 5: compatibility of the actual four sides

Only choose this comparison after the side constructions are fixed. The
family `XGlue` contains the chosen y-row proofs, so its dependent glue case
must match those proofs and the two chosen x-side proofs.

Normalize the dependent transports using the original `row_loop` families
and their chosen overlap computations before applying a generic cube lemma.
The rows' dependent applications need no additional `Join_ind_beta_jglue`
comparison. `cd_op_diagonal_equivariance_glue_glue` concerns equivariance, not the loop
family `M`; using it requires the conversion and boundary matching.

If a geometric symmetry remains, state it with the full boundary and the two
actual fillers before attempting it. For the canonical suspension diamond,
the available computations are the horizontal/vertical pole fillers and
`diamond_twist` on meridians. Any further compatibility must be proved.

## 6. Guardrails and regression checks

- Scalar truncation does not identify join-valued fillers or loop-proof
  comparisons.
- Connectedness does not extend arbitrary calculations at the unit into such
  join-valued families.
- Free paths may be eliminated in general diagram lemmas. Fixed circle loops,
  join glues, and constrained chosen diamonds may not be eliminated as though
  their boundaries were free.
- Join associativity is an equivalence between iterated joins; the domain of
  the multiplication associator is a product of joins. Its twist construction
  is a model for organization, not an immediate proof of this associativity.
- Do not silently change corner witnesses. Either preserve their computations
  or supply the comparisons needed by the downstream construction.

Tests of the actual implementations live in:

- `test/Homotopy/Join/Rec2.v`: arbitrary corner and edge computations, dependent
  extension from compatible left faces, independent universes, the
  specified intersection, and the exact mixed beta rule for nested induction;
- `test/Basics/PathGroupoids.v`: fiberwise binary application with independent
  universes, transposition of application naturality, and cancellation of a
  common change of zigzag center;
- `test/Cubical/PathCube.v`: relative cube induction, retained horn fillers,
  mapped-square naturality, specified source squares and beta witnesses,
  arbitrary chosen 3-paths, both equivalence round trips, and shared-face
  pasting with arbitrary source squares (including retained 2-loops);
- `test/Types/Paths.v`: transport conversions, five-face square filling,
  arbitrary retained 2-loops, and chosen cube pasting in dependent targets;
- `test/Homotopy/NullHomotopy.v`: the exact loop-closing witness without
  extensionality;
- `test/Homotopy/HSpaceS7Balanced.v`: general scalars, supplied diamond, four
  corner computations, actual filler comparison, and circle specialization;
- `test/Homotopy/HSpaceS7LeftScalar.v`: overlap and original loop witnesses;
- `test/Homotopy/HSpaceS7MiddleScalar.v`: middle associator, mixed beta,
  overlap, and the original column-loop witnesses;
- `test/Homotopy/Join/MapCoherence.v`: composite and turn comparison templates;
- `test/Homotopy/Join/SuspDiamond.v`: pole computations, two-map turns,
  composition with arbitrary boundaries, and the actual canonical diamond;
- `test/Homotopy/Join/Core.v`: general recursor postcomposition and mapped
  filler inversion with independent universes;
- `test/Homotopy/HSpaceS7RightScalar.v`: general scalar maps, the actual
  suspension filler comparison, original right-row and overlap witnesses,
  mixed beta computation, transparency, and arbitrary scalar loops;
- `test/Homotopy/CayleyDickson.v`: shared scalar witnesses with unchanged
  constructor computations and a supplied diamond;
- `test/Homotopy/HSpaceS7Direct.v`: the two whole faces, their actual
  intersection comparison, original first-left/right/middle mixed cells,
  normalized and expanded mixed boundaries, exact interchange expansion,
  chosen cubes, round trips, unit cases, conditional direct gluing, retained
  first associators, and second doubling;
- `test/Homotopy/HSpaceS7Outline.v`: the earlier one-hypothesis loop assembly,
  direct reuse of the original `row_loop` families, and its beta rules through
  the conditional S⁷ H-space.

Validate with `dune build`, `dune build test/`, and finally `dune test`, which
also runs `coqchk`. Full doubled associativity and the unconditional S⁷
H-space remain unproved.
