# S⁷: scalar actions and the remaining mixed comparison

The executable assembly is `S7ProofOutline` in
[`theories/Homotopy/HSpaceS7.v`](../theories/Homotopy/HSpaceS7.v).
Its sole remaining hypothesis is **OPEN 5**. Former OPEN 1, OPEN 2, and OPEN 3
are supplied by `S7LeftScalar.loop_y_joinl`, `S7RightScalar.loop_y_joinr`, and
`S7MiddleScalar.loop_x_joinl`. Former OPEN 4 is constructed by transport;
it is not an independent input. The right row uses the actual canonical
suspension diamond and retains the original corner loop witnesses.

The associativity required here is that of the **circle double**, which is
pointedly equivalent to S³. The resulting structure on S⁷ only needs to be an
H-space. No associator pentagon is required for the second doubling.

## 1. Current proof structure

```text
m_ll, m_lr, m_rl, m_rr                                  proved
        │
        ├── loop_y_joinl                               proved
        ├── loop_y_joinr                               proved (former OPEN 2)
        │       └── loop_row_l, loop_row_r
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
right-middle associator is constructed or needed. The `b = North` case of
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

Normalize the dependent transports and use the actual
`Join_ind_beta_jglue` computations before applying a generic cube lemma.
`cd_op_diagonal_equivariance_glue_glue` concerns equivariance, not the loop
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

- `test/Homotopy/Join/Rec2.v`: arbitrary corner and edge computations;
- `test/Types/Paths.v`: universe interfaces of the transport conversions;
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
- `test/Homotopy/HSpaceS7Outline.v`: the one-hypothesis assembly and its beta
  rules through the conditional S⁷ H-space.

Validate with `dune build`, `dune build test/`, and finally `dune test`, which
also runs `coqchk`. Full doubled associativity and the unconditional S⁷
H-space remain unproved.
