# S⁷: scalar actions and the four remaining comparisons

The executable assembly is `S7ProofOutline` in
[`theories/Homotopy/HSpaceS7.v`](../theories/Homotopy/HSpaceS7.v).
Its remaining hypotheses are **OPEN 2–5**. Former OPEN 1 is now supplied by
`S7LeftScalar.loop_y_joinl`, not by a section hypothesis.

The associativity required here is that of the **circle double**, which is
pointedly equivalent to S³. The resulting structure on S⁷ only needs to be an
H-space. No associator pentagon is required for the second doubling.

## 1. Current proof structure

```text
m_ll, m_lr, m_rl, m_rr                                  proved
        │
        ├── loop_y_joinl                               proved
        ├── loop_y_joinr                               OPEN 2
        │       └── loop_row_l, loop_row_r
        │
        ├── loop_x_joinl                               OPEN 3
        ├── loop_x_joinr                               OPEN 4
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

All assembly steps after the four hypotheses are implemented. This is still a
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

All four remaining hypotheses are families in `d`. Consequently, once they
are proved, the second-circle coherence is simply
`apD (all_scalar_loops x y) ell`; it is not a fifth missing input.

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

It replaces the final repeated bookkeeping block in both
`cd_op_diagonal_equivariance_glue_glue` and
`S7LeftScalar.first_l_glue_glue`. The existing side witnesses are retained.

### Closing nullhomotopies around loops

`ap_loop_nullhomotopic` in
[`Homotopy/NullHomotopy.v`](../theories/Homotopy/NullHomotopy.v) extracts the
common loop-closing calculation. Both the four original corner witnesses and
the new left row use it. This avoids repeatedly unfolding that calculation
when comparing their values.

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

Both outer arguments are arbitrary. This is new partial associativity, but
**it has not yet closed OPEN 3**: its choices still need to be compared with
the choices of the fixed loop outline.

## 5. Next mathematical work

### OPEN 3: use the middle-scalar associator

Prefer comparing partial associators to expanding proofs of loop vanishing.
The new middle-scalar associator gives a candidate family for the x-row with
middle argument `joinl s`.

The required work is to compare its restriction at the last left copy with
`AL x (joinl s) c`, including the existing corner comparison witnesses.
The balanced construction uses its induced scalar boundary paths; it does
not assert that its rows are the original `cd_assoc_first_ll` and
`cd_assoc_first_rl`. Either construct the middle associator with those rows,
or prove the row comparisons and their glue computations first.

After a compatible overlap is obtained, assemble nullhomotopy data and only
then apply `ap_loop_nullhomotopic`. Check that the resulting endpoint loop
proofs are the original `m_ll` and `m_rl`.

### OPEN 2 and OPEN 4: right-copy comparisons

Right-copy scalar translations involve `cd_chi` and reversed join glues.
A promising next reusable result would describe a rotation or twist on the
complete multiplication diagram, with its chosen boundaries and filler.
The fact that `cd_chi` is homotopic to the identity does not automatically
supply compatibility with the chosen scalar-action witnesses.

Retain `ap_V`, `inverse_natural`, and the mixed recursor beta rules. Do not
regard either right-copy case as a formal renaming of a left-copy proof.

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
- `test/Homotopy/HSpaceS7Outline.v`: the four-hypothesis assembly and its beta
  rules through the conditional S⁷ H-space.

Validate with `dune build`, `dune build test/`, and finally `dune test`, which
also runs `coqchk`. Full doubled associativity and the unconditional S⁷
H-space remain unproved.
