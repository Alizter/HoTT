# S⁷: executable outline and plan for the five missing proofs

The outline now lives **directly in
[`theories/Homotopy/HSpaceS7.v`](../theories/Homotopy/HSpaceS7.v)**, in
`Module S7ProofOutline`, `Section Construction`.

The five `Context` premises labelled **OPEN 1–5** are the unfinished lemmas.
Everything after them is executable Rocq code. In particular,
`S7ProofOutline.hspace_s7_from_gaps` constructs the H-space **conditional on those
five inputs**; it is not an unconditional instance.

[`test/Homotopy/HSpaceS7Outline.v`](../test/Homotopy/HSpaceS7Outline.v) uses the
actual library definitions and checks their corner, edge, mixed, and associator
computation rules. It no longer contains a second implementation of the outline.

## New checked progress toward OPEN 1

[`theories/Homotopy/HSpaceS7/LeftScalar.v`](../theories/Homotopy/HSpaceS7/LeftScalar.v)
now proves `S7LeftScalar.first_l D s y z`, an associator with first argument
`joinl s` and **both later arguments arbitrary**. It works for an arbitrary
supplied circle diamond `D`, not only the canonical suspension diamond.

Its constructor rows are exactly `cd_assoc_first_ll` and `cd_assoc_first_lr`.
The proof includes:

- the left-translation comparison of the actual diamond, including its four
  boundary paths;
- equality of those scalar boundary paths with the existing corner choices;
- the two mixed beta equations and all four selected face comparisons;
- the checked double join assembly.

`test/Homotopy/HSpaceS7LeftScalar.v` protects these computations, the explicit
chosen-diamond input, and the generic filler comparison's universe interface.

This does **not** yet close OPEN 1. The remaining overlap with the fixed `AL` is
stated explicitly below, and `S7LeftScalar.loop_y_joinl_from_overlap` checks that
it suffices for the **original** `ll` and `lr` loop proofs. That reduction is
conditional; all five original outline hypotheses remain unproved.

## 1. Read the proof from top to bottom

```text
m_ll, m_lr, m_rl, m_rr                                  proved
        │
        ├── loop_y_joinl, loop_y_joinr                  OPEN 1–2
        │       └── loop_row_l, loop_row_r
        │
        ├── loop_x_joinl, loop_x_joinr                  OPEN 3–4
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

The short names in the module mean:

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

`AL`, multiplication, the diamond, and the unit witnesses are unchanged. `AR` is
the transported right choice, **not** the older symmetry-based
`cd_assoc_last_joinr`. This makes the whole `jglue North d` boundary reflexivity;
there is no remaining task of matching the two right choices at arbitrary `d`.

The local `Let M` fixes one family with shared inferred circle data. It is a
definition, not another missing input.

Because all five open comparisons are families in `d`, assembling them gives
`forall x y d, M x y d` directly. The earlier targets (I) and (II) then are:

```coq
m0 x y := all_scalar_loops x y North
m1 x y := apD (all_scalar_loops x y) ell
```

Thus (II) is not a sixth hypothesis in this formulation. No rectangle criterion
or associator pentagon is needed after these five gaps are actually proved.

## 2. What the existing corner proofs contain

For a constructor pair `ij`, write:

- `alpha_ij := cd_assoc_first_ij a b`, the associator with its last join argument
  arbitrary;
- `q_ij c := cd_assoc_last_joinl_first_ij a b c`, the **specified** comparison of
  `AL` with `alpha_ij (joinl c)`.

The corresponding loop proof is made from this nullhomotopy:

```coq
K_ij c :=
  ap (transport (P x y) (jglue c d)) (q_ij c)
    @ apD alpha_ij (jglue c d).
```

Its type is `T x y d c = alpha_ij (joinr d)`. If `k` denotes that fixed right-hand
value, the loop-killing proof has the following actual shape:

```coq
ap_homotopic K_ij ell
  @ (((1 @@ ap_const ell k) @@ 1)
    @ ((concat_p1 (K_ij North) @@ 1) @ concat_pV (K_ij North)))
```

This is the construction in `cd_assoc_last_transport_loop_ij`. Consequently,
the edge proofs must track:

1. transport of `T` and its value at `North`;
2. the chosen `q_ij`, including its join triangles;
3. the `apD alpha_ij` term;
4. the naturality, constant-map computation, and cancellations closing the loop.

Knowing only that each corner sends `ell` to a trivial loop is insufficient to
identify these particular proofs.

## 3. Common preparation for OPEN 1–4

### 3.1 Normalize the dependent transport first

Fix `d` and the coordinate not being varied. Let `t` denote the varying join
coordinate and `e : t0 = t1` the relevant `jglue`. Set:

```text
B(t) = P(x(t),y(t),joinr d)
b(t) = T x(t) y(t) d North
L(t) = (b(t) = b(t))
u(t) = ap (T x(t) y(t) d) ell
v(t) = idpath (b(t))
M(t) = (u(t) = v(t)).
```

Apply the existing `transport_paths_FlFr_D` to obtain the **specified** comparison

```text
transport M e m
  = (apD u e)^ @ ap (transport L e) m @ apD v e.
```

The edge goal is equality of this expression with the destination corner proof.
`B(t)` varies with `t`, so treating these as paths in an unchanged fibre would
lose boundary transports. A generic calculation should be proved for an
arbitrary dependent family, not by eliminating the fixed join glue or diamond.

### 3.2 Compute how the scalar loop changes along the join edge

There is already a dependent comparison

```text
q_e(c) : transport B e (T x(t0) y(t0) d c)
           = T x(t1) y(t1) d c
```

obtained by `apD` of the existing function `T`. The calculation of `apD u e`
amounts to naturality of `q_e` around `ell`, with:

- the transport of `B`;
- its induced transport on `L`;
- the basepoint comparison `q_e(North)`;
- the `ap_compose` witnesses for postcomposition by transport.

Use `transport_paths_FlFr_D`, `apD_compose`, `apD_homotopic`, and the appropriate
`ap`/concatenation naturality rules to express this. The **existence** of
`apD u e` does not prove the edge goal: its value must still match the two
specified loop-closing expressions from §2.

### 3.3 Expand only the relevant computation data

Expand `AL` into its defining three pieces:

```text
right_translation_at_c (mu x y)
  @ diagonal_equivariance(c,x,y)^
  @ ap (mu x) (right_translation_at_c y)^.
```

Use `ap_pp`, `ap_V`, `ap_compose`, and `concat_Ap_concat` with explicit path
concatenations. Keep the resulting beta witnesses named. Start with `cd_diamond`
and `cd_op_diamond` opaque.

The useful equivariance computations are:

| Open lemma | Varying coordinate | Selected equivariance data |
|---|---|---|
| `loop_y_joinl` | `y`, with `x = joinl a` | `cd_op_diagonal_equivariance_joinl`; its `Join_ind_FlFr_beta_jglue` |
| `loop_y_joinr` | `y`, with `x = joinr a` | `cd_op_diagonal_equivariance_joinr`; its `Join_ind_FlFr_beta_jglue` |
| `loop_x_joinl` | `x`, with `y = joinl b` | the full equivariance beta, then `cd_op_diagonal_equivariance_glue_joinl` |
| `loop_x_joinr` | `x`, with `y = joinr b` | the full equivariance beta, then `cd_op_diagonal_equivariance_glue_joinr` |

These are families in the translation parameter `r`. Their computation as `r`
traverses `ell` is part of the required calculation; a pointwise beta rule is
not a substitute for its scalar-loop compatibility. Mixed computations of
multiplication itself must use `Join_rec2_beta_jglue_jglue` with the actual
`cd_op_diamond`.

## 4. Proposed work order for the four edge lemmas

### OPEN 3: `loop_x_joinl`

Start here, where the fixed middle argument is in the left copy.

1. Normalize the outer transport as in §3.
2. Substitute the exact `ll` and `rl` loop-closing expressions.
3. Use `cd_op_diagonal_equivariance_glue_joinl` to compute the equivariance part.
4. The two nullhomotopy centers simplify by constructor computation to
   `cd_assoc_lr b d (joinl a)` and `cd_assoc_lr b d (joinr a')`. The existing
   family `cd_assoc_lr b d` supplies their particular comparison by `apD` along
   `jglue a a'`. This avoids inventing an unrelated path between the centers.
5. Compare the transported `q_ll`/`q_rl` and `apD alpha` terms, and then the
   scalar-loop naturality and closing cancellations. That comparison is the
   unfinished mathematical step; the center comparison alone does not solve it.

Extract reusable **transport and loop-closing algebra** only once its exact
input/output witnesses are known. Those lemmas should concern free path data;
they must not assume the missing CD comparison as a disguised premise.

### OPEN 4: `loop_x_joinr`

Repeat the same calculation with the right-copy middle argument:

- use `cd_op_diagonal_equivariance_glue_joinr`;
- the centers are values of `cd_assoc_rr b d`, so their actual comparison again
  comes from `apD` of that existing family;
- retain all inverse-edge computations, especially `ap_V`, `inverse2`, and
  `inverse_natural`.

Reuse the generic algebra from OPEN 3, not an asserted reflection symmetry of
its geometric input. Check any resulting scalar comparisons at their natural
truncation level; the loop-proof comparison itself is join-valued.

### OPEN 1: `loop_y_joinl`

There is now a checked, more specific reduction using `S7LeftScalar.first_l`.
Write `A s y z` for this new partial associator. Its two middle-constructor rows
are the existing `alpha_ll` and `alpha_lr`, definitionally. We still need

```text
Q s y c : AL (joinl s) y c = A s y (joinl c)
```

with values **exactly** `q_ll s a c` and `q_lr s b c` on the two constructors.
Its missing join-glue equation, in the naturality presentation, is

```coq
concat_Ap (fun y => AL (joinl s) y c) (jglue a b)
    @ (q_ll s a c @@ 1)
  = (1 @@ q_lr s b c)
    @ S7LeftScalar.first_l_glue_l D s a b c.
```

This equation has **no final scalar `d`**. It compares one-glue computations;
the mixed diamond calculation needed for `A` has already been proved.
A concrete next calculation is:

1. Expand the three defining pieces of `AL`, retaining the selected
   precomposition, postcomposition, inverse, and join beta witnesses.
2. Normalize their scalar coefficient paths against the associativity and
   commutativity paths used by `first_l_glue_l`. These are scalar 2-path goals,
   where connectedness and 1-truncation can legitimately reduce comparisons
   to their unit values.
3. Identify the *existing* `q_ll` and `q_lr` with the corresponding mapped
   scalar comparisons, using naturality and cancellation of their triangle
   witnesses. Do not simply replace the point comparisons.
4. Use naturality of `join_natsq` with those particular scalar comparisons to
   finish the displayed equation, including the beta-path conversions.

**This overlap equation is not proved yet.** Under it, the source already
assembles `Q` and then the nullhomotopy

```text
K s y d c := ap (transport (P (joinl s) y) (jglue c d)) (Q s y c)
              @ apD (A s y) (jglue c d).
```

Closing `K` around `ell` gives a row of loop proofs. The checks `row_loop_l`
and `row_loop_r` show that its constructor values are the original `m_ll` and
`m_lr`, not different nullhomotopies. Its `apD` along `jglue a b` then supplies
`loop_y_joinl`, uniformly in `d`.

### OPEN 2: `loop_y_joinr`

Use the same organization for the right equivariance row, now comparing `rl`
with `rr`. Its reversed glues require the explicit inverse-path beta witnesses.
A unit-based center comparison can be chosen from the two `K` values at
`North` and the dependent naturality of `T` along this edge. That choice does
not supply its scalar-loop compatibility. The residual comparison of
loop-closing data must be proved for this row as well; it does not follow just
from OPEN 1 or from the existing rotation homotopy.

The proposed order **3 → 4 → 1 → 2** exploits the known center families for the
x-glues. It is a development strategy, not a claim that these comparisons have
already been reduced to reflexivity.

## 5. OPEN 5: compare the four actual side proofs

Only tackle `loop_mixed` after fixing the implementations of OPEN 1–4.

1. Unfold `XGlue`, but keep `M`, multiplication, and the diamond named where
   possible. Its two rows contain the choices made for OPEN 1 and OPEN 2.
2. Normalize its dependent transport using `transport_paths_FlFr_D` and the
   two-variable transport calculations. The ambient fibre here varies with
   `y`; first account for that before using a fixed-fibre naturality lemma.
3. Replace each row's `apD` along `jglue b b'` using `Join_ind_beta_jglue`.
   These computations give **exactly** `loop_y_joinl` and `loop_y_joinr`.
   The endpoint comparisons are **exactly** `loop_x_joinl` and `loop_x_joinr`.
4. Derive the higher compatibility of the loop-closing calculation from §3,
   preserving those four implementations. The relevant existing mixed
   equivariance computation is `cd_op_diagonal_equivariance_glue_glue`.
   Its type concerns equivariance, not `M`: it cannot simply be used as the
   missing `loop_mixed` term without the conversion and boundary matching.
5. Use `naturality_cube_change` or `join_zigzag_filler_cube` only when the
   normalized presentation and their supplied-filler hypotheses actually
   match. Matching boundaries alone never supplies their filler comparison.

The output must have precisely the dependent type shown at **OPEN 5** in the
source. Four separately proved sides do not imply this fifth equality.

## 6. If a genuine diamond calculation remains

Write down its full statement first: scalar parameters, four boundary paths,
map beta witnesses, and the two **actual** fillers being compared. Check whether
`join_zigzag_filler_change`, `join_zigzag_filler_compose`, or an existing
naturality lemma applies with those data.

If it does not, there is still a geometric proof to do. Specialize that residual
statement to the canonical circle diamond and use:

- at `North`: `diamond_v South North 1`;
- at `South`: `diamond_h North South 1`;
- on a meridian: `diamond_twist (merid a)` and the selected suspension beta rule.

Any necessary higher compatibility of these computations must be shown, not
replaced by a truncation argument. In particular:

- scalar 1-truncation may compare parallel **scalar** paths;
- it does not identify join-valued fillers or the proofs in OPEN 1–5;
- connectedness does not extend a unit calculation of these goals;
- the canonical suspension diamond is not an arbitrary filler with the same
  boundary;
- free boundary paths may be eliminated in general algebra lemmas, but the
  fixed circle loop, join glue, or chosen constrained diamond may not be
  path-inducted away.

## 7. How to turn the outline into the proof

For each gap, replace its `Context` premise by the corresponding proved lemma,
then let the unchanged assembly call that lemma. Do not prove a scratch goal
with the very same gap still available as a hypothesis and count that as
progress. Keep each proof uniform in `d`; if circle induction in `d` is used,
its dependent loop case must be supplied explicitly.

After each replacement:

1. Inspect its type and assumptions for accidental extra coherence inputs.
2. Preserve the regression checks for the selected corner and glue values.
3. Validate using the project Dune build; keep spheres and their target
   structures at `Set`.
4. Update the corresponding OPEN label only when the proof is complete.

After all five replacements, `all_scalar_loops`, `last_glue`, and `associator`
are already in place. Inverting the associator gives the library's orientation
of associativity. `cd_spheroid_of_associative`, `hspace_cd`, and the existing
pointed equivalence then finish S⁷ without further coherence assumptions.

**Current status:** the five-hypothesis assembly and its computations are
checked. The additional first-left-scalar associator is proved for the supplied
diamond. Its overlap reduction is checked but conditional. The five original
join-comparison hypotheses, full doubled associativity, and the unconditional
S⁷ H-space are still unproved.
