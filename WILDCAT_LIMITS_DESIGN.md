# One-categorical limits in `WildCat`

This is the working design record for the formalisation of limits in
`theories/WildCat`.  Colimits are exposed only as the formally dual API
obtained from limits in opposite categories.  The document records accepted
decisions, intended interfaces, known prerequisites, and validation
milestones.  It is not user-facing library documentation.

Update this document when an interface is accepted, an assumption changes, or
a universe/coherence obstruction is discovered.

## Goal

Develop ordinary conical limits for wild one-categories throughout the
library.  The abstraction is not specific to `Type` or `pType`: it is intended
to apply to every `Is1Cat` example that has the relevant concrete limits once
its mapping coherence is packaged.  `Type`, `pType`, `Group`, and `AbGroup`
are important diagnostics, not an exhaustive list of targets.

The indexing diagrams are one-dimensional: initially they are graph-shaped
objects of `Fun02 J A`.  The universal property nevertheless retains the
available homotopy coherence by taking values in `OneGpd`.

A limit is defined by a specified universal cone.  A chosen limit operation,
its functoriality, and its adjunction with the diagonal are theorems derived
from those local universal properties.  An adjunction is not a field of the
definition of having limits.

Colimits are not a second theory.  Following `Coproducts.v`, the complete
colimit interface is obtained from the limit interface by passing to the
opposite category and the opposite diagram.

## Accepted decisions

1. **Universal cones are primitive.**  Follow the organization of
   `WildCat/Products.v`: bundle an apex, a concrete cone, and the equivalence
   induced by that cone.
2. **Adjunctions are derived.**  Choosing a universal cone for every diagram
   yields the limit operation and its adjunction with the diagonal.
3. **Colimits are derived exclusively by duality.**  Follow
   `WildCat/Coproducts.v`: define colimit notions and operations as the
   corresponding limit notions and operations in `A^op`, with the indexing
   graph also reversed.  Do not duplicate cone proofs with cocone proofs.
4. **Use `OneGpd`-valued representability.**  `ZeroGpd` forgets comparisons
   between modifications.  Those three-cells are needed for coherent induced
   maps, iterated limits, and functor-category arguments.
5. **Start with `Fun02` diagrams.**  A graph with edges needs naturality
   two-cells and cylinder-coherent modifications.  `Fun01` does not provide
   the correct cells between cones.
6. **Products cover the discrete case.**  For an edge-free shape the cylinder
   conditions are vacuous, and the existing `Product` theory supplies the
   intended low-dimensional construction.
7. **Do not develop pseudofunctor bilimits yet.**  Diagrams
   `X : Fun22 J A`, pseudonatural cones, and arbitrary 2-categorical indexing
   shapes are outside the immediate scope.
8. **`Fun12` and `Fun22` may appear as derived structure.**  They describe the
   coherence of a chosen limit operation or of the cone functor.  Their use as
   bookkeeping does not change the fact that the indexed diagrams are
   one-dimensional.
9. **Unicity is categorical.**  Universal cones are related by categorical
   equivalences, not by paths obtained from univalence or `Funext`.
10. **The theory is not restricted to existing `Is21Cat` instances.**
    `Is21Cat` is the current sufficient package for constructing mapping
    `OneGpd`s.  Categories initially presented only as `Is1Cat`, especially
    locally truncated algebraic examples, should receive their canonical
    higher coherence through a reusable construction.  Truncation of a
    particular diagram object must not be built into the abstract definition
    of a limit.
11. **Scratch files are design sources, not implementation targets.**
    Accepted definitions move into permanent modules.  Permanent modules must
    not import `LimitsScratch.v` or `CohYonedaScratch.v`.

## Scope and terminology

### What “one-categorical” means here

The diagrams have objects and arrows but no nontrivial indexing 2-cells.  For
the first implementation, an indexing shape is a graph:

```coq
J : Type
`{IsGraph J}
X : Fun02 J A
```

The target is mathematically an `Is1Cat`.  Constructing its mapping
`OneGpd`s also requires enough local 3-cell coherence.  The first
implementation may use the existing sufficient package:

```coq
A : Type
`{Is21Cat A}
```

This assumption is coherence infrastructure, not a restriction of the
intended applications to categories already carrying a handwritten
`Is21Cat` instance.  A reusable lift should supply it, or the minimum
replacement interface, for locally truncated `Is1Cat` examples.  The limit
itself remains a conical limit of a one-dimensional diagram.

This first layer covers graph presentations of the shapes needed immediately,
including discrete families, spans, cospans, parallel arrows, and sequences
presented by generating successor maps.

An arbitrary category-shaped diagram with specified identity and composition
laws is a later extension.  Such a diagram will require more coherent functor
data than `Fun02` provides, even if the indexing category has no nontrivial
2-cells.

### Why `Fun01` is insufficient for edges

For an edge `u : i $-> j`, a cone contains a naturality 2-cell.  A cell between
two cones contains pointwise 2-cells together with compatibility between those
naturality cells.  That compatibility is a 3-cell, represented by a
`Cylinder`.

`FunctorCat.v` gives `Fun01` arbitrary pointwise 2-cells between natural
transformations.  It does not require the cylinder condition.  Therefore its
hom object is not the correct category of cones for an edgeful diagram.

`Fun02` has the same object and arrow data as `Fun01`, but its 2-cells are
`NatModification`s satisfying the required cylinder.  This is the minimum
appropriate diagram category for the present theory.

### Why `OneGpd` rather than `ZeroGpd`

For `X : Fun02 J A` and an apex `a`, the cone mapping object has:

- objects: natural-transformation cones;
- 1-cells: cylinder-coherent `NatModification`s;
- 2-cells: pointwise 3-cells between modifications.

A `ZeroGpd` can retain the first two levels, but not the third.  A `OneGpd`
retains all three levels available in the current `(2,1)`-categorical
infrastructure.

This matters even though the indexing diagram is one-dimensional.  The extra
level is used when proving that induced maps respect modifications, that
functor laws hold coherently, and that two iterated universal constructions
represent the same cone object.

## Existing precedents and infrastructure

### Products

`theories/WildCat/Products.v` has the desired order of construction:

```coq
Class Product ... := {
  cat_prod : A;
  cat_pr : forall i, cat_prod $-> x i;
  cat_isequiv_cat_prod_corec_inv :: forall z,
    CatIsEquiv (cat_prod_corec_inv ... z);
}.
```

It then derives:

- pairing/corecursion;
- beta and eta;
- uniqueness;
- equivalence of products;
- `Is0Functor` and `Is1Functor` structures on the chosen product operation.

The general limit interface should follow this ordering.  Products do not by
themselves solve the edgeful case because their indexing shape is discrete.

### Existing `CatPullback` and the `AbGroup` diagnostic

`theories/WildCat/Pullbacks.v` defines `CatPullback` by corepresenting the
pullback of mapping `ZeroGpd`s.  Its own comments record the loss of
coherence: the `ZeroGpd` pullback ignores 2-cells in the corner.  Consequently
the standard pullback of types is a `CatPullback` only when the corner type is
0-truncated; the proof uses `path_ishprop` to discard the missing coherence.

`AbGroup` is a notable current user.  `haspullbacks_abgroup` inherits the
existing `CatPullback` construction through `Group`.  No explicit truncation
argument appears at that call site because abelian-group carriers and their
relevant hom data are already truncated.  Nevertheless, the proof route
depends on exactly the low-coherence/truncation workaround above.

The new theory should improve this situation:

- the abstract walking-cospan limit must not assume that its corner object is
  truncated;
- the ordinary homotopy pullback of types should satisfy the new universal
  cone property without `IsTrunc 0` on the corner;
- the standard group and abelian-group pullbacks should satisfy the same
  universal property;
- the old `CatPullback` interface should be recovered as a comparison theorem
  when the relevant local truncation makes the forgotten coherence unique.

Thus `AbGroup` is both an intended application and a regression test that the
new abstraction removes accidental truncation hypotheses rather than merely
moving them.

### `Fun02`

`theories/WildCat/TwoFunctor.v` already supplies:

- `Fun02 J A`;
- natural transformations as its 1-cells;
- `NatModification` with a cylinder condition as its 2-cells;
- pointwise 3-cells;
- `Is21Cat (Fun02 J A)` when `J : IsGraph` and `A : Is21Cat`.

Thus the coherent category of graph diagrams already exists.

### `OneGpd` and coherent Yoneda

`theories/WildCat/OneGroupoid.v` supplies:

- `OneGpd`;
- 1-functors as morphisms;
- natural transformations and pointwise higher cells;
- `Is21Cat OneGpd`;
- categorical equivalences in `OneGpd`.

`theories/WildCat/CohYonedaScratch.v` contains prototypes for:

- `opyon_1gpd`;
- its `Fun12` and `Fun22` structures;
- the `OneGpd` of pseudonatural transformations;
- the coherent Yoneda equivalence.

The accepted subset must be moved to a permanent coherent-Yoneda module before
the permanent limit theory depends on it.

### Scratch limit theory

`theories/WildCat/LimitsScratch.v` contains reusable prototypes for:

- the coherent diagonal into `Fun02 J A`;
- `Fun12` and `Fun22` structures on that diagonal;
- `GpdAdjunction` and `CubicalAdjunction`;
- lower `ZeroGpd`-valued cone and dual cocone prototypes;
- pointwise constructions and Fubini machinery.

Its current `HasLimit02` and `HasLimit22` make an adjunction primitive.  The
new interface reverses that dependency: local universal cones are primitive
and these adjunctions, when wanted, are derived.

Only the limit-facing constructions should be promoted into the foundational
theory.  Cocone and colimit code in scratch files is evidence for the duality
interface, not a second implementation to port.

## Mapping objects

Let `J : IsGraph`, `A : Is21Cat`, and `X : Fun02 J A`.

### Cone 1-groupoid

For `a : A`, define conceptually

```coq
cone_1gpd X a
  := Hom_1gpd (diagonal02 A J a) X.
```

It is the hom `OneGpd` in `Fun02 J A` from the constant diagram at `a` to `X`.


### Functoriality in the apex

The cone construction is contravariant in `a`.  Ultimately it should be a
coherent `OneGpd`-valued functor:

```text
Cone(X,-) : A^op -> OneGpd.
```

The initial local universal-cone definition need not take this functor as a
field.  Its structure should be constructed once from precomposition and the
coherent diagonal.

## Universal cone

Given an apex `l : A` and a cone

```coq
lambda : diagonal02 A J l $-> X
```

composition with `lambda` induces, for each `a : A`, a 1-functor

```coq
limit_cone_map X l lambda a
  : Hom_1gpd a l $-> cone_1gpd X a.
```

Its action is:

- on a map `k : a $-> l`, send `k` to
  `lambda $o fmap diagonal02 k`;
- on a 2-cell `p : k $== k'`, use the diagonal modification and
  postcomposition by `lambda`;
- on a 3-cell, act pointwise.

The proposed local predicate is:

```coq
Definition IsLimitCone
  {A J} `{Is21Cat A, IsGraph J}
  (X : Fun02 J A) (l : A)
  (lambda : diagonal02 A J l $-> X)
  : Type
  := forall a : A,
       CatIsEquiv (limit_cone_map X l lambda a).
```

The proposed bundled construction follows `Product`:

```coq
Class Limit
  (J : Type) {A : Type}
  `{IsGraph J, Is21Cat A}
  (X : Fun02 J A) := {
  cat_limit : A;
  cat_limit_cone : diagonal02 A J cat_limit $-> X;
  cat_islimit_cone ::
    IsLimitCone X cat_limit cat_limit_cone;
}.
```

Separating `IsLimitCone` from `Limit` is useful for proving that a concrete cone
is universal and for transporting universality across an equivalence or
modification of cones.

The exact exported names remain subject to a collision audit against scratch
modules.  The mathematical interface above is the accepted one.

## Colimits by opposite-category duality

For `X : Fun02 J A`, its opposite diagram has the conceptual type

```coq
X^op : Fun02 J^op A^op.
```

A cocone `X $-> diagonal c` in `A` is exactly a cone
`diagonal c $-> X^op` in `A^op`.  Therefore define the colimit interface by
reuse:

```text
Colimit_A(X) := Limit_(A^op)(X^op).
```

As in `Coproducts.v`, exported colimit names are thin wrappers around the
corresponding limit definitions:

- `cat_colimit` is `cat_limit` in `A^op`;
- injections/cocone components are the projections/cone components in
  `A^op`;
- recursion is limit corecursion in `A^op`;
- beta, eta, unicity, functoriality, and the adjunction are limit theorems in
  `A^op`;
- colimit Fubini and pushout 3-by-3 are dual corollaries of their limit
  counterparts.

This requires coherent opposite infrastructure, not a duplicate cocone
theory:

1. construct `fun02_op : Fun02 J A -> Fun02 J^op A^op`;
2. identify the opposite diagonal with the diagonal of the opposite category;
3. transport cones, modifications, and their `OneGpd` mapping objects;
4. record double-opposite comparison coherently enough for the public
   wrappers;
5. derive `HasColimits` from `HasLimits` in the opposite category.

Any `IsColimitCocone` name should be a definitional wrapper or immediate
transport of `IsLimitCone` for the opposite diagram.  It must not carry an
independently proved universal property.

## Derived local API

From `Limit J X`, derive in this order:

1. the inverse equivalence on each mapping `OneGpd`;
2. `limit_corec`, sending a cone to its mediating map;
3. beta: the induced cone is related to the input cone by a modification;
4. eta: corecursion applied to the universal cone recovers the map;
5. action of `limit_corec` on modifications and 3-cells;
6. uniqueness/full faithfulness of mediating maps;
7. transport of universality along an equivalence of cones;
8. categorical equivalence between the apexes of two universal cones;
9. coherence of that apex equivalence with the two cones.

The convenience constructor analogous to `Build_Product` may accept explicit
corecursor, beta, eta, and coherence data, but it must construct the universal
mapping equivalence.  It must not introduce an alternative foundational notion
of limit.

All dual recursor, beta, eta, and unicity names belong to the thin
opposite-category wrapper described above.

## Chosen limits and the adjunction theorem

After the local interface is stable, define choice separately:

```coq
Class HasLimits (J A : Type) `{IsGraph J, Is21Cat A}
  := has_limits : forall X : Fun02 J A, Limit J X.
```

From `HasLimits J A`, derive:

1. the object function `X |-> cat_limit J X`;
2. its action on natural transformations using universal cones;
3. its action on `NatModification`s;
4. identity and composition comparison cells;
5. initially a `Fun12 (Fun02 J A) A` structure;
6. any further `Fun22` coherence justified by the `OneGpd` universal property;
7. the unit/counit or hom-equivalence form of the adjunction with the diagonal.

The first adjunction theorem should expose the useful one-categorical interface.
A coherent/cubical adjunction may then be derived as a stronger theorem.  No
adjunction is stored in `HasLimits`.

The colimit adjunction is obtained by applying this theorem in the opposite
category; it is not proved independently.

## `OneGpd` limits

The library currently gives `OneGpd` its wild `(2,1)`-category and equivalence
structures, but does not package its limits.

Mathematically, the desired limits are groupoid-valued homotopy-coherent
limits.  For example, the pullback appropriate to equivalence-valued
universality is an iso-comma/homotopy pullback, not merely a strict pullback of
underlying object types.

Develop only the closure results required by subsequent formalisation:

1. indexed products of `OneGpd`s;
2. the walking-cospan limit;
3. pointwise limits of the relevant functor categories;
4. more general graph limits only when an application requires them.

Each construction must include functoriality on objects, arrows, and 2-cells,
and its universal property must be stated using categorical equivalence.

## Pointwise limits, Fubini, and the final smoke test

The decisive test of the theory is not merely constructing a walking-cospan
limit.  It is proving limit 3-by-3 abstractly in a category with the required
chosen limits.

The proof must proceed through the universal-cone machinery:

1. Start with specified chosen `J`-limits in `A`.
2. For a graph `I`, construct `J`-limits in `Fun02 I A` pointwise.  At each
   object of `I`, use the chosen limit cone in `A`; use its universal property
   to define the action on edges, modifications, and higher cells.
3. Prove that the assembled pointwise cone is universal in the functor
   category.  Pointwise evaluation alone is not the theorem; the
   `OneGpd`-equivalence of cone objects is.
4. For `X : Fun02 I (Fun02 J A)`, form row-first and column-first iterated
   limits using these specified pointwise choices.
5. Show that both iterated limits represent the same `OneGpd` of double cones.
   Argument swap identifies the two cone presentations, and categorical
   unicity supplies the canonical Fubini equivalence

   ```text
   lim_I (lim_J X)  <~>  lim_J (lim_I (swap X)).
   ```

The construction must keep the chosen cones visible long enough to identify
the canonical comparison maps.  It must not rely on unrelated opaque
typeclass choices and then prove only that the resulting apexes happen to be
equivalent.

Finally specialize both `I` and `J` to the walking cospan.  For any category
`A` with the required chosen pullbacks and pointwise pullbacks, this must yield
the pullback 3-by-3 lemma: the two iterated pullback constructions are
canonically equivalent, with the equivalence compatible with their universal
cones.  This theorem must be abstract in `A`; specializing it to `Type` should
recover the existing concrete result without a new path-constructor
calculation.

This pullback 3-by-3 theorem is the final acceptance test for the initial
limit formalisation.  Pushout 3-by-3 is then obtained by applying it to the
opposite category, not by a separate proof.

## Applicability and diagnostics

### General `Is1Cat` examples

The intended users are all library categories presented as `Is1Cat` and
carrying the relevant limits.  The extra structure needed to form mapping
`OneGpd`s should be supplied independently of the limit construction.  A
category should not need a bespoke limit theory merely because its higher
coherence instance has not yet been packaged.

### `Type` and `pType`

`Type` and `pType` already have `Is21Cat` instances, so their mapping
`OneGpd`s and coherent cone objects can be formed immediately.  Their
canonical limits should be connected to the abstract interface by proving
`IsLimitCone`, not by rebuilding functoriality or Fubini with constructors and
path calculations.

### `Group` and `AbGroup`

The algebraic categories currently enter the library primarily through their
`Is1Cat` structures.  Their hom data are locally truncated, so the missing
higher coherence should be canonical rather than additional mathematical
content.

The standard group and abelian-group pullbacks are concrete test cases.  The
new `OneGpd`-valued universal cone should validate them without putting a
corner-truncation premise in the abstract pullback definition.  A separate
comparison should show that, in these truncated examples, the new pullback
recovers the existing `CatPullback` API used by `IsEpiStable` and the
`AbGroup` developments.


## Universe policy

The mapping `OneGpd`s for the ambient category, diagram category, and cone
category may live in different universes.  A naive bundled comparison can force
unwanted equalities between:

- the object and arrow universes of `J`;
- the object, 1-cell, 2-cell, and 3-cell universes of `A`;
- the carrier universes of the two mapping groupoids.

Before accepting the public signature:

1. prototype it in a temporary file with `Set Printing Universes`;
2. inspect all exported constants and classes;
3. reject any accidental equality between a shape universe and a cell universe;
4. if necessary, use a heterogeneous `Fun11`/equivalence formulation rather
   than forcing both mapping objects into one bundled `OneGpd` universe;
5. record unavoidable inequalities explicitly.

No universe workaround may use `Funext`, univalence, or equality of categorical
objects.

## Module boundaries

The intended permanent dependency order is:

1. `OneGroupoid.v`: the category of 1-groupoids;
2. a permanent coherent-Yoneda module extracted from
   `CohYonedaScratch.v`;
3. `Limits.v`: diagonal, cone mapping objects, universal cones, and derived
   local operations;
4. chosen-limit functoriality and adjunction, either later in `Limits.v` or in a
   focused companion module if the file becomes too large;
5. `Colimits.v`: a thin public dual interface implemented through limits in
   opposite categories, following `Coproducts.v`;
6. shape-specific limit modules such as pullbacks, with colimit modules such
   as pushouts implemented by duality.

`LimitsScratch.v`, `CohYonedaScratch.v`, and the pushout scratch files remain
sources to inspect.  Permanent modules must not import them.

## Formalisation milestones

### Coherent Yoneda foundation

- [ ] Select the required `OneGpd` Yoneda definitions from
      `CohYonedaScratch.v`.
- [ ] Move them into a permanent module without importing scratch code.
- [ ] Build the module and audit assumptions and universes.

### Universal cones

- [ ] Define the coherent diagonal for `Fun02` diagrams.
- [ ] Define `cone_1gpd` and its apex functoriality.
- [ ] Define `limit_cone_map` as a 1-functor.
- [ ] Audit the signature with universe printing.
- [ ] Define `IsLimitCone` and `Limit`.

### Local limit API

- [ ] Derive corecursion, beta, and eta.
- [ ] Derive action on modifications and higher cells.
- [ ] Prove transport of universality.
- [ ] Prove categorical unicity of universal cones.
- [ ] Add a `Build_Product`-style convenience constructor if justified by the
      first concrete example.

### Chosen limits

- [ ] Define `HasLimits` as a choice of local universal cone for every diagram.
- [ ] Derive the limit operation on transformations and modifications.
- [ ] Prove its functor laws from universal uniqueness.
- [ ] Prove the adjunction with the diagonal as a theorem.

### Opposite-category colimit interface

- [ ] Construct the coherent opposite of a `Fun02` diagram.
- [ ] Prove compatibility of opposite diagrams with the diagonal and cone
      mapping `OneGpd`.
- [ ] Define `Colimit`, `HasColimits`, and their public operations as wrappers
      around limits in the opposite category.
- [ ] Derive every colimit beta, eta, unicity, functoriality, and adjunction
      result from its limit counterpart.
- [ ] Confirm that no independent cocone universal-property proof remains in
      the permanent theory.

### Pointwise limits and Fubini

- [ ] Construct specified pointwise limits in `Fun02 I A` from specified
      limits in `A`.
- [ ] Prove the assembled pointwise cone is universal in the functor category.
- [ ] Define row-first and column-first double-cone presentations without
      hiding the chosen cones behind unrelated typeclass choices.
- [ ] Prove the abstract Fubini equivalence by coherent argument swap and
      categorical unicity.

### Validation

- [ ] Show that the discrete limit specializes to the existing `Product`
      universal property.
- [ ] Confirm that the dual discrete interface specializes as
      `Coproduct := Product` in the opposite category.
- [ ] Construct the required limits in `OneGpd`.
- [ ] Exhibit the standard homotopy pullback of types as a universal cone.
- [ ] Exhibit the corresponding pointed construction in `pType`.
- [ ] Provide a reusable coherent-hom lift for locally truncated `Is1Cat`
      examples.
- [ ] Exhibit the standard `AbGroup` pullback as a universal cone.
- [ ] Compare the new walking-cospan limit with `CatPullback` under the legacy
      truncation hypotheses.
- [ ] Derive pointwise limits in `Fun02 I A` from chosen limits in `A`.
- [ ] Prove abstract limit Fubini with its specified universal cones.
- [ ] As the final smoke test, derive pullback 3-by-3 in an arbitrary category
      with the required chosen pullbacks.
- [ ] Obtain pushout 3-by-3 solely by opposite-category duality.

## Explicit non-goals for the first implementation

- Limits of arbitrary `Fun22 J A` pseudofunctor diagrams.
- Weighted limits or general bilimits.
- Equality of limit apexes.
- A blanket claim that every low-coherence `Fun01` graph limit is meaningful.
- Reproving product theory through the new machinery before the general
  interface is stable.
- Object-specific proofs of pointwise functoriality or Fubini.
- Importing a scratch module from permanent library code.
- An independently implemented cocone/colimit theory or a second proof of any
  colimit theorem already obtained from limits in the opposite category.

## Open design questions

1. Final exported names: `Limit`, `GraphLimit`, or a temporary coherence suffix
   during migration.
2. The exact heterogeneous equivalence structure needed for separately
   universed mapping `OneGpd`s.
3. Whether the `OneGpd` universal property directly derives the full `Fun22`
   structure on the chosen limit operation, or first yields only `Fun12` plus a
   separate coherence theorem.
4. Whether all immediate indexing shapes are best represented as graphs, or
   whether an ordinary category-shaped layer is needed before sequential
   constructions.
5. The minimum reusable coherence interface, or automatic construction, that
   lets locally truncated `Is1Cat` examples such as `Group` and `AbGroup`
   supply mapping `OneGpd`s without bespoke proofs.
