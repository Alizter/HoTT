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

The indexing diagrams are one-dimensional graph-shaped objects of
`Fun02 J A`. A chosen limit operation is presented as a coherent right
adjoint to the diagonal. Its induced `GpdAdjunction` gives an equivalence of
coherent hom 0-groupoids: cone morphisms are `NatModification`s and therefore
retain their cylinder condition.

The earlier `OneGpd`-valued local representability prototype is superseded.
Its pointwise perturbations do not compare modification cylinders, while
equality of paths in a pullback retains the corresponding higher square. The
ordinary homotopy pullback of arbitrary types therefore cannot satisfy that
prototype's local injectivity condition.

Colimits are not a second theory.  Following `Coproducts.v`, the complete
colimit interface is obtained from the limit interface by passing to the
opposite category and the opposite diagram.

## Accepted decisions

1. **A coherent adjunction is primitive for chosen limits.**  A chosen
   `J`-limit operation is a coherent right adjoint to the diagonal
   `A -> Fun02 J A`.
2. **Local universality is derived at the coherent hom-0-groupoid level.**
   The induced `GpdAdjunction` corepresents cones whose morphisms are
   cylinder-coherent `NatModification`s.
3. **Colimits are derived exclusively by duality.**  Follow
   `WildCat/Coproducts.v`: define colimit notions and operations as the
   corresponding limit notions and operations in `A^op`, with the indexing
   graph also reversed. Do not duplicate cone proofs with cocone proofs.
4. **Do not use the corner-induced `pullback_0gpd` as the cone object.**  Its
   morphisms forget the square relating the stored glue. The hom 0-groupoid in
   `Fun02` is different: its morphisms are coherent modifications and retain
   that square.
5. **Start with `Fun02` diagrams.**  A graph with edges needs naturality
   two-cells and cylinder-coherent modifications. `Fun01` does not provide
   the correct cells between cones.
6. **Products cover the discrete case.**  For an edge-free shape the cylinder
   conditions are vacuous, and the existing `Product` theory supplies the
   intended low-dimensional construction.
7. **Do not demand arbitrary top-cell reflection.**  The chosen limit functor
   initially needs `Fun12` structure. Cubically natural unit/counit and
   triangle modifications package the selected next coherence without a
   `Fun22` action on every pointwise perturbation.
8. **Test the interface in `Type` first.**  Ordinary homotopy pullbacks carry
   the required selected coherence by path induction. General wild-category
   hypotheses should be isolated only after this instance and Fubini work.
9. **Unicity is categorical.**  Universal cones are related by categorical
   equivalences, not by paths obtained from univalence or `Funext`.
10. **The first implementation is Type-specific at the coherence boundary.**
    The abstract adjunction interface may apply to other `Is21Cat` examples,
    but it must not claim that the generic pointwise top cells of `Fun02`
    model all higher path coherence in arbitrary wild categories. Locally
    truncated algebraic examples can receive comparison theorems later.
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

### Why the coherent hom `ZeroGpd` is the right local target

For `X : Fun02 J A` and an apex `a`, use the hom 0-groupoid from the constant
diagram to `X`:

- objects are natural-transformation cones;
- morphisms are cylinder-coherent `NatModification`s.

This is not `ZeroGroupoid.pullback_0gpd`, whose graph is induced from its two
corners and forgets compatibility with the stored glue. The `Fun02` hom
0-groupoid retains exactly that compatibility in `natmod_isnatural`.

The next generic layer, pointwise perturbations between modifications, does
not compare those cylinders. Requiring a `CatIsEquiv` of the corresponding
mapping `OneGpd`s is therefore too strong for pullbacks of untruncated types.
The coherent adjunction instead supplies only the selected cubes needed for
unit/counit naturality and the triangle laws.

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

## Mapping objects and the chosen-limit adjunction

Let `J : IsGraph`, `A : Is21Cat`, and `X : Fun02 J A`.

For `a : A`, the coherent 0-groupoid of cones is

```coq
cone_0gpd X a
  := yon_0gpd X (diagonal02 A J a).
```

Its objects are cones and its morphisms are `NatModification`s with their
cylinder coherence. A chosen limit operation is global data

```coq
limit_functor : Fun12 (Fun02 J A) A
```

together with a coherent adjunction

```text
diagonal02 A J  ⊣  limit_functor.
```

The intrinsic record should contain cubically natural unit and counit plus
triangle modifications. Unlike the existing stronger `CubicalAdjunction`, its
endpoints need only be `Fun12`; it must not require the right adjoint to map
arbitrary pointwise perturbations.

Forgetting the selected cubical data produces

```coq
GpdAdjunction diagonal02 limit_functor
```

and hence, for every `a` and `X`, an equivalence

```coq
opyon_0gpd (diagonal02 A J a) X
  $<~> opyon_0gpd a (limit_functor X).
```

The counit component at `X` is the chosen universal cone. Corecursion, beta,
eta, and uniqueness are derived from this hom-0-groupoid equivalence.

For a single diagram, a local `IsLimitCone` wrapper may record that canonical
comparison as an equivalence of coherent hom 0-groupoids. It is derived from
the chosen adjunction and is not the former `OneGpd`-valued predicate.

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
3. transport cones, modifications, and their coherent hom 0-groupoids;
4. record double-opposite comparison coherently enough for the public
   wrappers;
5. derive `HasColimits` from `HasLimits` in the opposite category.

Any local `IsColimitCocone` name should be a definitional wrapper or immediate
transport of the coherent hom-0-groupoid limit property.

## Derived local API

From the coherent diagonal-limit adjunction derive, in this order:

1. the counit cone at each diagram;
2. the inverse map on each coherent hom 0-groupoid;
3. `limit_corec`, sending a cone to its mediating map;
4. beta and eta modifications;
5. uniqueness of mediating maps;
6. the action of the selected `Fun12` limit operation;
7. transport and categorical comparison results that follow at this level.

Do not derive an action on arbitrary perturbations unless an application
supplies a genuinely coherent top-cell model.

## Chosen limits

The primary class should package all chosen limits of one shape at once:

```coq
Class HasLimits (J A : Type) `{IsGraph J, Is21Cat A} := {
  cat_limit : Fun12 (Fun02 J A) A;
  cat_limit_adjunction : CoherentAdjunction12
    (fun12_diagonal02 A J) cat_limit;
}.
```

The exact record name is provisional. Its fields are the `Fun12` analogue of
the existing `CubicalAdjunction`: cubically natural unit/counit and triangle
`NatModification`s. It induces the ordinary `GpdAdjunction`.

This is stronger than merely choosing unrelated local apexes, but canonical
pullbacks in `Type` already provide a functorial choice. It is also weaker in
the relevant direction than the superseded local `OneGpd` equivalence: it
does not reflect arbitrary incoherent perturbations.

The colimit adjunction is obtained by applying this structure in the opposite
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

The proof should proceed directly from coherent adjunctions:

1. Construct the walking-cospan pullback `Fun12` and its coherent adjunction
   with the diagonal in `Type`.
2. Extract the local hom-0-groupoid universal property and check that the
   counit component is the canonical pullback cone.
3. Lift only the selected unit/counit coherence needed to assemble pointwise
   limits in `Fun02 I Type`.
4. Compose the resulting adjunctions and use argument swap to identify the two
   presentations of double cones.
5. Obtain the Fubini equivalence

   ```text
   lim_I (lim_J X)  <~>  lim_J (lim_I (swap X)).
   ```

The construction must keep the counit cones visible long enough to identify
the canonical comparison maps. It must not rely on unrelated opaque
typeclass choices.

First specialize both shapes to the walking cospan in `Type`. Once that smoke
test works, isolate the exact coherent-adjunction hypotheses under which the
same proof is abstract in `A`. Pushout 3-by-3 remains the opposite-category
corollary.

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

`Type` is the first coherence diagnostic. Its ordinary pullback operation
should be constructed as a `Fun12`, with the canonical pullback cone as the
adjunction counit. Path induction supplies the chosen cylinder and triangle
coherence. This Type-specific proof determines the minimum abstract
coherent-adjunction interface; it must not be forced through generic
pointwise perturbations.

### `Group` and `AbGroup`

The algebraic categories currently enter the library primarily through their
`Is1Cat` structures.  Their hom data are locally truncated, so the missing
higher coherence should be canonical rather than additional mathematical
content.

The standard group and abelian-group pullbacks remain later comparison cases.
Their local truncation should make the distinction between the new coherent
hom-0-groupoid property and the legacy `CatPullback` interface harmless.


## Universe policy

The indexing graph `J` is a small diagram shape relative to the ambient
category `A`.  This covers the intended walking spans, walking cospans, finite
grids, and other small indexing categories.

The coherent-adjunction and `GpdAdjunction` interfaces use hom 0-groupoids, so
they avoid the former bundled `OneGpd` universe constraint. Indexing graphs
remain small relative to the ambient category. Inspect exported signatures,
but do not preserve the superseded `OneGpd` predicate merely for its existing
universe policy.

Before accepting a public signature:

1. inspect it with `Set Printing Universes`;
2. confirm that its constraints express only this small-shape policy;
3. avoid a parallel heterogeneous equivalence API solely to preserve
   unnecessary independence between the two mapping-groupoid universes.

No universe workaround may use `Funext`, univalence, or equality of
categorical objects.

## Module boundaries

The intended permanent dependency order is:

1. `OneGroupoid.v`: the category of 1-groupoids and its standard
   `CatIsEquiv` structure;
2. `TwoYoneda.v`: the permanent coherent covariant and contravariant
   `OneGpd`-valued Yoneda constructions;
3. `Limits.v`: diagonal, cone mapping objects, universal cones, and derived
   local operations;
4. chosen-limit functoriality and the diagonal adjunction, implemented later
   in `Limits.v`;
5. `Colimits.v`: a thin public dual interface implemented through limits in
   opposite categories, following `Coproducts.v`;
6. shape-specific limit modules such as pullbacks, with colimit modules such
   as pushouts implemented by duality.

`LimitsScratch.v`, `CohYonedaScratch.v`, and the pushout scratch files remain
sources to inspect.  Permanent modules must not import them.

## Formalisation milestones

### Coherent Yoneda foundation

- [x] Select the required `OneGpd` Yoneda definitions from
      `CohYonedaScratch.v`.
- [x] Move them into a permanent module without importing scratch code.
- [x] Build the module and audit assumptions and universes.

### Superseded universal-cone prototype

- [x] Build and audit the `OneGpd`-valued `IsLimitCone` prototype.
- [x] Derive its corecursor, chosen limit `Fun12`, pointwise construction, and
      diagonal `GpdAdjunction`.
- [x] Diagnose its invalid top-cell requirement using the walking-cospan
      pullback: pointwise perturbations omit cylinder comparison.
- [ ] Keep the built modules as migration references until their useful
      lower-dimensional API has moved to the replacement.

### Coherent-adjunction replacement

- [x] Define the `Fun12` coherent-adjunction record with cubically natural
      unit/counit and triangle modifications.
- [x] Prove that it induces `GpdAdjunction`.
- [x] Define `HasLimit02` from a chosen limit `Fun12` and its
      `GpdAdjunction`.
- [ ] Recover the local coherent hom-0-groupoid cone property and corecursor
      API.
- [x] Construct the walking-cospan pullback `Fun12` in `Type`.
- [ ] Construct its unit, canonical-cone counit, selected cubical naturality,
      and triangle modifications.
- [x] Build the resulting `GpdAdjunction` and audit assumptions.

The current `Type` prototype deliberately stops at `HasLimit02` and the
coherent hom-0-groupoid cone property.  It does not register the legacy
`Limits.HasLimits` instance: that would reintroduce the false
`OneGpd`-valued local injectivity requirement.  Instead,
`PullbackFubiniApplicationScratch.v` now contains a closed concrete regression
theorem, `equiv_iterated_cospan_pullback_fubini`, which consumes one coherent
double cospan and returns the equivalence between its canonical rowwise and
columnwise iterated pullbacks.  Its proof delegates to
`Limits.Pullback.pullback3x3` after a generic homotopy normalization of the
transposed naturality witnesses; it does not yet supply the abstract
pointwise-limit Fubini theorem.

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

- [ ] Assemble pointwise limits directly from the coherent limit adjunction.
- [ ] Prove the pointwise counit cone and the hom-0-groupoid universal
      property using only the selected cubical coherence.
- [ ] Compose the two pointwise adjunction presentations and derive Fubini.
- [ ] Record compatibility of the Fubini map with both induced double cones.
- [ ] Specialize both shapes to `WalkingCospan` in `Type` and compare the
      resulting equivalence and boundary beta laws with
      `Limits.Pullback.pullback3x3`.

The concrete one-argument equivalence is now checked in
`PullbackFubiniApplicationScratch.v`.  Its implementation reuses
`Limits.Pullback.pullback3x3`; replacing that concrete step by abstract Fubini
remains part of the unchecked work above and does not require an API change.

- [ ] After the Type smoke test, state the minimum hypotheses for the abstract
      walking-cospan theorem.

### Validation

- [x] Build and assumption-audit `fun12_cone_1gpd`, `fun12_cat_limit`, and
      `gpd_adjunction_cat_limit`; all are closed under the global context.
- [x] Build and assumption-audit `cospan_pullback_map_homotopy`,
      `gpd_adjunction_cospan_pullback`, and `cospan_pullback_islimit`; all are
      closed under the global context.
- [x] Audit conversion-heavy proofs in `PointwiseLimitCorec.v` and
      `PointwiseLimitUniversal.v`.  Timings below are wall times for dedicated
      `coqc -time` scratch reproductions unless marked as module builds; `≤1 s`
      records a proof whose complete dedicated or reduced scratch finished
      within one second.

| Proof | Revised conversion use | Timing |
| --- | --- | ---: |
| `fun11_bireflect_square` | named square whiskering only | `≤1 s` |
| `fun11_bireflect_fmap` | none | `≤1 s` |
| `fun11_fmap_bireflect` | none | `≤1 s` |
| `cylinder_id_to_3cell` | named cylinder elimination and unit laws | `≤1 s` |
| `transpose_hrefl_vrefl_direct` | none | `≤1 s` |
| `transpose_vrefl_hrefl_direct` | none | `≤1 s` |
| `pointwise_diagonal_fmap_direct` | none | `≤1 s` |
| `pointwise_diagonal_map_comparison` | none | `≤1 s` |
| `pointwise_diagonal_comparison` | none | `≤1 s` |
| `swap_fun02_hom_to_naturality_direct` | one targeted `cbn beta` | `≤1 s` |
| `pointwise_limit_cone_map_comparison` | none | `≤1 s` |
| `pointwise_limit_cone_map_comparison_component` | rewrites only | `≤1 s` |
| `pointwise_limit_corec_naturality_cone` | none | `≤1 s` |
| `pointwise_limit_corec_modification_naturality_cone_square` | named square pasting and boundary rewrites | `72.50 s` |
| `pointwise_limit_corec_modification_naturality_cylinder` | constructor, reflection, and boundary rewrites | `≤1 s` |
| `pointwise_limit_beta_at` | starts from `Build_Cylinder`; no square/cylinder unfolding | `16.04 s` |
| `pointwise_limit_beta_component` | rewrites removed | `1.07 s` |
| `pointwise_limit_beta_comparison` | componentwise square constructor | `1.30 s` |
| `pointwise_limit_beta_naturality` | nested componentwise square constructors | `3.26 s` |
| `pointwise_limit_beta` | packaging conversion removed | `1.01 s` |
| `pointwise_limit_eta_naturality_cone` | named boundary eliminators and square pasting | `74.68 s` |
| `pointwise_limit_cone_map_comparison_component_eta` | none | `4.15 s` |
| `pointwise_limit_eta` | componentwise comparison square; beta opaque | `36.81 s` |

- [x] Rebuild the revised pointwise-limit modules.  The current
      `PointwiseLimitCorec.v` `coqc -time` run completed in `329.42 s`;
      the current `PointwiseLimitUniversal.v` sequential check completed in
      `43.14 s`.

#### Square/Cylinder abstraction and proof direction

The pointwise-limit proofs were also audited for reliance on the definitions
`Square l r t b := r $o t $== b $o l` and
`Cylinder p q s t := Square (q $@R f) (g $@L p) s t`.  A representation leak
includes not only an explicit `unfold Square` or `unfold Cylinder`, but also a
`change` to the resulting raw composite, proving a square by component
`intro`s, using a cylinder directly as a 3-cell by conversion, or
`lazymatch`ing the boundary of a `Square`.  The forward-proof counts below are
counts of `pose`, `assert`, and Ltac `let` commands in the proof body.  They are
a warning metric, not by themselves a defect: a backward proof should first
apply the constructor, eliminator, reflection, or pasting operation dictated
by its goal, and introduce local names only for repeated subterms.

API work required before rewriting the largest proofs:

- [x] Move the pointwise-only corner-whiskering calculations to `Square.v`
      as the reusable `whiskerTR_gpd`, `whiskerBL_gpd`, and
      `whiskerLB_gpd` operations.
- [x] Add `Build_NatModificationSquare` and
      `natmod_square_component` as the componentwise constructor and
      eliminator for squares of modifications.
- [x] Move identity-sided cylinder elimination to `Cylinder.v` as
      `cylinder_id_to_3cell`, expressed through `gpdhom_cylinder` and named
      unit laws.
- [x] Add the generic laws exposed by the rewrites:
      `fmap_comp_prewhisker_natural`,
      `fmap_comp_postwhisker_natural`, and
      `cat_assoc_opp_natural_m`; the existing rotation and pasting operations
      cover the remaining cases.
- [x] Adopt the client-module invariant that `Square` and `Cylinder` are not
      unfolded and their raw composite equations are not targets of `change`.
      Representation-level proofs remain in `Square.v` and `Cylinder.v`.

Representation-dependent proofs, in priority order:

- [x] Rewrite `pointwise_limit_eta_naturality_cone` to inspect constituent
      boundaries only through the named `square_*` eliminators and assemble
      the result through square pasting.  Its remaining long equations are
      3-cell coherence calculations after boundary elimination, not
      conversions from `Square` or `Cylinder`.
- [x] Rewrite the edge-coherence branch of `pointwise_limit_beta_at` to start
      from `Build_Cylinder`; it no longer unfolds either representation.
- [x] Replace `gpdhom_of_cylinder_id_direct` by the generic
      `cylinder_id_to_3cell`.
- [x] Rewrite `pointwise_limit_beta_comparison` through
      `Build_NatModificationSquare`.
- [x] Rewrite `pointwise_limit_beta_naturality` through nested
      `Build_NatModificationSquare` constructors.
- [x] Rewrite the local comparison square in `pointwise_limit_eta` with
      `Build_NatModificationSquare`, named boundary rewrites, and
      `Build_Square`.

Forward-construction hotspots refactored toward goal-directed construction:

- [x] Refactor
      `pointwise_limit_corec_modification_naturality_cone_square` to apply
      `hconcatR` and `hconcatL` from the target before assembling its
      constituent squares.
- [x] Refactor
      `pointwise_limit_corec_modification_naturality_cylinder` to apply
      `cylinder_of_square`, reflection, and boundary rewrites from the target.
- [x] Refactor `fun11_bireflect_square` as a backward sequence of generic
      square-whiskering operations.
- [x] Refactor `pointwise_limit_eta_component` to apply `fun11_bireflect`
      first and fill its beta/comparison argument afterward.
- [x] Review `pointwise_limit_corec_naturality_cone`; its goal-directed
      `lhs'` chain is retained and only repeated composite terms are named.

Completion criteria:

- [x] The two pointwise-limit modules contain no `unfold Square`,
      `unfold Cylinder`, `change` to a raw square/cylinder composite, or
      `lazymatch` over a `Square` boundary.
- [x] Square and cylinder construction sites use named constructors,
      eliminators, reflection, rewrites, or pasting operations; forward
      aliases name repeated terms in the resulting coherence subgoals.
- [x] Rebuild both modules and rerun the closed-context assumption audit;
      all audited declarations remain closed under the global context.
- [ ] Show that the discrete limit specializes to the existing `Product`
      universal property.
- [ ] Confirm that the dual discrete interface specializes as
      `Coproduct := Product` in the opposite category.
- [ ] Construct the walking-cospan pullback coherent adjunction in `Type`.
- [ ] Exhibit the corresponding pointed construction in `pType`.
- [ ] Compare locally truncated algebraic examples with the coherent
      hom-0-groupoid interface and legacy `CatPullback`.
- [ ] Derive pointwise limits and abstract limit Fubini from coherent
      adjunctions.
- [ ] As the final smoke test, derive pullback 3-by-3 first in `Type`, then
      under the isolated abstract hypotheses.
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

1. Final exported names for the coherent-adjunction and derived local
   interfaces.
2. Whether the intrinsic `Fun12` record should generalize
   `CubicalAdjunction` directly or be limit-specific.
3. The minimum selected coherence needed to lift the adjunction pointwise
   without a `Fun22` action on arbitrary perturbations.
4. Whether all immediate indexing shapes are best represented as graphs, or
   whether an ordinary category-shaped layer is needed before sequential
   constructions.
5. The cleanest comparison with locally truncated `Group` and `AbGroup`
   examples.
