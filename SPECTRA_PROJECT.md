# Spectra and spectrification project

This file records the direction of the current development. It is a working checklist, not library documentation; update it whenever a milestone is completed or the design changes.

## Goal

Construct spectrification of prespectra and use it to turn the existing suspension prespectrum into the suspension spectrum. The critical mathematical input is the interaction between loops and sequential colimits of pointed types.

There is a parallel categorical track developing wild limits and colimits. Its immediate test case is that colimits commute with colimits and hence give the pushout 3-by-3 lemma. This infrastructure is useful, but it should not unnecessarily block the direct construction of spectrification.

The current focus is the pushout 3-by-3 smoke test. The categorical structures on `Fun02` and `Fun12` are now assembled. Alongside the direct refactoring of the limits-and-colimits interface, `theories/WildCat/KanScratch.v` now tests a local Kan-extension formulation. The immediate question is whether Kan-extension pasting and uniqueness yield 3-by-3 with less global pseudofunctor infrastructure. The associativity-cylinder cleanup and the two unit-cylinder proofs remain deliberately deferred.

## Established spectrum infrastructure

- [x] Define prespectra as coalgebras for pointed loops and spectra as prespectra whose structure maps are equivalences.
- [x] Give the natural-number-indexed constructors `prespectrum_from_sequence` and `spectrum_from_sequence`.
- [x] Define maps, homotopies, higher globes, identity, composition, and the displayed wild-category structure.
- [x] Induce the wild-category and equivalence structures on `PreSpectrum` and `Spectrum`.
- [x] Define levelwise spectrum equivalences and show that they are categorical equivalences.
- [x] Develop shift and levelwise-loop functors, their iterates, and the shift/loop equivalences for spectra.
- [x] Define the zero spectrum, dependent products, truncations, fibers, pullbacks, and products.
- [x] Define the suspension prespectrum and its functoriality. It deliberately remains a prespectrum until spectrification exists.
- [x] Define Eilenberg-Mac Lane spectra and their functoriality.
- [x] Add `theories/Spectra.v` as the library index.

## Critical path: pointed sequential colimits

Current work is in `theories/Pointed/pSequential.v`.

- [x] Define pointed sequences and their underlying ordinary sequences.
- [x] Define pointed cocones, pointed legs, and pointed cocone equations.
- [x] Point the ordinary sequential colimit using the zeroth basepoint.
- [x] Define the canonical pointed cocone, injections, gluing homotopies, and pointed recursor.
- [x] Prove the pointed universal property `equiv_pseq_colimit_rec`.
- [x] Show that deleting the zeroth term does not change the pointed sequential colimit.
- [x] Define the levelwise loop sequence and the canonical comparison
  `pSeqColimit (pseq_loops A) ->* loops (pSeqColimit A)`.
- [ ] Prove that this loop comparison is a pointed equivalence, using the path-space characterization in `Colimits.Sequential`.
- [ ] Determine and state the exact assumptions of that equivalence, especially `Univalence` and any use of `Funext`.
- [ ] Add the functoriality on maps and homotopies of pointed sequences needed by spectrification.
- [ ] Promote `pSequential.v` from working-tree development to settled library material and validate its public imports.

## Critical path: spectrification

For a prespectrum `X`, the intended level `n` of its spectrification is the pointed sequential colimit

```text
colim_k Omega^k X_(n+k).
```

- [ ] Define the pointed sequence `k |-> Omega^k X_(n+k)` and its transition maps from the prespectrum structure.
- [ ] Define the levels of `spectrify X` as their pointed sequential colimits.
- [ ] Construct the structure equivalence at each level from:
  - deletion of the zeroth term;
  - the prespectrum structure maps;
  - the equivalence between the colimit of loops and the loop space of the colimit.
- [ ] Assemble those levels with `spectrum_from_sequence`.
- [ ] Define spectrification on maps and homotopies and package it as a wild functor where appropriate.
- [ ] Define the unit map from a prespectrum to its underlying spectrified prespectrum using the zeroth colimit injections.
- [ ] Prove naturality of the unit.
- [ ] Show that spectrification fixes spectra up to levelwise equivalence.
- [ ] State and prove the expected universal property of spectrification if the preceding construction supplies it cleanly.
- [ ] Define the suspension spectrum by spectrifying `suspension_prespectrum`.
- [ ] Define the sphere spectrum as the corresponding suspension spectrum of the pointed zero-sphere.

## Wild limits and colimits track

### General machinery

Current work is in `theories/WildCat/LimitsScratch.v`.

- [x] Define adjunctions enriched in 0-groupoids (`GpdAdjunction`).
- [x] Construct them from unit/counit data and prove composition and transport along natural equivalences.
- [x] Lift adjunctions pointwise to functor categories.
- [x] Define diagonal functors, `HasLimit`, `HasColimit`, and preservation of limits and colimits.
- [x] Prove that right adjoints preserve limits and left adjoints preserve colimits.
- [x] Construct provisional pointwise limits and colimits in `Fun01` categories.
- [x] Prove the provisional abstract Fubini equivalence `equiv_colimit_colimit`.
- [x] Define the walking span and state the provisional abstract span-colimit 3-by-3 equivalence.
- [ ] Refactor `diagonal`, `HasLimit`, and `HasColimit` so that the category of graph-indexed diagrams is `Fun02`, not `Fun01` with arbitrary pointwise 2-cells.
- [x] Define coherent evaluation and argument swap, including the hom 0-groupoid equivalence for swapping arguments.
- [x] Prove the two naturality laws for the swap hom equivalence and package argument swap as a `GpdAdjunction`.
- [x] Define the underlying coherent postcomposition map on `Fun02` objects and natural transformations.
- [x] Determine the minimum coherence required of postcomposition: a `Fun12` suffices through natural transformations, while mapping modifications requires a `Fun22` action on cylinders.
- [x] Define the underlying pointwise coherent limit and colimit candidates by composing argument swap with coherent postcomposition.
- [ ] Promote coherent postcomposition to a `Fun12` for a `Fun22` codomain functor.
- [ ] Reprove pointwise limits and colimits and the Fubini equivalence through the coherent diagram category.
- [ ] Replace remaining costly elaboration (`refine` and inferred functors) with explicit functors and `nrefine`/`napply` where the goal determines the data.
- [ ] Reduce `Typeclasses Depth 4` in `LimitsScratch.v` if the coherent interface permits it.

### Coherent functors between (2,1)-categories

Current work is in `theories/WildCat/Cylinder.v` and `theories/WildCat/TwoFunctor.v`.

- [x] Fix the hierarchy: the first index records functor coherence and the second index records genuine coherent higher cells (`Fun02`, `Fun12`, and eventually `Fun22`).
- [x] Remove the redundant `IsLocally1Functor` class; hom-wise functoriality is a field of `Is2Functor` itself.
- [x] Define `Is2Functor` with hom-wise functoriality, naturality of the compositor, and associativity/unit coherence.
- [x] Write down the prospective `Fun22`, pseudonatural-transformation, and modification data, while keeping it off the immediate critical path.
- [x] Establish the missing relation between `cat_assoc_opp` and the inverse associator in `Is21Cat` and its current instances.
- [x] Define a generic `Cylinder` between squares with fixed horizontal boundary.
- [x] Prove identity, composition, inverse, and boundary-rewriting operations for cylinders.
- [x] Define concatenation above and below directly by pasting associator-naturality, functoriality, and interchange squares, then use them to define general vertical concatenation.
- [x] State horizontal concatenation of cylinders, completing the three expected composition directions together with native front-to-back composition.
- [x] State the associativity, left-unit, and right-unit cylinders for vertical concatenation of squares.
- [x] Use `cylinder_vconcat_below` to reduce `natmod_postcompose` to a one-step application.
- [x] Use `cylinder_vconcat_above` to reduce `natmod_precompose` to a one-step application.
- [x] Define coherent modifications `NatModification` using `Cylinder` rather than an opaque higher `Square`.
- [x] Define identity, composition, and inverses of `NatModification` via the generic cylinder operations.
- [x] Define postcomposition and precomposition of `NatModification`; these proofs should later be replaced by generic cylinder-pasting lemmas.
- [x] Define the forgetful map `Fun02 -> Fun01` and induce `IsGraph` and `Is01Cat` from `Fun01`.
- [x] Add the coherent `Is2Graph` on `Fun02` using `NatModification`.
- [x] Define the hom 1-category, hom 1-groupoid, and pre/postcomposition functor structures pointwise for `Fun02`.
- [x] State a constructor showing that the three cylinder-coherence laws are the only missing inputs for `Is1Cat (Fun02 A B)`.
- [x] Define the forgetful maps from `Fun12`; induce its categorical tower consistently through `Fun12 -> Fun02`, retaining `Fun12 -> Fun11` only as a forgetful map.
- [x] Replace the admitted proof of `square_vconcat_assoc`.
- [ ] Streamline the boundary-reassociation steps in the proof of `square_vconcat_assoc`.
- [ ] Replace the admitted proof of `square_vconcat_idl`.
- [ ] Replace the admitted proof of `square_vconcat_idr`.
- [x] Prove `cylinder_hconcat` by a direct pasting of square operations.
- [ ] Derive horizontal whiskering operations for cylinders from `cylinder_hconcat` and the appropriate degenerate cylinders.
- [x] Install `Is1Cat (Fun02 A B)` from the three cylinder lemmas; the two unitor lemmas still have the TODOs above.
- [x] Finish the easy pointwise fields of `Is21Cat (Fun02 A B)` and install the instance.
- [x] Induce the corresponding coherent structure on `Fun12` from `Fun02`.
- [ ] Replace the current `Fun02`, `Fun12`, and `Fun22` records by the intended nested sigma presentation.
- [ ] Connect the pointwise colimit construction in `LimitsScratch.v` to `Fun02` as the graph-indexed diagram category.
- [x] Remove the former raw/wrapper indirection from the above/below cylinder pastings; the public lemmas are the direct calculations.
- [ ] Decide precisely which lower structures, if any, `Fun22 -> Fun12` can induce once pseudonatural transformations are chosen as its 1-cells.
- [ ] If coherent postcomposition requires `Is2Functor`, move the necessary `Fun22` identity/composition infrastructure onto the smoke-test critical path.
- [ ] Define identity and composition for `Fun22` and prove their `Is2Functor` laws.
- [ ] Define identity and composition of pseudonatural transformations.
- [x] Define identity, composition, and inverses of modifications between pseudonatural transformations.
- [ ] Build the full graph/category structures on `Fun22` categories if later applications require them.
- [x] Define the bundled universe `OneGpd` of wild 1-groupoids, with 1-functors as morphisms, natural transformations as 2-morphisms, and pointwise 2-morphisms as 3-morphisms.
- [x] Prove generically that natural transformations into a 1-groupoid can be inverted and hence that `Fun11 A B` is a 1-groupoid when `B` is.
- [x] Construct the wild 1-category structure on `OneGpd` and the hom-wise 1-functor structures needed for its `(2,1)`-category structure.
- [x] Finish the associator/unitor naturality and coherence fields of `Is21Cat OneGpd`.
- [x] Equip `OneGpd` with equivalences given by bi-invertible 1-functors, which is the structure required to state the 1-groupoid-valued Yoneda equivalence.
- [ ] Develop practical constructors and cancellation lemmas for equivalences of 1-groupoids; defer the fully-faithful/essentially-surjective characterization until an application needs it.
- [x] Define the three 1-groupoid-valued representables `opyon0_1gpd : Fun02 A OneGpd`, `opyon1_1gpd : Fun12 A OneGpd`, and `opyon2_1gpd : Fun22 A OneGpd`.
- [x] Prove the fully coherent 1-groupoid-valued Yoneda equivalence for `opyon2_1gpd : Fun22 A OneGpd`, with pseudonatural transformations and modifications as its hom 1-groupoid.
- [ ] Formulate the lower `Fun02` and `Fun12` Yoneda equivalences using the appropriate coherent transformation strata; their present ordinary-natural-transformation homs do not contain the 2-cell naturality needed by the Yoneda retraction.
- [ ] Bundle wild `2Gpd` when the 2-groupoid-valued Yoneda development needs it.
- [ ] Move stable definitions out of the scratch file and choose their permanent module boundaries.

Performance note: `TwoFunctor.v` currently uses `Typeclasses Depth 3`; depth 2 cannot resolve the graph structure on 3-cells. The former long whiskering proofs now live once, generically, in `Cylinder.v`; their clients elaborate immediately.

### Local Kan-extension experiment

Current work is in `theories/WildCat/KanScratch.v`.

- [x] Define a local left Kan extension relative to a restriction functor by requiring its canonical map on hom 0-groupoids to be an equivalence.
- [x] Package local left Kan extensions and their global existence using sigma types.
- [x] Isolate corepresentability of a 0-groupoid-valued cocone functor and identify the local Kan-extension property with this corepresentability condition.
- [x] Formulate the Kan-style pushout property by corepresenting `PushoutRecData`, and prove that the ordinary HIT pushout has it.
- [x] Prove the generic pasting calculation: successive universal maps agree with the canonical map for the pasted unit up to the compositor and associator.
- [x] Prove that two local left Kan extensions paste to a local left Kan extension for the composite restriction functor.
- [x] Define coherent restriction of `Fun02` diagrams along a graph map, including its action on natural transformations and modifications.
- [ ] Prove uniqueness of local left Kan extensions at the level needed to compare their extension objects.
- [ ] Decide on the indexing-shape structure for which restriction along `J -> 1` is genuinely the constant-diagram functor. The present graph-only `Fun02` experiment deliberately leaves this unresolved.
- [ ] Define the walking-span product shape and its two projections in that indexing language.
- [ ] Show that the three row or column pushouts assemble into the corresponding local left Kan extension along a projection.
- [ ] Apply pasting along each projection followed by the terminal map, identify the two composite restrictions, and then use uniqueness to obtain pushout 3-by-3.
- [ ] Compare the resulting proof and required infrastructure with the direct coherent-colimit route before choosing the permanent definition.

### Pushouts and the 3-by-3 test

Current work is in `theories/WildCat/PushoutScratch.v`.

- [x] Define pushout recursion data and its coherent morphisms.
- [x] Give this recursion data its 0-groupoid structure.
- [x] Prove the 0-groupoid-valued universal property of the ordinary pushout.
- [x] Repackage that universal property as corepresentability of the span-cocone functor in `KanScratch.v`.
- [x] State the concrete pushout 3-by-3 equivalence.
- [x] Reduce the concrete statement, via Yoneda, to a natural equivalence between the two pushout-recursion-data functors.
- [ ] Identify natural transformations out of a walking-span diagram with `PushoutRecData`.
- [ ] Instantiate `HasColimit Type WalkingSpan` with the ordinary pushout.
- [ ] Instantiate pointwise walking-span colimits in the relevant functor category.
- [ ] Obtain the concrete pushout 3-by-3 lemma from `equiv_span_colimit_3_by_3`.
- [ ] Compare that proof with the direct recursion-data computation and retain only the reusable supporting lemmas.

The pushout work should remain in its separate scratch file while it is experimental; it imports the general limits scratch file.

### Immediate route to the smoke test

- [x] Assemble the `Is21Cat` structure on `Fun02` and induce it on `Fun12`; the two unitors currently depend on the explicitly deferred cylinder placeholders.
- [x] Write down the local Kan-extension universal property and prove its basic pasting theorem.
- [x] Verify that the ordinary pushout satisfies the corresponding corepresentability statement for concrete span-cocone data.
- [ ] Prove local Kan-extension uniqueness and settle the terminal/walking-span indexing shapes.
- [ ] Test whether the pushout constructions give the required projection Kan extensions without first building global coherent postcomposition.
- [ ] If that test fails, return to the coherent diagonal, evaluation, argument-swap, and postcomposition route and build only the required part of `Fun22`.
- [ ] Express natural transformations from a `WalkingSpan` diagram to a constant diagram as `PushoutRecData`, including the coherent 2-cells.
- [ ] Use `pushout_rec_natequiv` to instantiate the ordinary pushout as `HasColimit Type WalkingSpan`.
- [ ] Instantiate the pointwise `WalkingSpan` colimit in the coherent diagram category.
- [ ] Obtain `pushout_3_by_3_statement` either from Kan-extension pasting and uniqueness or from the refactored coherent Fubini theorem.

## Structured-object investigation

Current exploratory work is in `theories/WildCat/SectionsScratch.v`.

- [x] Describe pointed types and successor structures as wild lax equalizers at the object and morphism levels.
- [x] Identify why continuing uniformly to the `(2,1)`-categorical level needs coherent functors and modifications.
- [ ] Return to the generic lax-equalizer/displayed-category construction only after the coherent functor machinery is usable.
- [ ] Check whether this abstraction genuinely shortens the existing direct structures on `Type`, `pType`, and successor structures before promoting it.

## Design decisions to preserve

- Use `ps` prefixes for prespectrum operations and `s` prefixes for spectrum operations.
- Use `$->` and `$==` throughout for maps and homotopies; map lemmas should use the `smap` naming family.
- Prefer sigma types where a record adds no useful projections or abstraction.
- Prefer tactic proofs, especially `napply`, `snapply`, and `nrefine`, over large explicit proof terms.
- Pass functors and potentially ambiguous instances explicitly in categorical lemmas; use `!` in typeclass binders to avoid duplicate inferred instances.
- Keep named instances.
- The wild-category structure on spectra is induced from prespectra.
- Suspension currently produces a prespectrum; the suspension spectrum is a consequence of spectrification.

## Later developments, not on the immediate critical path

- [ ] Dependent smash products of pointed types and spectra, following the comparison with van Doorn's formulation.
- [ ] Tensor-hom adjunctions for those dependent smash products.
- [ ] General colimits of pointed types and spectra beyond what spectrification requires.
- [ ] Colimits of abelian groups.
- [ ] Homotopy groups of spectra.
- [ ] Exact triangles and triangulated-category structure.

## Validation status

- [x] `Cylinder.v` builds.
- [x] `TwoFunctor.v` builds after introducing cylinders and the forgetful lower structures.
- [x] Rebuild `LimitsScratch.v` after the coherent-functor refactor.
- [x] Rebuild `PushoutScratch.v` after the coherent-functor refactor.
- [x] `git diff --check` currently passes.
- [ ] Run `dune build test/` before the next commit.
- [ ] Run the full `dune test` validation once the current development is ready to leave scratch status.
