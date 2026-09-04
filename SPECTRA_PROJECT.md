# Spectra and spectrification project

This file records the direction of the current development. It is a working checklist, not library documentation; update it whenever a milestone is completed or the design changes.

## Goal

Construct spectrification of prespectra and use it to turn the existing suspension prespectrum into the suspension spectrum. The critical mathematical input is the interaction between loops and sequential colimits of pointed types.

There is a parallel categorical track developing wild limits. Its final smoke test is an abstract pullback 3-by-3 theorem obtained from pointwise limits in functor categories and limit Fubini. The entire colimit theory, including pushouts and pushout 3-by-3, is then derived by applying the limit theory to opposite categories and opposite diagrams. This infrastructure is useful, but it should not unnecessarily block the direct construction of spectrification.

The existing coherent-colimit and `Type`-specific pushout work is a prototype and regression target, not the permanent architecture. The replacement direction is to make a coherent diagonal-limit adjunction primitive for a chosen limit operation. Its induced `GpdAdjunction` gives the local universal property in the 0-groupoid of coherent cones, whose morphisms are cylinder-coherent modifications. This deliberately avoids asking the generic pointwise perturbations of `Fun02` to reflect coherence stored in paths of `Type`. Pointwise limits, limit Fubini, and walking-cospan pullback 3-by-3 should be derived from that adjunction; pushout results remain thin dual consequences.

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

## Wild limits track and dual colimits

### General machinery

Current work is in `theories/WildCat/LimitsScratch.v`.

The checked entries below record useful scratch prototypes. They do not fix the
permanent dependency direction. `WILDCAT_LIMITS_DESIGN.md` is authoritative:
universal cones and limits are primitive; every colimit construction is
obtained through opposite-category duality.

- [x] Define adjunctions enriched in 0-groupoids (`GpdAdjunction`).
- [x] Construct them from unit/counit data and prove composition and transport along natural equivalences.
- [x] Lift adjunctions pointwise to functor categories.
- [x] Define diagonal functors, `HasLimit`, `HasColimit`, and preservation of limits and colimits.
- [x] Prove that right adjoints preserve limits and left adjoints preserve colimits.
- [x] Construct provisional pointwise limits and colimits in `Fun01` categories.
- [x] Prove the provisional abstract Fubini equivalence `equiv_colimit_colimit`.
- [x] Define the walking span and state the provisional abstract span-colimit 3-by-3 equivalence.
- [x] Define the coherent `Fun02` versions of diagonals, limits, colimits, and double cocones without relying on the arbitrary pointwise 2-cells of `Fun01`.
- [x] Define coherent evaluation and argument swap, including the hom 0-groupoid equivalence for swapping arguments.
- [x] Prove the two naturality laws for the swap hom equivalence and package argument swap as a `GpdAdjunction`.
- [x] Define the underlying coherent postcomposition map on `Fun02` objects and natural transformations.
- [x] Determine the minimum coherence required of postcomposition: a `Fun12` suffices through natural transformations, while mapping modifications requires a `Fun22` action on cylinders.
- [x] Define the underlying pointwise coherent limit and colimit candidates by composing argument swap with coherent postcomposition.
- [x] Promote coherent postcomposition to a `Fun12` for a `Fun22` codomain functor.
- [x] Prove the conditional pointwise limits/colimits and Fubini equivalence through the coherent diagram category.
- [x] Prove the specialized pointwise walking-span pushout mate equivalence needed for `Type`, without requiring the stronger global `HasColimit22 Type WalkingSpan` interface.
- [x] Package the coherent pointwise construction as `gpd_adjunction_pointwise_colimit_fun02`, prove the full universal properties `pointwise_colimit02_iscolimit` and `pointwise_colimit02_cocone_iscolimit`, and register the conditional instance `hascolimit02_fun02`.
- [x] Construct `IsCoherentDiagonal02 (Fun02 A B) J` and `HasPointwiseDiagonalComparison02` generically, including the cylinder relating the two identity-like naturality squares.
- [x] Determine whether the packaged functor-category colimit can be made definitionally pointwise: under the current `IsCoherentDiagonal02` interface the diagonal comparison is necessary, since that class does not constrain the chosen action on 2-cells to be the componentwise one.
- [x] Diagnose the obstruction in the permanent `OneGpd`-valued `IsLimitCone`: pointwise perturbations compare modification components but not their cylinders, so the ordinary pullback of arbitrary types cannot satisfy the demanded local injectivity.
- [x] Select the replacement interface: a chosen limit operation is packaged by a coherent right adjunction to the diagonal, and its local universal property is the induced `GpdAdjunction` equivalence between coherent hom 0-groupoids.
- [x] Generalize the intrinsic unit/counit/triangle fields of `CubicalAdjunction` to `Fun12` adjoints, without requiring an action on arbitrary top perturbations.
- [x] Instantiate the walking-cospan `Fun12` and its diagonal `GpdAdjunction` in `Type` with ordinary homotopy pullbacks; its counit is definitionally the canonical pullback cone.
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
- [x] Connect the pointwise colimit construction in `LimitsScratch.v` to `Fun02` as the graph-indexed diagram category.
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

This experiment is deferred. The universal-cone limit route is the selected
permanent architecture; do not advance the Kan construction unless a later
application needs it independently.

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
- [ ] If resumed, compare its derived pushout theorem with the
      opposite-category consequence of limit Fubini; do not use it as a second
      permanent colimit implementation.

### Existing pushout prototype

Current work is in `theories/WildCat/PushoutScratch.v`.

This file records the existing colimit-first experiment. Its coherent diagonals, argument swap, and Fubini calculations are reusable evidence, but the pointwise pushout mate/unmate construction is not the permanent route. The permanent theorem first proves pullback 3-by-3 from limits in an arbitrary category and then obtains this pushout theorem by applying that result to the opposite category.

- [x] Define pushout recursion data and its coherent morphisms.
- [x] Give this recursion data its 0-groupoid structure.
- [x] Prove the 0-groupoid-valued universal property of the ordinary pushout.
- [x] Repackage that universal property as corepresentability of the span-cocone functor in `KanScratch.v`.
- [x] State the concrete pushout 3-by-3 equivalence.
- [x] Reduce the concrete statement, via Yoneda, to a natural equivalence between the two pushout-recursion-data functors.
- [x] Identify coherent natural transformations out of a walking-span diagram with `PushoutRecData`.
- [x] Instantiate `HasColimit02 Type WalkingSpan` with the ordinary pushout.
- [x] Construct the specialized pointwise walking-span pushout equivalence in the coherent diagram category.
- [x] Prove that the two iterated pushouts corepresent the row and column double-cocone functors.
- [x] Obtain the concrete `pushout_3_by_3` equivalence from `equiv_colimit_fubini`.
- [x] Define coherent specified colimits, `pushout_square_cocone`, and `IsPushoutSquare` so that the face of a square is part of its universal cocone.
- [x] Derive the specified universal cocone of every chosen coherent colimit from its adjunction.
- [x] State the coherent walking-span 3-by-3 equivalence and derive it from abstract Fubini.
- [x] Prove directly from the existing pushout adjunction that the ordinary `pushl`/`pushr`/`pglue` square satisfies `IsPushoutSquare`.
- [ ] Retain the generic `Type` comparison only as a regression test for the
  opposite-category specialization.
- [ ] Remove or relocate the obsolete specialized mate/unmate and direct
  inverse computations once the dual limit route subsumes them.

The pushout work remains in its separate scratch file as a regression and
design reference; permanent limit modules must not import it.

### Permanent universal-cone route to the smoke test

- [x] Move the coherent adjunction and coherent `Fun02` infrastructure needed by the experiment into permanent modules.
- [x] Prototype specified universal cones through a `Fun11` comparison of mapping 1-groupoids and derive the local corecursor API, chosen limit functor, and diagonal `GpdAdjunction`.
- [x] Diagnose why that prototype is too strong for edgeful limits in untruncated `Type`: `is3graph_fun02` forgets modification-cylinder coherence, while equality of pullback paths retains the corresponding higher square.
- [x] Retain the useful lower-dimensional result: the hom 0-groupoid in `Fun02` has cones as objects and cylinder-coherent `NatModification`s as morphisms, unlike the known-defective corner-induced `pullback_0gpd`.
- [ ] Introduce the coherent-adjunction-first chosen-limit interface. It must package a `Fun12` limit operation, cubically natural unit and counit, and triangle modifications, but must not require a `Fun22` action on arbitrary pointwise perturbations.
- [ ] Derive its `GpdAdjunction` and recover local corecursion, beta, eta, and uniqueness from the resulting equivalence of coherent hom 0-groupoids.
- [ ] Build this adjunction directly for walking-cospan pullbacks in `Type`, using `equiv_path_pullback`, `pullback_homotopic`, and path induction for the selected coherence.
- [ ] Rework the pointwise-limit construction to consume the coherent adjunction directly and retain only the cubes used by the pointwise cone.
- [x] Construct limits in `Fun02 I A` pointwise from specified limits in `A`,
      including coherence on transformations and modifications.
- [ ] State coherent preservation for a chosen limit adjunction, without requiring a false `OneGpd` equivalence or unrelated global typeclass choices.
- [ ] Construct the cone mate/unmate equivalence at the coherent hom-0-groupoid level and use it to prove that right adjoints preserve the selected limit operation.
- [ ] Derive abstract limit Fubini as
      `lim_J (lim_I D) $<~> lim_I (lim_J ∘ D)`, retaining compatibility with
      the induced double cones. Argument swap should only re-express the
      second iterated diagram.
- [ ] Specialize both shapes to the walking cospan and derive pullback 3-by-3
      in `Type` first, then isolate exactly which coherent-adjunction fields
      make the argument abstract.
- [x] Add a concrete `Type` presentation regression test:
      `equiv_iterated_cospan_pullback_fubini` takes one coherent double
      cospan and compares its canonical columnwise and rowwise iterated
      pullbacks. The proof reuses `Limits.Pullback.pullback3x3` after a
      generic homotopy normalization; callers supply no reconstructed maps
      or doubled inverse witnesses.
- [ ] Compare the canonical map and boundary beta laws of the `Type`
      specialization with `Limits.Pullback.pullback3x3`.
- [ ] Construct coherent opposite diagrams and expose `Colimit`,
      `HasColimits`, their adjunction, pointwise colimits, and colimit Fubini
      only as wrappers around the corresponding limit results.
- [ ] Obtain pushout 3-by-3 by opposite-category duality and use the existing
      `Type` theorem only to check the specialization.

## Handoff to the next model

The immediate categorical objective is the coherent diagonal-pullback adjunction in `Type`, followed by the limit Fubini smoke test. Do not continue the specialized pushout mate/unmate machinery or attempt to complete the superseded `OneGpd`-valued pullback `IsLimitCone`.

Reusable prototypes already present:

- `TwoYoneda.v` now contains the permanent covariant and contravariant
  `OneGpd`-valued Yoneda constructions used by universal cones.
- `Adjoint.v` now contains `CubicalAdjunction`, its coherent
  postcomposition lift, and the generic composition and natural-equivalence
  transport operations for `GpdAdjunction`.
- `SwapAdjunction.v` contains the permanent coherent argument-swap
  adjunction.
- `PointwiseLimits.v` composes those operations into
  `gpd_adjunction_pointwise_limit_fun02`, conditional on `HasLimit22`.
- `LimitsScratch.v` contains coherent diagonals, argument swap, pointwise
  machinery, and Fubini calculations to inspect while deriving the permanent
  limit-first interfaces.
- `PushoutScratch.v` and `PushoutComparisonScratch.v` provide regression
  statements for the eventual opposite-category specialization.

The coherent diagram, cylinder, adjunction, argument-swap, and pointwise-limit prototypes are reusable. The permanent `OneGpd`-valued local limit API builds, but its top-cell requirement is not valid for ordinary pullbacks of arbitrary types and is now superseded.

The first replacement increment is complete:

- [x] Prototype the walking-cospan pullback as a `Fun12` right adjoint to the
  diagonal, construct its `GpdAdjunction`, and recover the canonical cone's
  hom-0-groupoid universal property.

The remaining increments are:

1. package the selected cubical unit/counit coherence without demanding a
   `Fun22` action on arbitrary pointwise perturbations;
2. drive pointwise limits and abstract Fubini from that coherent adjunction;
3. only then expose colimits and pushouts by duality.

The scratch files last built successfully. Keep them building as reference
material, but do not make permanent modules depend on them.

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
- [x] Rebuild `PushoutComparisonScratch.v` and `PushoutScratch.v` after packaging the full conditional pointwise-colimit theorem.
- [x] `git diff --check` currently passes.
- [x] Build and assumption-audit the permanent coherent-Yoneda module;
      `opyoneda_equiv_1gpd` is closed under the global context.
- [x] Build and assumption-audit the permanent coherent-Yoneda and local
      `OneGpd`-limit prototypes. These checks establish that the definitions
      are well formed, not that ordinary pullbacks instantiate them.
- [x] Reproduce the walking-cospan obstruction at local injectivity: a
      perturbation supplies only pointwise comparisons of modification
      components, while equality of maps into a pullback also compares the
      stored pullback-path square.
- [x] Build and assumption-audit the walking-cospan pullback `Fun12`, its
      diagonal `GpdAdjunction`, and the derived coherent hom-0-groupoid cone
      property; all are closed under the global context.
- [x] Build and assumption-audit
      `PullbackFubiniApplicationScratch.v`; its one-argument canonical
      walking-cospan Fubini equivalence and the reusable pullback homotopy
      helpers are closed under the global context.
- [ ] Package the selected cubical naturality as the full coherent-adjunction
      replacement without requiring a `Fun22` pullback operation.
- [ ] Add the abstract walking-cospan pullback 3-by-3 smoke test.
- [ ] Rerun the full `dune test` validation after the permanent limit-first
      route is integrated.
