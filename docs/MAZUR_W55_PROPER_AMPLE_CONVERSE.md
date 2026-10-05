# W55: proper ample converse

`FLT.Mazur.FCurve.RelativelyAmpleLineBundle.relativeAmple` proves the
proper ample converse over arbitrary bases. For a locally free rank-one
sheaf, `relativeAmple_iff_proper_and_relativelyAmple` gives the exact comparison:

```lean
RelativeAmple f L ↔ IsProper f ∧ RelativelyAmpleLineBundle f L
```

The properness hypothesis is necessary because `RelativeAmple` uses closed
projective presentations. The converse requires no Noetherian or reducedness
hypothesis. The source scheme and coefficient ring may be empty or trivial.

## Construction

`AffineOpenDenominators` clears functions and restriction kernels on arbitrary
affine principal opens, including finite dependent families. In a finite
cover by section generator opens, section ratios identify pair and triple
intersections with principal opens. `SectionCoverCoordinates` supplies the
chart numerators. `SectionCoverDiscrepancy` kills their overlap differences
with one further power.

`SectionPowerGluing` glues the corrected coefficients in the actual tensor-power
sheaf. `AmpleChartSectionExtension` proves extension of any chart function
in every sufficiently large degree and of any finite family in one positive
degree. `AmpleChartGeneratorRatios` realizes finite chart-algebra generators
as ratios of these global sections.

`SectionProjectiveImmersion` proves the immersion criterion from surjectivity
of the actual chart ring maps on a subcover. `SectionChartGenerators` derives
that surjectivity from algebra generators. `FiniteSectionProjectivePresentation`
combines denominators and numerators into a finite section family; a dummy zero
coordinate also handles an empty cover. Properness closes the immersion, and
the existing O(1) comparison identifies its line bundle.

`ProperAmpleConverse` applies this construction on each affine base open and
transports the tensor powers through restriction. Each new module is under
240 lines. The proof introduces no conclusion-bearing record.

## Remaining work

The next A6 gap is general relative ampleness locality and arbitrary base
change. The existing `relativeAmple_affinePower_baseChange` transports a
supplied global affine-base presentation. It does not establish the required
presentations on every affine open after an arbitrary base change. The new
comparison theorem makes section ampleness available for this next step.

General fppf descent also remains. Component degree/support positivity and the
arbitrary-base fiberwise ampleness criterion require the degree and
cohomology/approximation work identified in `MAZUR_W52_SPLIT.md`, F1–L3.

A7 needs ample-level transport and descent before constructing its quotient
presheaf. A8 still needs an exact-order rational point to finite étale subgroup
construction, smooth-fiber ampleness, and generator invariance. W55 does not
remove `Mazur_statement` from the Fermat endpoint.

## Recheck

Build each of the ten new modules with `LEAN_NUM_THREADS=2 lake build MODULE`,
then lint each separately with `lake exe runLinter MODULE`. Import
`FLT.Mazur.ProperAmpleConverse` and print the axioms of
`FLT.Mazur.FCurve.RelativelyAmpleLineBundle.relativeAmple` and
`FLT.Mazur.FCurve.relativeAmple_iff_proper_and_relativelyAmple`.
The allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.

The untracked W55 validation artifacts record individual builds/lints, an
exhaustive audit of originating declarations, the old converse contract now
inhabited, a nonreduced `ZMod 4` consumer, an empty-family extension consumer,
and the post-main-merge root build. `BLOCKED.md` records their checked-at time
and commit hashes; `W55_CHECK_SOURCE.py` reruns the scope and evidence checks.
