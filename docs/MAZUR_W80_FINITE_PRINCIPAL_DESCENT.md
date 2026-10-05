# Finite principal refinements for affine overlap descent

This increment advances L1 / 0D2S. It does not prove L1, descend a general
open immersion to a coefficient model, glue a family, or remove
`Mazur_statement` from the Fermat endpoint.

## Common stages and retained data

`IntegerModelOpenImmersionBaseChange` identifies the spectrum square of a
transported model map as a pullback. An established open immersion therefore
survives every further coefficient enlargement. No flatness of the coefficient
inclusion is assumed.

`CommonCoefficientStage` constructs a finite-type integer subalgebra above
finitely many finite-type coefficient stages and a prescribed finite set.
Its extension form retains the initial stage even for an empty family.

`FinitePrincipalChartIntegerDescent` applies the single-chart theorem to each
member of a finite family and transports all resulting open immersions to
that common stage. Each resulting map is the transport of its original fixed
map; no new chart map is substituted.

`IntegerModelDiagramTransport` preserves identity and composition equations,
triangle relations, principal covers, and chosen unit-ideal cover equations.
`IntegerModelPullbackTransport` preserves an already established cartesian
square between four fixed models. These are preservation results: they do
not construct missing overlap pullback identifications or cocycles.

## Finite algebraic criterion for general affine open immersions

`PrincipalRefinementOpenImmersion` proves a source-cover criterion with
fiber-saturated charts, deriving injectivity rather than assuming it for the
principal-refinement application. Pullbacks of target principal opens are
fiber-saturated, so their restricted maps detect an affine open immersion.

`FinitePrincipalTargetRefinement` chooses finitely many target denominators
whose principal opens lie inside the image and whose inverse images cover
the affine source. Compactness of the source supplies finiteness.

`PrincipalTargetRestrictionIsomorphism` proves that the canonical localized
restriction on each such target open is an isomorphism of spectra and a
bijective ring map. It uses the actual localization pullback square.

The resulting theorem in `AffineOpenImmersionLocalizationCriterion` is:

```text
Spec(f) is an open immersion
  iff there exists a finite set t of target denominators such that
    the opens D(f(r)), r in t, cover Spec(source ring), and
    each canonical map R[1/r] -> S[1/f(r)] is bijective.
```

Here `f : R -> S`, so `R` is the ring of the target scheme. The criterion
also allows empty covers, covering the zero-ring case.

## Canonical localized comparison descent

`LocalizedIntegerModelIsomorphism` starts with a map between two canonical
localizations of fixed models, together with an algebra isomorphism recovered
over the original base. It descends invertibility to a larger coefficient
stage, where both ends are again canonical localizations of the enlarged
models. Compatibility holds on every old localized element.

`LocalizedIntegerChartComparison` upgrades compatibility on old chart elements
to compatibility on the entire enlarged model. Such a comparison certifies
that the actual composite chart map is an open immersion.

The isomorphism over the original base is legitimate input supplied by the
principal-target restriction theorem. No inverse at a coefficient stage is
assumed; it is obtained from isomorphism descent.

## Next work

1. Lift the finitely many target denominators and their source-cover witnesses
   into fixed models. Construct the canonical localized model restrictions
   and prove recovery from the original affine map.
2. Apply the localized comparison theorem to this finite family at one common
   stage, retaining the canonical restriction maps and the source cover.
   The finite algebraic criterion then yields general overlap open immersions.
3. Descend the overlap pullback identifications and triple-overlap equations
   at the common stage. The preservation lemmas above retain them thereafter.
4. Descend transition units, glue the family and invertible sheaf, and prove
   pullback identifications. Properness and fiber data still need descent;
   proper-only 0D2S still requires inverse-system approximation without an
   extra finite-presentation hypothesis.
5. Prove the Noetherian ample neighborhood L2 / 0D2N and transfer it through
   approximation. Then address A7–A8 and the rational-point/subgroup bridge.

## Validation commands

For each of the eleven new modules: foreground
`LEAN_NUM_THREADS=2 lake build MODULE`, then `lake exe runLinter MODULE`.
An originating-declaration audit permits only `propext`, `Classical.choice`,
and `Quot.sound`. The untracked W80 handoff records the checked commit,
validation logs, source hashes, and the post-merge root build.
