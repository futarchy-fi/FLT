# Canonical flat base change of global sections

This document records theorem contracts and their dependency boundary. The
W59 handoff and validation logs, outside `FLT/` and `docs/`, record run results.

## Chart transport (D2c)

`ModulePullbackSectionCoherence.open_unit_top` proves that the actual
`FCurve.modulePullbackOpenIso p U M` carries the ambient pullback unit on a
section of `M` over `U` to the pullback unit on the restricted chart. Neither
scheme needs to be affine, and the module need not be locally free or
quasi-coherent. The proof uses the mate of the restriction square and
naturality across the equalities identifying a chart's top open.

`OpenModuleSectionScalars.chartIso` identifies ambient sections and global
sections of the restricted module, linearly over the original base ring.
`AffineOpenCartesianSections.sectionsIso` applies the affine cartesian
comparison to the restricted square and transports back to ambient sections.
Its `sectionsIso_tmul` theorem retains the actual unit, rather than merely
asserting existence of an abstract module isomorphism.

For a cartesian square

```text
P --p--> X
|        |
q        f
|        |
v        v
T --g--> S
```

`CartesianOpenSectionMap.comparison h M U` is the tensor extension of the
actual sheaf adjunction unit. It is defined on every open, before any
quasi-coherence, affineness or flatness assumptions. Its source is

```text
Γ(T,O) ⊗[Γ(S,O)] Γ(U,M),
```

and its target is `Γ(p⁻¹U,p* M)`. Both module structures retain the original
structural maps. A pure tensor `b ⊗ m` maps to the restriction of `q*(b)` times
the pullback-unit section of `m`.

When `S,T` and the open `U` are affine and `M` is quasi-coherent,
`comparison_isIso` proves this canonical map invertible. No affineness of
`X` or `P` is required. `CartesianSectionRestriction` identifies restriction
of this map with the actual base-linear restriction maps used in the section
equalizer, including arbitrary tensors, not only pure tensors.

## Finite gluing and global base change (D2d)

`FlatCartesianSectionGluing.comparison_bijective` works with a finite affine
cover and affine pairwise intersections. It applies the existing flat tensor
equalizer to the original sheaf. Injectivity follows from chart injectivity;
local inverse images of an upstairs global section agree on overlaps and
therefore give a unique global tensor. The sheaf equalizer then identifies
its image with the original upstairs section.

`FlatGlobalSectionBaseChange.comparison_isIso` chooses a finite affine
subcover and derives affine intersections from separatedness. Its assumptions
are exactly:

- An actual cartesian square as above, with `S` and `T` affine.
- `CompactSpace X` and `X.IsSeparated`.
- `Flat g` and `M.IsQuasicoherent`.

There is no affineness hypothesis on `X`, no finite-presentation or Noetherian
hypothesis, no reducedness hypothesis, and no line-bundle hypothesis. The
finite-equalizer API is in universe zero, so this global result uses `Scheme`
in universe zero; chart transport is universe-polymorphic.

`sectionsIso` is `asIso` of that same canonical map. `sectionsIso_tmul` gives
the unit formula and `sectionsIso_restrict` gives restriction naturality on
all tensors. `FlatGlobalSectionExpansion.exists_sum_pullGlobal` expresses
every upstairs global section as a finite linear combination over `Γ(T,O)`
of pullbacks of downstairs global sections.

## Evaluation compatibility

`ModuleGlobalEvaluationPullback.evaluation_pullback` proves that pullback of
the actual global evaluation morphism is evaluation at the pulled-back
sections, after the canonical free-sheaf pullback isomorphism. This holds for
arbitrary families and arbitrary scheme morphisms. Epimorphic evaluation is
therefore preserved by pullback (`evaluation_epi`). This is preservation;
faithfully flat reflection of epimorphic evaluation is a separate obligation.

## Remaining route to A6 and the Mazur endpoint

The next missing bridge is reflection of generation through faithfully flat
pullback, using the finite expansions and evaluation compatibility above.
It must apply to the actual module evaluation morphism. An abstract field
assuming generation or ampleness descent would not discharge this bridge.

The existing finite-coordinate projective-space construction does not supply
the full graded section-algebra Proj construction or its ample/open-immersion
criterion. The latter, its compatibility with base change, and descent of
the associated open immersion still require proofs. These results are needed
to turn the affine fpqc refinement into reflection of relative ampleness.

The arbitrary-base fibre-to-neighborhood theorem, component degree/support
and ample-degree criterion remain subsequent obligations. A7–A8 still need
ample cyclic-level quotient/presheaf descent, exact-order rational-point
finite étale subgroup constructions, ample levels and generator invariance.
None of the new results identifies these conclusions with assumptions or
alters the existing Mazur endpoint declaration.
