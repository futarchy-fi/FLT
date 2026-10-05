# Affine open-immersion descent in fixed integer models

This increment proves that a fixed map of finite-presentation coefficient
models recovering an affine open immersion becomes an open immersion after
coefficient enlargement. It also descends recovered equations between model
maps. It does not finish L1, construct overlap pullback identifications, or
remove `Mazur_statement` from the FLT endpoint.

## Main contract

`exists_integer_model_openImmersion` takes finite presentations `P` and `Q`
over a ring `A`, a finite-type integer coefficient stage `A₀`, a model map
`f`, and an original algebra map `φ` recovered by `f`. If `Spec.map φ` is an
open immersion, it returns a finite-type stage `S ≥ A₀` where the actual
`integerModelTransportHom P Q h f` induces an open immersion. The result
retains any prescribed finite set of base coefficients.

No principal cover, localized inverse, flatness, or injectivity of recovery
is assumed. The finite-presentation inputs are the existing affine-chart
presentations; this is not a new finite-presentation hypothesis for the
proper-only form of 0D2S.

`exists_integer_model_finite_openImmersions` does this simultaneously for
any finite family of arrows. It retains the initial stage for empty families.
Established diagram laws and pullbacks remain available through the existing
transport lemmas.

## Construction

1. Extract finite target denominators from the original open immersion.
2. Lift them into an enlargement of the fixed target presentation model.
3. Lift the source-cover coefficients, then make their unit-ideal equation
   hold by eventual vanishing. Recovery need not be injective.
4. Construct the canonical localized algebra maps and their recovery.
5. Descend the localized isomorphisms separately, preserving their chart maps.
6. Transport the equivalences to a common stage and identify them with the
   canonical restrictions of the transported map.
7. Apply `isOpenImmersion_of_localized_bijective`, the sufficient direction
   of the finite affine criterion.

## Supporting modules

| Module | Result |
| --- | --- |
| `PrincipalIntegerRestriction` | Canonical localized algebra maps and recovery by localization extensionality |
| `LocalizedIntegerComparisonTransport` | Localized equivalences retain full chart compatibility under enlargement |
| `FiniteLocalizedIntegerComparisons` | Finite canonical comparisons descend at a common coefficient stage |
| `FixedModelElementLifts` | Finite element families lift while retaining the fixed presentation |
| `IntegerModelCoverDescent` | Recovered finite principal covers descend with explicit unit-ideal witnesses |
| `PrincipalRestrictionEquivalence` | Canonical algebra equivalences on principal target opens and bijectivity detection |
| `IntegerModelOpenImmersionRefinement` | Descent from a fixed finite principal refinement |
| `IntegerModelOpenImmersionDescent` | Unconditional eventual open immersion for a fixed map recovering one |
| `FiniteOpenImmersionIntegerDescent` | A common stage for finite families of affine open immersions |
| `IntegerModelRelationDescent` | Recovered map equalities and triangle equations descend |
| `FiniteIntegerModelRelations` | Finitely many recovered equations hold at a common stage |

## Remaining ordered work

1. **L1 / 0D2S:** construct and descend the canonical overlap pullback
   comparisons. The existing pullback transport theorem only preserves a
   pullback already established at a stage. A useful next leaf is the
   canonical tensor-product comparison for a recovered affine pullback,
   followed by its compatibility with coefficient model enlargement.
   Apply eventual isomorphism descent to that comparison, and combine the
   finite diagram equations and open immersions in an actual overlap atlas.
   The new triangle theorem descends supplied recovered cocycle equations;
   no geometric triple-overlap atlas has yet been constructed.
2. Descend transition units, glue the family and invertible sheaf, and prove
   their pullback identifications. Descend properness and fiber data. The
   proper-only 0D2S case still needs inverse-system approximation, without
   adding a finite-presentation hypothesis.
3. Descend an ample fiber presentation, prove the Noetherian ample
   neighborhood **L2 / 0D2N**, and transfer through approximation.
4. **A7–A8:** compatible level isomorphisms, quotient/presheaf coherence,
   and the exact-order rational-point/subgroup bridge.

## Verification

The reproducible checks are one foreground `LEAN_NUM_THREADS=2 lake build
FLT.Mazur.MODULE` and one `lake exe runLinter FLT.Mazur.MODULE` for each module,
then an originating-declaration audit allowing only `propext`,
`Classical.choice`, and `Quot.sound`. The root check is a single foreground
`LEAN_NUM_THREADS=2 lake build FLT` after merging `origin/main`.
The untracked W81 handoff records checked-at time, command results, commits,
and source hashes for this run; this document states mathematical contracts.
