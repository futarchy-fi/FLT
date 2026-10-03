# W28 direct polygon ampleness: D04a refinement

The W27 contracts in `MAZUR_W27_SPLIT.md` remain the targets. Each new Lean
module has a whole-file cap of 240 lines. No statement about polynomial matching
is a substitute for actual sheaf sections or ampleness.

## D04a split

| Leaf | Module | Contract and proof design | Status |
|---|---|---|---|
| D04a.1 | ProjectiveLineEndpointCover | The Laurent open plus zero and infinity covers every P1 point. Compute the polynomial evaluation kernel and complement of D(X), then use the two-chart cover. | Elaborated prototype W28_ENDPOINT_COVER.lean passes. |
| D04a.2 | PolygonNormalizationTorusPullback | Show a component normalization pulls its torus back identically. Exclude endpoints using actual node nonsmoothness, then use the torus open immersion. | Elaborated prototype W28_TORUS_PULLBACK.lean passes. |
| D04a.3 | PolygonDivisorNormalizationPullback | Pull back each closed marked section through the torus square; other component factors become the unit ideal by disjoint support; pullback commutes with the finite product. | Elaborated prototype W28_DIVISOR_PULLBACK.lean passes. |

One-gon self-incidence and the two-gon are retained. There is no n >= 3
assumption in this plan. D04b/c and D05–D10 still require the genuine dual-ideal,
power, section-space and projective embedding comparisons listed in W27.

## D04b refinement

D04b.1 `ProjectiveLineMarkedCharts` (cap 240): the actual P1 marked ideal
pulls back on the two charts to evaluation at a and a⁻¹; after the canonical
Spec/global-section coordinate isomorphism its equation is X minus that
coordinate. The pullback square uses the chart monomorphism. Prototype
`W28_MARKED_CHARTS.lean` elaborated, including the ideal equality.
`W28_CARTIER.lean` also elaborated: the marked P1 section is relative Cartier
by the existing smooth-open section theorem.

D04b.2 `ProjectiveLineMarkedDualCoordinates` (cap 240) gives explicit
regular equations and dual-section coordinates for powers on these affine
charts. Prototype `W28_DUAL_COORDINATES.lean` elaborated, including the
canonical-section endpoint formula. Gluing, endpoint comparisons and
comparison with the pullback of the polygon line remain separate obligations.

D04c.1 `PolygonDivisorPowerPullback` (cap 240): arbitrary scheme pullback
commutes with powers by induction using `idealSheaf_comap_mul`; specialize
to normalization and its left/right charts. Prototype `W28_POWER_PULLBACK.lean`
elaborated. This does not identify tensor powers or dual-module pullbacks.

D04b.3 `ProjectiveLineMarkedTransition` (cap 240): compute the Laurent
unit (-a⁻¹) T⁻¹ taking the left regular equation to the right one, its powers,
and the change in dual evaluations. Prototype `W28_TRANSITION.lean` elaborated.
The dual calculation is on the principal Laurent ideal; identifying it with
restrictions of the global polygon line still needs a naturality proof.

## First remaining geometric comparison

For `I = PolygonBoundaryDivisor.ideal K n p a` and
`νᵢ = (componentι K n i ≫ p).left`, construct a natural isomorphism

```lean
(Scheme.Modules.pullback νᵢ).obj (divisorLineBundle I hI) ≅
  divisorLineBundle (markedPoint K (a i)).ker
    (ProjectiveLineMarkedCharts.relativeCartier K (a i)).1
```

and prove that it respects the ideal inclusion, its dual pairing and the
canonical section. The new D04a theorem proves the equality of ideal **data**;
it is not this isomorphism of module sheaves. `idealModuleRestrictIso` in
`DivisorLineBundleRestrict` requires an open immersion; the normalization
component is not an open immersion at its endpoints. The new affine
`sectionsCoordinate` is for the genuine dual of the pulled-back chart ideal,
not yet for the restriction of the polygon's positive divisor line.

Proposed next leaves (each cap 240; no elaborated proof design yet):

| Leaf | Required result | Existing inputs |
|---|---|---|
| D04b.4 | Pullback of the actual invertible ideal module is its comap ideal module when the pulled-back equation remains regular; retain the inclusion map. | `idealModuleι`, the D04a/marked Cartier proofs, local Cartier trivializations, `ModuleSheafMorphismGluing`, `ModuleSheafOpenIsoDetection`. |
| D04b.5 | Dualize that comparison; identify the two affine section coordinates and prove restriction agrees with `dual_transition`. | Actual dual pairing, `DivisorLineBundleRestrict`, `ProjectiveLineMarkedDualCoordinates`, `ProjectiveLineMarkedTransition`. |
| D04c.2 | Transport through `divisorLineBundlePowerIso`; identify the intrinsic endpoint fibers and their canonical-unit trivializations; derive predecessor-oriented matching weights. | `PolygonDivisorPowerPullback`, the new unit/sign formulas, W27's explicit predecessor contract. |
| D05a | Identify genuine P1 H0 with bounded polynomials, with both endpoint evaluation formulas. | Sheaf gluing on the two charts; D04b.5/D04c.2. |
| D05b | Tensor the actual normalization sequence with the line, prove exactness, and compare its maps under projection. | `PolygonNormalizationExact.shortExact`; `ClosedLineProjectionFormula.projectionIso` already works for arbitrary scheme morphisms and locally free rank-one coefficients. |
| D05c | Identify actual polygon H0 with W27's weighted matching kernel. | D05a/b and the computed endpoint maps, not a new surrogate section space. |

This is a dependency refinement, not a size estimate or a claim that a listed
proof will fit without further splitting. In particular, the projection formula
itself is available; its normalization specialization and compatibility with the
branch-difference maps remain to be proved. A source search found no existing
ideal-module or divisor-dual pullback comparison along general morphisms.

The canonical-section endpoint formula alone is not evaluation of an arbitrary
section in a common node fiber. Raw Laurent dual evaluations alone do not prove
sheaf descent. The required matching relation uses the predecessor: zero on i
is identified with infinity on next(i). After identifying intrinsic fibers, a
rational representative p(t)/(t-a)^m has values p(0)/(-a)^m at zero and its
coefficient of degree m at infinity. These comparisons still need proof.

D06a–D10 retain the W27 contracts: generation at all scheme points after field
extension, ratio maps and their gluing, actual O(1) pullback, coordinate-ring
surjectivity on torus and node charts, and the closed immersion. Keep the
self-incidence one-gon chart and both nodes of the two-gon. No ampleness
producer or removal of `Mazur_statement` is claimed by W28.

## Validation

Checked at 2026-10-03 14:17 UTC. All seven modules passed individual foreground
builds and individual `lake exe runLinter MODULE` runs with
`LEAN_NUM_THREADS=2`. The originating-declaration audit checked all 58
declarations, including generated declarations, and admitted only `propext`,
`Classical.choice`, and `Quot.sound`.

| Module | Whole-file lines/cap |
|---|---:|
| `FLT.Mazur.ProjectiveLineEndpointCover` | 54/240 |
| `FLT.Mazur.PolygonNormalizationTorusPullback` | 91/240 |
| `FLT.Mazur.PolygonDivisorNormalizationPullback` | 84/240 |
| `FLT.Mazur.ProjectiveLineMarkedCharts` | 134/240 |
| `FLT.Mazur.PolygonDivisorPowerPullback` | 59/240 |
| `FLT.Mazur.ProjectiveLineMarkedDualCoordinates` | 107/240 |
| `FLT.Mazur.ProjectiveLineMarkedTransition` | 83/240 |

`W28_CONSUMER_CONTRACT.lean` passed with empty output: actual one-gon cubic
and zeroth-power ideal pullback, both two-gon component indices with arbitrary
unit markings, the right-chart reciprocal formula, endpoint signs in
characteristics 2 and 3, bijectivity of the genuine affine divisor-section
coordinates, and the global marked P1 Cartier condition.

Evidence commands: `lake build MODULE`, `lake exe runLinter MODULE`,
`lake env lean GOAL_MAZUR_W28_AXIOM_AUDIT.lean`,
`lake env lean W28_CONSUMER_CONTRACT.lean`, and `python3 W28_CHECK_SOURCE.py`.
Per-module logs, the full axiom report, consumer report and source-scope check
are untracked `GOAL_MAZUR_W28_*` artifacts in the worktree root. The scope
check verifies new Lean files only, sorted aggregate imports, line caps,
admission scan, clean validation logs and whitespace. No whole-library build
or lint was run. The final FLT theorem was not re-audited; source inspection
still finds `Mazur_statement` and its `mazur_W` consumer.
