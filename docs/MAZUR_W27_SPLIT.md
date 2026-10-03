# W27: ampleness producer, source comparison and bounded leaves

Source check: 2026-10-03; FLT base `be58327f`; Mathlib
`c32e1ec0d1eb5237ba344eee50162f45d5b0fc76`.
The required output is a positive-power `RelativeVeryAmple` witness for the
**actual** `PolygonBoundaryDivisor.ideal`, followed by the existing W26
coefficient comparison. Neither support meeting every component nor the
finite locally free rank of the divisor is this witness.

Every proposed Lean module has a **240-line hard cap**. The three ready leaves
below have full elaborated prototypes, including their proofs, before this
split is committed. The remaining rows are source-checked dependency contracts;
they are **not** checked Lean proofs or certified size estimates. Split those
again before implementation if a proof exceeds its cap. No new ampleness
predicate, assumed presentation, or conclusion-bearing record is permitted.

## Source/API comparison

The Stacks statements and their proofs were read from the linked tags. Local
searches covered Mathlib's `AlgebraicGeometry` directory and `FLT/Mazur`.
Source/API reproduction commands and saved evidence are in the untracked W27
validation files named in the final handoff.

| Mathematical step | Source and hypotheses | Existing Lean source | Missing bridge |
|---|---|---|---|
| Define invertible-sheaf degree | [33.44, 0AYQ](https://stacks.math.columbia.edu/tag/0AYQ): on a proper scheme of dimension at most one, degree is Euler characteristic minus rank times the structure-sheaf Euler characteristic | `ProperCoherentCohomology.proper_coherent_hasFiniteCohomology` supplies coherent cohomology finiteness; `PolygonPureDimension.pureDimension` and `PolygonProper.proper` supply polygon geometry | No matching general degree/Euler-characteristic API was found in Mathlib AG or FLT/Mazur. One must construct the integer invariant and prove exact-sequence and tensor formulas. |
| Tensor degree and effective positivity | [0AYX](https://stacks.math.columbia.edu/tag/0AYX), [0B40](https://stacks.math.columbia.edu/tag/0B40) | `DivisorCanonicalSection.divisorSection`, `divisorSection_nonvanishing`, `DivisorLineBundlePower.divisorLineBundlePowerIso` | Canonical sections are available, but their vanishing length has not been identified with invertible-sheaf degree on each reduced component. `PolygonDivisorDegree.coordinate_degree` is the finite divisor's rank over the base, not this invariant. |
| Positive degree implies ample on an integral proper curve | [0B5X](https://stacks.math.columbia.edu/tag/0B5X) | Coherent finiteness and affine acyclicity exist in FLT | Missing linear growth of H0 from degree, finite-support H1 vanishing in this argument, annihilation by powers of a section [01XR](https://stacks.math.columbia.edu/tag/01XR), and the cohomological ampleness criterion [0B5U](https://stacks.math.columbia.edu/tag/0B5U). |
| Pass from components to the whole proper scheme, dimension at most one | [0B5Y](https://stacks.math.columbia.edu/tag/0B5Y) | `PolygonComponentImages.components_eq`; normalization/component morphisms and properness | The source uses the finite surjection from reduced 1-dimensional components plus isolated points and **finite-surjective descent of ampleness**, [0B5V](https://stacks.math.columbia.edu/tag/0B5V). None of these degree/ampleness implications is supplied by the existing component-support theorem. |
| Compare ample with a positive very-ample power | The usual projective-presentation characterization over a field | `RelativeVeryAmpleLineBundle.RelativeVeryAmple`; `DivisorPowerVeryAmple.exists_relativeVeryAmple_divisorPower_iff` | W26 compares two actual coefficient sheaves, but still needs an embedding or an independently proved ampleness-to-presentation theorem. |
| Use Serre vanishing | FLT's existing theorem | `RelativeSerreVanishing.relativeVeryAmple_eventually_acyclic` | Its input already is `RelativeVeryAmple`. Using it to manufacture that input is circular. |
| Match normalized sections at nodes | Polynomial endpoint restriction and normalization equalizer | Mathlib `Polynomial.degreeLT`, `degreeLTEquiv`; FLT `PolygonNormalizationExact.abelianSheaf_shortExact`, `PolygonNodeEqualizer`, `PolygonNodePresentation` | Existing polygon normalization exactness is for the structure sheaf. Tensoring with the actual divisor line, comparing pullbacks and describing its global sections are separate missing proofs. D01–D03 below prove only the polynomial algebra. |
| Construct a projective morphism from sections | Standard nonvanishing-open ratio construction | `ProjectiveSpaceCharts`, `ProjectiveChartPolynomialEquiv`, `ProjectiveTwistingSheaf`; Mathlib `ProjectiveSpectrum/Functor.lean` | The graded `Proj.map` construction is not a ready map from an arbitrary polygon with generating sections. Construct and glue chart maps and the actual hyperplane pullback isomorphism. |
| Prove closed immersion | Surjective coordinate-ring maps on a covering of the image, then properness | `PolygonNodePresentation.a_adjoin`, `b_adjoin`, `aPresent_surjective` in `NodeQuotient.lean`, `bPresent_surjective` in `OneGonQuotient.lean`; `RelativeVeryAmpleLineBundle.targetOpenCoefficientMap_isClosedImmersion` | Known affine node generators must be expressed as section ratios on precisely identified projective inverse-image opens. Tangent separation alone does not prove this. |

## Ready leaves: complete checked proof designs

These are polynomial modules, not replacement definitions of sections or
ampleness. `Bounded R d` abbreviates Mathlib's `degreeLT R (d+2)`;
`matching` is the kernel of an explicit linear map between these modules.
It is not asserted to be H0 of any sheaf.

| Leaf / module | Cap | Design and dependencies | Checked output |
|---|---:|---|---|
| D01 `PolynomialEndpointInterpolation` | 240 | Read coefficient 0 and coefficient d+1; right inverse `(a,b) ↦ C a + monomial (d+1) b`. Use Mathlib's monomial degree bound and coefficient equivalence. | Endpoint restriction is split surjective for every commutative ring; finite dimension d+2 over every field. |
| D02 `PolygonPolynomialMatching` | 240 | For component i of degree d(i)+1, take discrepancy `top(i) - weight(i)*constant(neighbor(i))`. Right inverse has zero constants and specified tops. Lift node values with D01; subtract the right inverse to correct any family. Apply rank-nullity and `degreeLTEquiv`. | Discrepancy surjective, node values surjective on its kernel, explicit correction, kernel dimension `sum_i (d(i)+1)`. Arbitrary neighbor function and weights; no division by the component count. |
| D03 `PolygonCubicInterpolation` | 240 | Cubics have four independent coefficients. Impose the D02 relation only on coefficient 3. The two interior coefficients remain free. For a nonzero a, coefficients `(2*r-a*s)/a` and `(a*s-r)/a^2` give polynomial `b*X+c*X^2` with value r and derivative s at a. | Arbitrary node constants and both branch-linear coefficients; arbitrary torus first jet supported on one component with zero endpoint values. Works in every field, including characteristics 2 and 3. |

Validation prototype: `LEAN_NUM_THREADS=2 lake env lean W27_CUBIC_PROOF.lean`
contains D01–D03 in dependency order. Each promoted module must independently
pass foreground build and module-only lint, then the declaration axiom audit.

## Orientation, weights and exceptional polygons

`PolygonPinchingDiagram.endpoint` identifies **zero on component i** with
**infinity on component next(i)**. In D02, high coefficient on component j
is matched to the constant on `neighbor(j)`, so for this presentation use
`neighbor = predecessor`, not the pinching diagram's successor. This orientation
must be proved in the coefficient comparison; it is not silently inferred.

For the actual mark a in the torus, a rational section represented by
`p(t)/(t-a)^m` has endpoint values `p(0)/(-a)^m` and its coefficient of t^m.
Thus equal raw endpoint coefficients are generally the **wrong** gluing rule.
D02 leaves arbitrary weights available; D04b must compute the actual units,
power, and indexing. No identification of these rational formulas with the
constructed ideal-dual sheaf has been claimed.

For n=1, `neighbor=id`; the top coefficient is constrained by the same
polynomial's constant coefficient, and the two cubic interior coefficients
remain independent. For n=2, each component has two distinct endpoint branches;
the two nodes must not be collapsed into one edge. D02 retains one discrepancy
per node. All algebra is valid for `Fin 1`, `Fin 2`, and arbitrary positive n,
and the jet formulas divide only by a nonzero torus coordinate.

## Direct route: remaining bounded contracts

Each row is one proposed module of at most 240 lines. Status is **unproved**;
API checks found the named inputs, not a complete elaborated proof. D04–D10
are substantial geometry, and their estimated boundaries must be refined when
actual proofs are attempted. They are not made ready merely by the short D01–D03
proofs. Follow dependency order; do not assume any row as a record field.

| Leaf / proposed module | Cap | Required proof and available input |
|---|---:|---|
| D04a `PolygonDivisorNormalizationPullback` | 240 | Pull back the actual product of section ideals to each normalization P1; show exactly the chosen marked-point factor survives. Start with `PolygonMarkedSections` and actual ideal pullback, not only set-theoretic support. |
| D04b `PolygonDivisorEndpointCoordinates` | 240 | Trivialize the actual dual ideal on both P1 charts; compute degree-one transition and endpoint units. Use D04a, `DivisorCanonicalSection`, `DivisorLineBundleRestrict`. |
| D04c `PolygonDivisorPowerCoordinates` | 240 | Transport those coordinates through `divisorLineBundlePowerIso` and compute the weighted relation and predecessor orientation. Includes signs in odd degree. |
| D05a `ProjectiveLineTwistPolynomialSections` | 240 | Identify genuine H0 of O(m) with `degreeLT K (m+1)` by gluing two affine-chart polynomials with Laurent transition; prove coefficient-zero and coefficient-m evaluation formulas. Existing `ProjectiveLineConstantSections` only handles the structure sheaf. |
| D05b `PolygonLineNormalizationExact` | 240 | Tensor the existing normalization short exact sequence with the actual locally free line. Establish exactness and projection/pullback comparisons, without treating a scheme pushout as automatic module descent. |
| D05c `PolygonDivisorGlobalSections` | 240 | Identify H0 of O(mD) with the D02 kernel, using D04c/D05a/D05b and the actual global-section maps. |
| D06a `PolygonCubicGeneratingSections` | 240 | Transport D03 into genuine global sections; show generation at all scheme points after residue-field extension, including endpoints and non-rational points. Rational K-point interpolation alone is insufficient. |
| D06b `PolygonSectionRatioCharts` | 240 | Construct affine target chart maps on nonvanishing opens using section ratios, with inverse-image opens proved equal to the required opens. |
| D06c `PolygonSectionProjectiveMap` | 240 | Prove overlap identities and glue D06b to a projective morphism over K. |
| D07a `PolygonSectionHyperplanePullback` | 240 | Glue chart trivializations to an isomorphism between O(3D) and the actual pullback of O(1), checking transition maps. |
| D08a `PolygonTorusImmersionCharts` | 240 | Recover torus coordinates as ratios of adjacent interior monomials; prove coordinate-ring surjectivity/local immersion on the corresponding opens. |
| D08b `PolygonSplitNodeImmersionCharts` | 240 | Express both split-node branch generators as ratios; compare with `aPresent_surjective`. Prove the chart covers the relevant node. Retain both nodes when n=2. |
| D08c `PolygonOneGonImmersionCharts` | 240 | Separate self-incidence case: compare ratios with the actual B-ring generators u,v, using `bPresent_surjective` and `OneGonAffineNormalizationCoordinates`. An n>=3 argument cannot be reused without this proof. |
| D09 `PolygonCubicClosedImmersion` | 240 | Assemble D08 chart immersions; use the already proved properness to obtain a closed immersion. |
| D10 `PolygonDivisorPowerVeryAmple` | 240 | Feed D07/D09 into existing `relativeVeryAmple_divisorPower_of_embedding` with positive exponent 3. No new predicate. |

## General route: remaining bounded contracts

These are an alternative program, not prerequisites for completing the direct
route. All are unproved with 240-line caps, not a claim that the general theory
fits into these initial module boundaries.

| Leaf / proposed module | Cap | Source-matched proof obligation |
|---|---:|---|
| G01 `CurveCoherentEulerCharacteristic` | 240 | Define integer Euler characteristic from actual finite cohomology; prove the dimension-one truncation used in 0AYQ. |
| G02 `CurveEulerCharacteristicExact` | 240 | Derive additivity from the actual long exact sequence and finite dimensions. |
| G03 `CurveInvertibleSheafDegree` | 240 | Define degree using G01; establish invariance under actual sheaf isomorphisms. |
| G04 `CurveTensorDegree` | 240 | Prove 0AYX's tensor formula, then degree of positive powers. Missing devissage may require further splits. |
| G05 `CurveEffectiveDivisorDegree` | 240 | Identify degree with the length of a nonzero effective zero divisor using the ideal-dual exact sequence; deduce 0B40 positivity. |
| G06 `CurvePositiveDegreeSections` | 240 | Derive the growing H0 bound and a nonzero section vanishing at a prescribed finite set as in 0B5X. |
| G07 `CurveSectionPowerAnnihilation` | 240 | Prove 01XR for an affine nonvanishing locus and genuine coefficient tensor powers. |
| G08 `CurveIdealTwistVanishing` | 240 | Use finite-dimensional H1, surjectivity through finite-support cokernels, and G07 to prove the vanishing step of 0B5X. |
| G09 `CurveVanishingProjectivePresentation` | 240 | Prove the required direction of 0B5U and obtain a positive-power presentation in the **existing** `RelativeVeryAmple` sense. A new ampleness definition cannot bypass this. |
| G10 `CurveFiniteSurjectivePresentationDescent` | 240 | Establish the descent used by 0B5V, with the existing positive-power presentation target; the proof in the source uses cohomological tools beyond finite morphism instances. |
| G11 `CurveComponentPositivePresentation` | 240 | Construct the finite-surjective component cover, including isolated points, then combine G05–G10 exactly as in 0B5Y. |
| G12 `PolygonComponentDivisorDegree` | 240 | Identify the actual divisor line on each reduced irreducible component and show positive degree; use G11 and W26 to conclude. |

The first unsolved direct dependency is D04a; the general route starts with
G01 and needs substantially more theory. Beyond either ampleness producer,
actual generalized-curve/moduli objects, arbitrary-base descent, coarse moduli,
cusps and Mazur's arithmetic argument remain. This split does not remove
`Mazur_statement` from the final Fermat theorem.

## Accepted W27 scope

Checked 2026-10-03 with `python3 W27_CHECK_SOURCE.py` and the saved foreground
Lean logs. D01–D03 are proved: **277 Lean lines** (66, 103, 108), each below
its 240-line cap. Only these new Lean modules and sorted `FLT.lean` imports
were changed. No replacement ampleness definition or new structure was added.

Each module passed `LEAN_NUM_THREADS=2 lake build FLT.Mazur.MODULE` and its
own `LEAN_NUM_THREADS=2 lake exe runLinter FLT.Mazur.MODULE`, sequentially.
`GOAL_MAZUR_W27_AXIOM_AUDIT.lean` checks all originating declarations, including
generated declarations: 20 + 23 + 22 = **65**, using only `propext`,
`Classical.choice`, and `Quot.sound`.
`W27_CONSUMER_CONTRACT.lean` checks dimensions for one-gons, two-gons and arbitrary
n, the actual pinching predecessor orientation, characteristics 2 and 3,
and the unchanged W26 target for the genuine all-one polygon divisor.

These results establish the polynomial input to the direct route, not global
sections of O(3D), global generation of that sheaf, or an immersion. D04a–D10
and G01–G12 remain unproved. No final-theorem axiom audit was rebuilt;
`GOAL_MAZUR_W27_REMAINING_SOURCE_CHECK.txt` records the existing Mazur assumption
and consumer by source inspection. The untracked handoff lists local commits
and repeatable validation commands.
