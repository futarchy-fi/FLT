# Mazur track D: extension and local arithmetic

Audit checked 2026-10-04 against FLT `55366a69` and pinned Mathlib
`c32e1ec0d1eb5237ba344eee50162f45d5b0fc76`. This is the implementation order
for GOAL-MAZUR-D-W1. Every new module has a hard cap of 240 physical lines.
W74 in wt-r5a owns ampleness/moduli; no leaf below duplicates that work.

## Existing APIs and limits

- Mathlib `AlgebraicGeometry/ValuativeCriterion.lean` proves properness implies
  existence and separatedness implies uniqueness for valuation-ring squares.
  A DVR is a valuation ring, so G1-D1 needs an over-category adapter, not a
  new valuative criterion.
- `AlgebraicGeometry/Birational/RationalMap.lean` supplies
  `PartialMap.ofFromSpecStalk`, its restriction identity, and spreading out.
  `Morphisms/Separated.lean`, `ext_of_isDominant_of_isSeparated`, supplies
  uniqueness on a reduced base. `Scheme.OpenCover.glueMorphisms` is the
  actual gluing API. Local lifts must first be spread to open neighborhoods;
  spectra of local rings are not an open cover.
- `FLT/Mazur/OverPoints.lean` and `Contracts.lean` supply actual morphisms over
  the base. `IntegralBase.lean` supplies canonical maps of Z[1/(2p)]. The
  supplied `IntegralData.generic` must be identified with the canonical map.
- Mathlib elliptic `Reduction.lean` defines minimal, good, multiplicative and
  additive reduction. It does not construct Néron models or their components.
- `FLT/FreyCurve/Serre/GoodReduction.lean` proves prime-to-residue-characteristic
  torsion injectivity. `GoodReductionSpecialization.lean` constructs a
  surjective geometric specialization. Neither proves G2-D5: rational torsion
  of residue-characteristic order at odd unramified primes must be included.
- `FLT/GroupScheme/Raynaud*Rigidity.lean` provides finite-flat algebra tools;
  applicability to torsion in a constructed abelian scheme still needs proof.
  No general Néron special-fiber/component or elliptic formal-group endpoint
  was found by `rg` in FLT and Mathlib. Frey-specific semistability is not A1.

## Ordered leaves

Names in this table are planned modules under `FLT/Mazur/`; a name is not a
claim that its prerequisites or proof already exist. Split again before a
proof exceeds its cap. Sources: MAZUR_CONTRACTS G1-D/G2-D and
MAZUR_GOAL_LEDGER source table; [M] is Mazur (1977).

| Item | Proposed module | Cap | Exact output / prerequisites |
| --- | --- | ---: | --- |
| G1-D1 | ProperPointExtension | 160 | Unique extension of an actual K-point over any valuation ring R with fraction field K; hence every DVR. Proper structure map only. |
| G1-D2a | GenericSectionUniqueness | 160 | Restriction injectivity from a reduced base along a dominant map to a separated target; apply to canonical generic points. |
| G1-D2b | ProperStalkExtension | 240 | Spread the valuative lift at a point of an integral base with valuation stalk to an open neighborhood; preserve the generic point and base equation. |
| G1-D2c | ProperSectionGluing | 240 | Glue those neighborhoods by generic uniqueness; unique global section. |
| G1-D2d.i | DedekindPointExtension | 160 | Prove valuation stalks for Dedekind spectra; transport the extension to any specified fraction field. |
| G1-D2d.ii | IntegralPointExtension | 160 | Prove valuation-stalk/fraction-field hypotheses for Z[1/(2p)], identify the canonical generic map, conclude G1Extension. |
| A1-F1 | EllipticReductionKernel | 240 | Construct local minimal-model reduction and its kernel from actual rational points; requires the local model and group-law comparison. |
| A1-F2 | EllipticFormalParameter | 240 | Construct the formal parameter and multiplication series for that kernel, with integral coefficients. Depends F1. |
| A1-F3 | EllipticFormalTorsionBound | 240 | Prove valuation bounds for multiplication, including the small-prime exceptions. Depends F2; [M] III §5 Step 1. |
| A1-C1 | EllipticNeronComponents | 240 | Identify reduction modulo the identity component and prove the additive component order bounds. Requires a constructed Néron model and local fiber classification. |
| A1-S1 | PrimeTorsionSemistabilityAway | 240 | Exclude additive reduction away from the torsion prime for a rational point of prime order ≥17 using F3/C1. |
| A1-S2 | PrimeTorsionSemistabilityAtPrime | 240 | Exclude additive reduction at the torsion prime via finite-flat rigidity; requires the actual torsion closure and its rank/flatness. |
| A1-C2 | PrimeTorsionComponentsAtTwo | 200 | Small-prime component assertion at 2; retain split/nonsplit and formal-kernel hypotheses from [M] III §5 Steps 1–2. |
| A1-C3 | PrimeTorsionComponentsAtThree | 200 | Corresponding component assertion at 3; depends F3/C1/S1. |
| A1-Cp | PrimeTorsionComponentsAtPrime | 240 | Component assertion at p; depends S2 and finite-flat local model. |
| G2-D5a | AbelianTorsionClosure | 240 | Construct finite-flat closure of rational torsion in the good abelian model, with generic point and specialization comparison. |
| G2-D5b | OddPrimeTorsionRigidity | 240 | Prove trivial specialization kernel, including q-primary torsion, over the unramified odd local base. Depends D5a and proven rigidity, not a kernel assumption. |
| G2-D5c | OddPrimeTorsionSpecialization | 160 | Injectivity on actual rational torsion from D5a/b. [M] III §5 p.160 footnote. |
| G2-D6 | FiniteSectionSpecialization | 180 | Combine finite rational points, generic restriction injectivity and D5c to get G2Specialization. |

The arithmetic rows are source-level subdivisions with named foundation
prerequisites, not assertions that Néron theory fits in one 240-line module.
Implementation proceeds in order; a missing foundation is reported with the
exact missing theorem, never installed as a conclusion-bearing record field.
G1-D3–D6 (Néron reduction and cusp orientation) remain separate prerequisites
of the final cusp argument. Nothing here alone removes `Mazur_statement`.

## Validation

Each implemented module: foreground `LEAN_NUM_THREADS=2 lake build MODULE`,
then `lake exe runLinter MODULE` alone, then `#print axioms` for every new
theorem (allowed: propext, Classical.choice, Quot.sound only). Before handoff:
merge origin/main, build `FLT` once, check caps and declaration clashes.

## Implementation boundary (2026-10-04)

G1-D1 and G1-D2 are implemented by the six modules above.
`g1Extension_of_isProper` proves the actual contract for `p ≠ 0` and proper
`D.X.hom`. No canonical-map hypothesis is assumed: `IntegralBase.generic_unique`
proves every map from Spec Q to this base equals the canonical map. The modular
curve itself and its properness remain G1-C work.

The next leaf A1-F1 is not supplied by existing reduction APIs:
`WeierstrassCurve.reducePoint` in `EllipticCurve/PointReduction.lean:30` requires
`(W.map (residue A)).IsElliptic`; `reducePointHom` additionally uses an
algebraically closed generic field. Additive and multiplicative special fibers
are singular, and arbitrary rational points can meet singular points on a
minimal Weierstrass model. A1 needs the actual nonsingular-reduction subgroup
E₀(K), its reduction homomorphism and formal kernel E₁(K), then their comparison
with the Néron model. Sending all singular reductions to zero is not that map.
`Reduction.exists_isMinimal` constructs a minimal equation but does not prove
these subgroup, component, or formal multiplication assertions.

A concrete prerequisite subdivision for A1-F1 is: (i) define E₀(K) through
projective reduction and prove closure under addition/negation (cap 240),
(ii) construct its homomorphism to the smooth special cubic and characterize
E₁(K) by the formal parameter (cap 240), (iii) construct/compare the Néron
identity fiber and its component quotient (each further leaf cap 240). None
is marked implemented. Formal multiplication coefficients and local valuation
bounds must then be proved before any semistability/component corollary.

For G2-D5, `ThreeAdicPlan.ModelHom.surjective_of_padic_power` is an existing
odd-prime rigidity theorem for supplied finite-flat Hopf models. Its inputs
are actual `FF` models and a generically bijective `ModelHom`; it does not
construct the torsion closure in the abelian scheme or identify specialization.
The missing comparison cannot be replaced by assuming an injective reduction
map. A1, G2-D5 and `Mazur_statement` therefore remain open.

## Checked validation (2026-10-04 22:41 UTC)

Six module builds and six individual module linters passed. All 15 new theorems
and G1Extension were checked with `#print axioms`: only propext, Classical.choice
and Quot.sound. Each new module is 51–92 lines. After merging origin/main
`0d2a816c` in `a3ef538d`, `LEAN_NUM_THREADS=2 lake build FLT` passed all 12,505
jobs, including the root and FermatsLastTheorem. Root imports are sorted and
`git diff --check` passed. The guarded final theorem audit still includes
Mazur_statement and sorryAx; the arithmetic leaves above are not closed.

## D-W2: projective reduction foundation leaves

A1-F1 is larger than one 240-line module. Work first constructs actual projective
reduction, including singular reductions; it does not replace singular points by
infinity. The following leaves precede the subgroup and homomorphism assertions.

| Item | Module under `FLT/Mazur/` | Cap | Output |
| --- | --- | ---: | --- |
| A1-F1a.i | ValuationProjectiveNormalization | 240 | Every nonzero finite coordinate vector has an integral representative with a unit coordinate; primitive representatives equivalent over the fraction field differ by an integral unit. |
| A1-F1a.ii | EllipticProjectiveReduction | 240 | Choice-independent projective reduction on actual generic-fiber points, satisfying the reduced equation even at bad reduction. |
| A1-F1a.iii | EllipticSmoothReduction | 240 | Nonsingular-reduction locus, infinity fiber, and compatibility with negation; no claim of additive closure until proved. |
| A1-F1a.iv | EllipticReductionInfinityChart | 240 | Identify the infinity fiber by vanishing of the reduced Z coordinate; establish its integral formal-parameter chart. |
| A1-F1b.i | EllipticSmoothReductionAddition | 240 | Prove nonsingular-reduction locus closed under addition using integral group-law charts, including opposite reductions. |
| A1-F1b.ii | EllipticReductionKernel | 240 | Package the proved locus as E₀, its reduction homomorphism, and E₁ as the kernel; compare with formal coordinates. |

Formal multiplication, Néron components and the subsequent arithmetic leaves stay
in the order above. A set closed under negation alone does not close A1-F1.

### D-W2 implementation boundary

The four A1-F1a leaves above are implemented. `projectiveReduction` accepts actual
generic-fiber projective points of any integral Weierstrass equation over a
valuation subring, with no good-reduction or algebraic-closure assumption. Its
primitive reduced coordinates are nonzero and satisfy the special cubic. Singular
reductions remain singular projective classes. `SmoothReduction` and
`InfinityReduction` are predicates on these actual points, stable under negation;
`smoothReductionPoint` maps the former locus to actual smooth special-fiber points.
They have **not** been promoted to subgroups.

`infinityReduction_affine_iff` identifies the infinity fiber with the failure of
joint integrality of the affine coordinates. `exists_infinity_parameters` constructs
the actual integral coordinates t = -X/Y and s = -Z/Y in the maximal ideal and
proves s = t³ + a₁ts + a₂t²s + a₃s² + a₄ts² + a₆s³. It does not construct a power
series expressing s in terms of t or a formal multiplication law.

The first remaining statements are:

- `SmoothReduction A W P → SmoothReduction A W Q → SmoothReduction A W (P + Q)`.
- The reduction of that sum equals the sum of `smoothReductionPoint` values.

The generic projective addition formulas do not directly prove these statements:
Mathlib `Projective/Formula.lean`, `addXYZ_self`, gives the zero vector on coincident
inputs. Distinct generic points can have coincident reductions, so reducing their
secant formula can give zero rather than a primitive vector. `Projective.map_add`
only transports through field homomorphisms and does not apply to the residue map.
Integral group-law charts or explicit exceptional-denominator arguments still
need construction. Existing `PointReductionAddition`/`PointReductionKernel` APIs
package addition using an elliptic special fiber, so they cannot directly supply
these bad-reduction statements.

After those statements: package E₀ and the reduction homomorphism, define E₁ as
its kernel, then implement A1-F2/F3. A1-C1 (Néron model/components and bounds),
A1-S1/S2, A1-C2/C3/Cp, and G2-D5/D6 remain unimplemented here. No later arithmetic
leaf is closed by the projective-coordinate foundation.

Validation of these leaves: four foreground module builds and four individual
module linters pass; all 28 new theorems have only propext, Classical.choice and
Quot.sound in their axiom sets. Modules have 108, 135, 134 and 135 physical lines,
respectively, against the 240-line caps. Re-run the axiom checks with
`lake env lean Scratch/MazurDW2/Axioms.lean` (untracked validation artifact).
