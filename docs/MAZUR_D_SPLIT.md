# Mazur track D: extension and local arithmetic

## D-W4: formal addition construction leaves

Subdivision recorded before implementation; each new module has cap 240 lines.

| Item | Planned module | Output |
| --- | --- | --- |
| A1-F2b.i | EllipticFormalCoordinates | Substitution of the integral infinity series into multivariate parameters, with the chart equation and uniqueness. |
| A1-F2b.ii | EllipticFormalSecant | Integral secant slope and intercept, both line incidences, and zero constant coefficients. |
| A1-F2b.iii.1 | EllipticFormalCubic | Cubic coefficients and a third-root identity valid without cancellation. |
| A1-F2b.iii.2 | EllipticFormalIntersection | Integral third-intersection coordinates and their chart equation. |
| A1-F2b.iv.1 | EllipticFormalNegation | Integral normalized negation, its chart equation and involution. |
| A1-F2b.iv.2 | EllipticFormalSymmetry | Symmetry of the slope, intercept and third intersection. |
| A1-F2b.iv.3 | EllipticFormalAddition | Negation of the third intersection, identity and symmetry. |
| A1-F2b.iv.4 | EllipticFormalSubstitution | Substitution compatibility and representation by the two-variable series. |
| A1-F2b.iv.5 | EllipticFormalLinearTerms | Axis identities, symmetry and the two linear coefficients of the series. |
| A1-F2b.v | EllipticFormalGroupLaw | Associativity and the actual FormalGroup construction, with linear coefficients. |

F2c/F2d/F3 and later arithmetic leaves retain their previous order. The first
four construction leaves alone do not establish a formal group or its comparison
with actual point addition.

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

### D-W2 root verification (2026-10-04 22:59 UTC)

After commit `ba010248`, fetched origin/main (`baff6e10`) and ran
`git merge origin/main`: already up to date. The required foreground
`LEAN_NUM_THREADS=2 lake build FLT` passed all 12,519 jobs, including FLT and
FermatsLastTheorem, with no declaration clashes. Evidence:
`Scratch/MazurDW2/root-build.log`. The guarded global axiom audit still contains
Mazur_statement and sorryAx; these foundation leaves do not remove either.

## D-W3: additive closure subdivision

Before implementation, split A1-F1b.i into the following leaves (each cap 240
physical lines). These proofs retain bad reduction and arbitrary valuation
subrings; smoothness of individual reduced points is not good reduction.

| Item | Module under `FLT/Mazur/` | Cap | Output |
| --- | --- | ---: | --- |
| A1-F1b.i.1 | EllipticReductionRelation | 240 | Relate actual affine points via projective reduction; zero, integral, negation and uniqueness APIs. |
| A1-F1b.i.2 | EllipticReductionTranslation | 240 | Adding a nonintegral point to any integral affine point gives integral coordinates with the same residues; no elliptic special-fiber assumption. |
| A1-F1b.i.3 | EllipticReductionAffineAddition | 240 | Compatible addition when integral smooth reductions are not opposite, using the two slope charts. |
| A1-F1b.i.4 | EllipticReductionOpposite | 240 | Opposite smooth affine reductions sum to infinity; use integrality of the slope when the sum is integral to exclude that case. |
| A1-F1b.i.5 | EllipticSmoothReductionAddition | 240 | Full compatibility and smooth-locus closure, including the sum of two infinity-fiber points. |
| A1-F1b.ii | EllipticReductionKernel | 240 | E₀ subgroup, actual reduction homomorphism and E₁ kernel. |

The two-infinity case can be reduced to translation: if their sum were integral,
translation by its negative would contradict the known infinity reduction of the
other point. Later arithmetic leaves still follow the original order.

### D-W3 formal-series subdivision

A1-F2 also requires multiple capped leaves. After constructing E₀/E₁:

| Item | Module under `FLT/Mazur/` | Cap | Output |
| --- | --- | ---: | --- |
| A1-F2a | EllipticInfinityPowerSeries | 240 | Construct the integral solution s(T) of the infinity-chart equation, with s(T) = T³ times a unit of constant term one. |
| A1-F2b | EllipticFormalGroupLaw | 240 | Construct the two-variable integral addition law and prove its identities from the actual Weierstrass law; split again before exceeding the cap. |
| A1-F2c | EllipticFormalMultiplication | 240 | Multiplication series [n](T) with its linear coefficient and higher-order divisibility properties. |
| A1-F2d | EllipticFormalEvaluation | 240 | Identify convergent evaluation on the complete local base with actual E₁ addition and multiplication. |

F2a alone is not a multiplication law or the evaluation comparison. F3 requires
F2c/d, including the residue-characteristic-primary multiplication estimates.

F2a is further split before implementing the actual-parameter comparison:
`EllipticInfinityPowerSeries` (F2a.i, cap 240) constructs the universal integral
series; `EllipticInfinityParameter` (F2a.ii, cap 240) proves uniqueness of the
maximal-ideal chart and constructs an injective parameter on actual E₁ points.
Neither leaf substitutes for F2b's addition law or F2d's convergence proof.

### D-W3 implementation boundary (2026-10-04)

A1-F1b.i.1–5 and A1-F1b.ii are implemented. `SmoothReduction.add` proves closure
on actual projective points; `smoothReductionPoint_add` proves additivity.
`ellipticE0` and `ellipticE1` are actual subgroups, and `smoothReductionHom_ker`
identifies the reduction kernel with E₁ pulled back to E₀. The special cubic is
allowed to be singular, the valuation subring is arbitrary, and no algebraic
closure, lifting-surjectivity or closure assumption is added.

The exceptional cases are proved: `slope_mem_of_addX_mem` forces integral slope
from integral sum; `not_opposite_of_integral_slope` contradicts smoothness for
opposite reductions, including reduced order-two points. Translation by a point
reducing to infinity preserves arbitrary integral affine coordinates modulo the
maximal ideal. If a sum of two infinity-fiber points were integral, translation
by its negative would give the contradiction used in `reducesTo_add_zero`.

F2a.i and F2a.ii are implemented. `infinitySeries` is constructed over **any**
commutative coefficient ring, not postulated: a monic reciprocal cubic is Hensel
lifted in the T-adically complete power-series ring. The series satisfies the
infinity equation, has zero constant coefficient and cubic coefficient one,
is the unique zero-constant solution, and commutes with coefficient-ring maps.
`infinityParameter` is an injective function from actual E₁ points to the
valuation subring, with image in the maximal ideal, and vanishes exactly at zero.
`infinityChart_eq_cube_mul_unit` proves the actual relation s = t³ times a unit
of residue one. These are coordinate statements, not formal multiplication.

The next unimplemented statement is F2b: construct an integral two-variable
power series F_W(X,Y) for this Weierstrass curve and prove its formal-group
identities. In the t,s chart, a candidate uses the divided difference
λ = (s(X)-s(Y))/(X-Y), ν = s(X)-λX, and the third intersection of the line
s = λt+ν with the cubic, followed by Weierstrass negation. The divided difference,
unit denominators, group identities and comparison with actual addition still
need proofs; one-variable uniqueness by itself does not supply them. Subdivide
F2b further before a proof exceeds 240 lines.

After F2b: multiplication series F2c, convergent comparison F2d, valuation bounds
F3, the actual Néron model/component classification C1, semistability S1/S2,
components C2/C3/Cp, and abelian torsion closure/odd-prime specialization D5/D6.
No claim is made to finish those leaves or to remove `Mazur_statement`.

### D-W3 validation (2026-10-04 23:28 UTC)

All eight modules built in the foreground and passed separate one-module linters.
All 47 new theorems have only propext, Classical.choice and Quot.sound in their
axiom sets. Modules have 87–151 physical lines against caps of 240. The
implementation commits are `7be7c9f2` and `c0b96992`; no push was made.

Fetched origin/main at `988a75e5` and merged it in `280af779`. The required
foreground `LEAN_NUM_THREADS=2 lake build FLT` passed all 12,545 jobs, including
FLT and FermatsLastTheorem, with no declaration clashes. Root imports are sorted
and unique; `git diff --check` passes. Recheck evidence in
`Scratch/MazurDW3/root-build.log`, `*lint.log`, and `axioms.log`; re-run the 47
axiom checks with `lake env lean Scratch/MazurDW3/Axioms.lean`. The guarded global
theorem check still includes Mazur_statement and sorryAx. F2b onward remains open.

### D-W4 construction boundary and validation (2026-10-04 23:54 UTC)

The nine construction leaves A1-F2b.i through A1-F2b.iv.5 are implemented in
`f0aea5d4` and `ac1e7330`. They construct an integral two-variable addition
candidate over every commutative ring. Its constant coefficient is zero, both
linear coefficients are one, its axis restrictions are the identity, and it is
symmetric. The secant and third-intersection equations hold even on the diagonal;
only denominators with constant coefficient one are inverted. Formal negation
is an involution. The entire construction commutes with zero-constant formal
substitution.

A1-F2b.v remains open: the series has not been proved associative or packaged
as a `FormalGroup`. There is no comparison with actual E₁ addition or convergent
evaluation. F2c/F2d/F3 and every later arithmetic leaf remain open.

Read-only checks: all nine foreground module builds and nine separate module
linters passed (`Scratch/MazurDW4/*-lint.log`). All 59 new theorem axiom sets
contain only propext, Classical.choice and Quot.sound (`lake env lean
Scratch/MazurDW4/Axioms.lean`, captured in `axioms.log`). The modules have
65–127 physical lines against their 240-line caps. Root imports are sorted and
unique; `git diff --check` passes. No existing Lean module was edited except
the root imports.

Fetched origin/main at `3509f324` over authenticated HTTPS (SSH authentication
failed); `git merge origin/main` reported already up to date. The required
foreground `LEAN_NUM_THREADS=2 lake build FLT` passed all 12,563 jobs, including
FLT and FermatsLastTheorem, with no declaration clashes (`root-build.log`).
The final theorem audit still lists Mazur_statement and sorryAx, checked by
`lake env lean Scratch/MazurDW4/GlobalAxioms.lean` (`global-axioms.log`).
