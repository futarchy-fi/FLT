# W52: Cartier comparison, descent, and ampleness

Source match checked 2026-10-04 by fetching the cited Stacks tags and the
upstream `divisors.tex`, `descent.tex`, `more-morphisms.tex`, and tag database.
This is a proof-obligation split, not a list of completed theorems. Every new
Lean module has a hard cap of 240 lines including headers. Large theory rows
below must be subdivided further after their foundational APIs exist.

## Source contracts

- [01WS](https://stacks.math.columbia.edu/tag/01WS): the actual ideal sheaf is
  invertible exactly when it has regular principal equations locally. The
  reverse implication requires quasi-coherence and passage from stalks to
  affine neighborhoods; a stalk generator alone is not a Cartier chart.
- [056Q](https://stacks.math.columbia.edu/tag/056Q): if a regular equation has
  quotient flat over the base, arbitrary tensoring preserves its injectivity.
  This proves that the canonical pulled-back ideal map is invertible locally;
  the map must be identified, not replaced by an unrelated rank-one isomorphism.
- [05B2](https://stacks.math.columbia.edu/tag/05B2): finite locally free
  quasi-coherent modules descend under fpqc covers. Apply to the actual ideal
  after identifying its flat pullback with the extended ideal; descend rank
  one and then use 01WS. The subgroup divisor is already flat by `ideal_degree`.
- [0B5Y](https://stacks.math.columbia.edu/tag/0B5Y): on a proper scheme over a
  field of dimension at most one, ampleness of an invertible sheaf is equivalent
  to positive degree on every one-dimensional irreducible component.
- [0D2S](https://stacks.math.columbia.edu/tag/0D2S) supplies the missing
  **arbitrary-base** fiber-to-neighborhood theorem: for a proper morphism and
  invertible sheaf, ampleness on one fiber implies relative ampleness near that
  point. Its proof uses approximation by proper schemes over finite-type
  Z-algebras, descent of invertible sheaves, and descent of fiber ampleness.
  The Noetherian-only 0D2N is insufficient by itself; 0D2S resolves the source
  question but does not supply these absent Lean limit/cohomology APIs.
- [0D2P](https://stacks.math.columbia.edu/tag/0D2P): relative ampleness of an
  invertible sheaf is fpqc local on the base. First compare the library's
  positive-projective-power predicate with the source's relative ampleness.

## Capped dispatch

| Leaf | Proposed module | Contract and dependencies | Cap / readiness |
| --- | --- | --- | --- |
| C1 | IdealModulePrincipalPullback | Identify canonical ideal map on affine regular principal charts via section generators | 240 / ready |
| C2 | RelativeCartierIdealPullback | Detect its invertibility on two affine covers for arbitrary relative Cartier base change; C1, 056Q | 240 / ready after C1 |
| C3 | RelativeCartierDivisorPullback | Construct actual divisor-line pullback iso and canonical section identity; C2 | 240 / ready after C2 |
| D1 | LocalCartierGeneratorDescent | Descend a regular principal ideal along a flat local ring map, using finite generation descent | 240 / algebra ready |
| D2 | CartierIdealStalkDescent | Identify ideal stalk extension under flat maps and descend regular principal stalk generators; D1 | 240 / missing sheaf/stalk comparison |
| D3 | CartierIdealNeighborhood | Spread finite presentation and regular generators to affine neighborhoods; D2 | 240 / missing finite-presentation/local-freeness bridge |
| D4 | GeneralizedCurveCartierDescent | Use fppf generator cover, D2–D3, and unconditional flatness from ideal_degree | 240 / blocked by D2–D3 |
| P1 | DivisorProjectivePowerPullback | Tensor-power coherence and pullback of actual closed projective presentations; C3 | 240 / needs projective base-change presentation |
| P2 | GeneralizedCurveAmpleBaseChange | Positive-power presentations on every affine new-base open; P1 | 240 / needs relative ampleness comparison/locality |
| F1 | CurveDivisorDegreeSupport | Degree of effective divisor restriction equals length and detects nonempty support | 240 / large missing degree theory |
| F2 | CurveComponentAmpleCriterion | Formalize 0B5Y and compare with projective powers; F1 | 240 / large missing cohomology/ampleness theory |
| F3 | GeneralizedCurveFiberAmple | Smooth irreducible fiber and polygon component-support criterion; F2 | 240 / blocked by F1–F2 |
| L1 | RelativeAmpleApproximation | Descend proper family and invertible sheaf to finite-type Z-model; 0D2S | 240 / large missing limit theory |
| L2 | RelativeAmpleFiberNeighborhood | Descend ample fiber, use 0D2N, pull back neighborhood; L1 | 240 / large missing cohomology/limit theory |
| L3 | GeneralizedCurveAmpleDescent | Compare projective-power predicate, use fpqc source or F3/L2; D4, P2 | 240 / blocked |
| A7a | AmpleCyclicLevelIso | Actual compatible level isomorphisms and equivalence relation; D4 | 240 / after A6 |
| A7b | AmpleCyclicLevelPresheaf | Quotient pullbacks and full-category coherence; A7a, P2, L3 | 240 / blocked by ampleness transport |
| A8a | RationalPointFiniteSubgroup | Exact-order rational point gives finite étale closed subgroup | 240 / needs point-to-group-scheme embedding |
| A8b | RationalPointAmpleLevel | Cartier generator and smooth-fiber ampleness, hence moduli point; A8a, F3, A7b | 240 / blocked |
| A8c | RationalGeneratorInvariance | Equal subgroup/moduli point for prime-to-order change of generator; A8b | 240 / blocked |

The 240 entries for F1–L3 are interface caps, not claims that the missing theory
fits in one module. Release only concrete capped sublemmas, with exact types,
once their dependencies are available. No production record may carry any
of these conclusions merely to bypass the missing proof.

## Refinement of the remaining foundation rows

D2 is implemented in `CartierIdealStalkDescent`; D4's stalk conclusion is in
`GeneralizedCurveCartierStalks`. Their output is a regular generator at every
stalk, not an affine Cartier neighborhood. The remaining D3 work splits into:

| Leaf | Exact missing bridge | Cap |
| --- | --- | ---: |
| D3a | For a finitely presented module, a stalk basis extends to a basis on a principal neighborhood | 240 |
| D3b | Finite presentation of a module descends along a faithfully flat ring map | 240 |
| D3c | Affine sections of the ideal module after flat pullback identify with tensor extension | 240 |
| D3d | Reduce an fppf cover of an affine scheme to a finite affine faithfully flat family and apply D3b–c | 240 |
| D3e | Spread the descended rank-one ideal basis using D3a; injectivity of the ideal inclusion makes its image regular | 240 |
| D3f | Assemble Cartier charts and combine with subgroup flatness | 240 |

D3b is proved by `FaithfullyFlatFinitePresentation`. D3a has the existing
`IsLocalizedModule.exists_bijective_map_powers` ingredient in Mathlib, but the
bridge from the actual ideal stalk must still be assembled. D3c/d/e require
further implementation. Finite generation alone must not be silently
substituted for finite presentation in D3a.

F1–L2 are large theory projects, not ready one-module assignments. Their first
bounded interfaces are: restriction of a line bundle to the reduced component;
Euler-characteristic degree and its additivity in a divisor exact sequence;
identification with the finite divisor length; the integral-curve ample-degree
theorem; finite-surjective descent of ampleness; comparison with the project's
closed-projective-power predicate; descent of finitely presented schemes to
finite-type Z-models; descent of invertible sheaves; descent of closed
projective presentations; the Noetherian fiber-to-neighborhood theorem.
Each interface has the same 240-line cap, needs an exact Lean contract before
release, and may expose further prerequisite modules. None is counted as done.

## W52 implemented boundary

Recheck with one foreground `LEAN_NUM_THREADS=2 lake build MODULE` followed by
`lake exe runLinter MODULE`, separately for each module below. The originating
module declaration audit allows only `propext`, `Classical.choice`, `Quot.sound`.
The handoff records the checked-at timestamp, commits and exact log artifacts.

| Leaf | Implemented module | What the proof actually supplies |
| --- | --- | --- |
| C1 | IdealModulePrincipalPullback | Canonical comparison on principal charts whose equation stays regular |
| C2 | RelativeCartierIdealPullback | Canonical ideal comparison for arbitrary relative Cartier base change |
| C3 | RelativeCartierDivisorPullback | Positive divisor iso, canonical section identity and all tensor powers |
| D1 | LocalCartierGeneratorDescent | Regular principal ideal descent along flat local ring maps |
| D2 | CartierIdealStalkDescent | Actual ideal stalk extension and regular generator descent |
| D4 partial | GeneralizedCurveCartierStalks | Cyclic subgroup regular ideal stalks and unconditional divisor flatness |
| C2 consumer | GeneralizedCurveDivisorPullback | Actual subgroup ideal comparison, assuming its effective Cartier condition |
| P1 | VeryAmplePresentationBaseChange | Actual closed projective presentation under arbitrary affine coefficient change |
| P2 partial | RelativeAmplePresentationTransport | Sheaf-iso invariance and affine coefficient change of a global power presentation |
| D3b | FaithfullyFlatFinitePresentation | Faithfully flat descent of finite presentation for modules |

The subgroup consumer does not assert global Cartier descent from cyclicity.
The P2 consumer needs an actual global power presentation; it does not assert
general relative ampleness base change from affine-local witnesses. No new
production structure or conclusion-carrying record was introduced.
