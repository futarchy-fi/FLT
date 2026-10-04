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
| G1-D2d | IntegralPointExtension | 240 | Prove valuation-stalk/fraction-field hypotheses for Z[1/(2p)], identify the canonical generic map, conclude G1Extension. |
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
