# F03–F06: the local comparison input for the family theorem

W25 split, 2026-10-03; base 27edf541. Every new Lean module has a
150-line complete-file cap. Split again before implementing any larger leaf.
Contracts below are proof obligations, never fields assuming comparison or
family existence. The family admission is not discharged by this program.

## Sources and target

[S] Snowden, arXiv:0905.4266v1, §1.2 (weight two), §3 (A1), Thm. 5.1.2.
[T] Tate, *p-divisible groups*, Proc. Conf. Local Fields (1967), §2
(level systems and Tate modules); bibliographic source obligation.
[BC] Brinon–Conrad, *CMI Summer School Notes on p-adic Hodge Theory*,
https://math.stanford.edu/~conrad/papers/notes.pdf (downloaded for this split).
[B] `blueprint/src/chapter/ch03freyreduction.tex:189–211`.

The local target is de Rham admissibility of the original generic fibre,
with graded ranks one in degrees 0 and -1 at each coefficient embedding,
as in [S]. Finite-flat torsion levels alone are not this assertion.
The determinant is cyclotomic; after comparison bounds the weights to
{0,-1}, determinant compatibility must force their multiplicities to be one.
Restriction of scalars has dimension twice the coefficient degree, so the
height alone cannot prove the per-embedding multiplicities.

## Bounded proof leaves

| Gate / module | Required construction or theorem | Dependencies / source |
|---|---|---|
| F03 U1 / TorsionFlatUniverses | Choose finite-flat levels with Type-0 points equivalent to the original arbitrary-universe tensor quotient. | HR open-ideal flatness, finite-point shrinking; [T] §2 |
| F03 U2 / TorsionComparisonsUniverses | Choose models and equivariant comparisons, retaining the original module. | U1 |
| F03 U3 / TorsionGenericUniverses | Transport the prescribed tensor inclusions/reductions and their exactness. | U2, existing tensor maps |
| F03 U4 / TorsionTransitionsUniverses | Extend reductions and prove all coherence diagrams. | U3, proved rational extension |
| F03 U5 / TorsionInclusionsUniverses | Extend inclusions; prove multiplication factorization. | U4 |
| F03 U6 / TorsionExactnessUniverses | Prove actual integral kernel equations and faithfully flat reductions. | U4, rational kernel theory |
| F03 U7 / TorsionRankUniverses | Compute level ranks from the original coefficient degree. | U2, PadicPowerCardinality |
| F03 U8 / TorsionPDivisibleUniverses | Assemble the original-universe system. | U5–U7 |
| F03 C1 / PDivisibleSystemCategory | Construct level morphisms commuting with both maps; identity/composition/category laws. | Existing system; no comparison premise |
| F04 T1 / PDivisibleTateSequences | Construct coherent inverse-limit point sequences and evaluation maps. | System reductions; [T] §2 |
| F04 T2 / PDivisibleTateAction | Construct the pointwise Galois action on these sequences. | T1 |
| F04 T3 / TateProjectionSurjective | Prove surjectivity of level evaluation using finite surjective reductions. | T1, generic faithful-flat surjectivity |
| F04 T4 / TateIntegralRecovery | Identify the original complete lattice with the limit of its p-power quotients. | T3, p-adic completeness and separatedness |
| F04 P1 / CompletedAlgebraicClosure | Construct C_p with its valuation and continuous Galois action. | Completion of algebraic closure; [BC] |
| F04 P2 / TiltIntegral | Construct inverse Frobenius limit of O_C/p, prove perfectness. | P1; Witt vectors alone do not supply this ring |
| F04 P3 / FontaineTheta | Construct A_inf and theta, prove surjectivity and principal kernel. | P2, Mathlib Witt vectors |
| F04 P4 / DeRhamPeriodCompletion | Construct B_dR+ by ker(theta)-adic completion after inverting p. | P3 |
| F04 P5 / CyclotomicPeriod | Construct t, prove its Galois action and filtration degree. | P4, compatible roots of unity |
| F04 P6 / DeRhamPeriodField | Invert t, prove filtration, graded pieces and invariants. | P5; large proofs require further splitting |
| F04 D1 / DeRhamInvariants | Define filtered invariants and the canonical comparison map. | P6; no bijectivity field |
| F04 D2 / PDivisibleComparison | Prove de Rham comparison for the constructed p-divisible system. | T4, P6; major missing theorem, split by source proof before implementation |
| F04 D3 / TwoWeightBound | Deduce support in degrees 0,-1. | D2, integral tangent/dual theory |
| F04 D4 / CoefficientComparison | Prove coefficient decomposition and compatibility at each embedding. | D2 |
| F04 D5 / DeterminantHodgeRanks | Use cyclotomic determinant and D3–D4 to compute both ranks as one. | [S] §1.2 |
| F06 R1 / CharacterFiltrationDeterminant | Prove determinant product for an actual exact character filtration. | Existing filtration_of_reducible; no splitting |
| F06 R2 / ResidualReducibleFiltration | Apply the actual filtration to all reducible residual HR representations. | R1, HR determinant |
| F06 R3 / ExtensionCoordinates | Construct extension coordinates/cocycle retaining its class. | R2; cannot replace the class by zero |
| F06 R4 / ReducibleFamilyRealization | Construct compatible members realizing the original extension. | Character arithmetic and extension-class realization; source missing |
| F06 R5 / ThreeAdicFamilyRealization | Realize the actual p=3 characteristic-zero member. | Proven trace alone is insufficient; source missing |

An fppf colimit is not required just to define the Tate inverse limit. If
D2's chosen proof needs the fppf sheaf instead of the level presentation,
first split representable functors, filtered colimit presheaf, fppf sheaf
property, exactness, and identification of p^n-torsion into separate capped
leaves. Do not assert this colimit exists merely by naming the level system.

## Residual scope obligation

[B] assumes irreducible reduction; the Lean family theorem does not.
A reducible residual representation may lift to an irreducible generic one.
Even when the generic representation is reducible, trace determines only
semisimplification; the target requires an equivalence with the actual
member. R4/R5 need additional mathematics, not a direct-sum substitution or
an extra residual irreducibility hypothesis on the existing target.
