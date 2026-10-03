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
| F06 R5 / ThreeAdicFamilyRealization | Keep the actual p=3 member in a piecewise weakly compatible family. | R5a–R5g below; the existing trace theorem supplies the polynomial input after transport |

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

## Checked source anchors and comparison boundary

[BC] was inspected as the June 24, 2009 preliminary version. Def. 7.2.1
and Prop. 7.2.2 (pp. 91–92) give C1 and T1–T4; §2.1 gives P1;
§§4.2–4.3 give P2 and its Witt input; Lemma 4.4.1 and Props. 4.4.2–4.4.3
give P3; Props. 4.4.6 and Def. 4.4.7 give P4/P6; the rest of §4.4
gives the cyclotomic period and graded ring. §§5.1–5.2 and 6.1–6.3 give
D1 and the tensor/determinant filtered formalism needed for D4–D5.

D2 is not proved by the level-system definition. [BC] Thm. 7.2.10 is a
Honda-system classification over W(k), not the period comparison itself;
it points to Fontaine [18, Ch. IV] and [15, Thm. 1.9]. The proof of [BC]
Thm. 12.3.2, p. 192, **uses** crystallinity and the two-weight bound for
Tate modules. Citing that proof does not discharge this input. A direct
comparison proof, or a fully developed Honda/Dieudonne route plus its
period realization, is still required. The notes switch covariant and
contravariant conventions: reconcile these against [S]'s explicit graded
degrees 0,-1 before any D3 endpoint is accepted.

Read-only reproduction: inspect the cited sections in the linked PDF and
`Scratch/snowden.txt`; run
`rg -n 'B_dR|HodgeTate|deRham|BarsottiTate' FLT .lake/packages/mathlib/Mathlib`.
Mathlib contains Witt vectors and completions, but that search exposes no
ready Galois de Rham comparison API. F04 T1/T2 are foundational progress,
not construction of B_dR or proof of weight two.

W25 R3 first subleaf (cap 150): `ModThreeExtensionCocycle` chooses a lift
of 1 along the already constructed trivial quotient, retains the original
cyclotomic kernel, and proves that its actual displacement is a twisted
1-cocycle. It does not assert vanishing or realize a characteristic-zero family.

## W25 refined P1–P3 split after the wider API search

`Mathlib/NumberTheory/Padics/Complex.lean` already constructs C_p and its
integer ring. `Mathlib/RingTheory/Perfection.lean` already constructs the
inverse-Frobenius ring, its perfectness, valuation and domain theorem.
These names were missed by the older B_dR/HodgeTate-only search. Reuse them:

| Leaf (cap 150 each) | Actual input and output |
|---|---|
| P2a / PadicTilt | Instantiate the integral tilt for the existing C_p; prove p is a nonunit, characteristic p, perfectness and the domain/valuation specialization. |
| P3a / FontaineWittVectors | Construct A_inf as Witt vectors of that actual tilt; identify A_inf/(p) with the tilt using the existing Witt quotient theorem. |
| P1b | Extend the actual local Galois action continuously to C_p and its integers. |
| P2b | Prove the sharp map to O_C with multiplicativity and topology. |
| P3b | Use sharp and Witt expansions to construct theta; prove surjectivity and its kernel theorem. |

P3a's quotient is modulo p and lands in the tilt. It is **not** theta,
whose target is O_C in characteristic zero; the two maps must not be conflated.

D2 is a parent gate, not an executable 150-line theorem. Before attempting
it, refine the selected source proof into tangent/cotangent modules,
Cartier dual compatibility, the period pairing, integrality of that pairing,
Galois equivariance, injectivity, surjectivity, and filtration strictness.
Each of those is itself subject to the 150-line cap and further splitting.
No generic comparison isomorphism may be accepted as a constructor argument.

The HR system is over the rational-place completion, whereas P2a/P3a use
Mathlib's standard C_p over Q_p. Before connecting these tracks, transport
the fields, integer rings, absolute Galois actions and point comparisons
across the rational completion equivalences (the integer equivalence already
appears in `RationalIntegralTransition.lean`). This is a separate capped
base-identification leaf, not a definitional equality to assume.

## R5 refinement: retain the original member by a piecewise family

A fresh read of `GaloisRepFamily.lean:58–65` matters: compatibility imposes
unramifiedness and common Frobenius characteristic polynomials, **not
semisimplicity or equality of extension classes across primes**. Therefore
p=3 may admit a simpler route than R4's general arithmetic realization:
use the original representation at 3, and the split cyclotomic-plus-trivial
representation at the other primes. This does not identify the original
nonsplit representation with a direct sum. The following are unproved,
separately capped leaves (150 each, split again before larger proofs):

| Leaf | Required proof |
|---|---|
| R5a | Construct the integral cyclotomic-plus-trivial rank-two representation for each prime. |
| R5b | Construct its finite-flat p-power models and prove the actual local flatness predicate. |
| R5c | Prove its determinant, good-place unramifiedness and tame-at-two HR clause. |
| R5d | Compute its Frobenius polynomial as (X-1)(X-q), with a common rational polynomial. |
| R5e | Extend the proved original three-adic trace theorem to the required universes and coefficient embedding, then compute its actual characteristic polynomial. |
| R5f | Define the dependent piecewise family, keeping the actual original member at 3; prove compatibility from R5d/R5e. |
| R5g | Supply the integral HR models at every odd prime and the original-member equivalence; handle the number-field/coefficient universes. |

No complete p=3 family or standard-family HR API was found in the current
family-module search. R5a–R5g are a concrete source-code-matched route to
investigate, not a claim that an extension-class obstruction makes the
weak family definition impossible. General reducible-residual inputs can
still have irreducible characteristic-zero generic fibre and are not
resolved by this route merely from their residual filtration.

## W26 Tate recovery refinement (2026-10-03)

T3/T4 are split before implementation. Each complete new file remains at
most 150 lines; all statements use the actual reductions and original lattice.

| Leaf | Required result |
|---|---|
| T3a / TateProjectionSurjective | Lift a point through a countable surjective reduction tower; prove evaluation surjective. |
| T3b / TorsionTateSurjective | Prove the original HR reductions satisfy T3a and apply it. |
| T4a / PDivisibleTateModule | Define the p-adic scalar action through finite residues and prove module laws. |
| T4b / PDivisibleTateTopology | Subspace topology, continuous evaluations and continuous Galois action. |
| T4c / PadicLatticeCompletion | Recover a finite free p-adic lattice from its power quotients. |
| T4d / TorsionTateRecovery | Compare the actual geometric-point tower with those quotients, retaining Galois action. |
| T4e / TorsionTateFree | Transport finite freeness and the computed rank through that comparison. |

R5a–R5g and P1b/P2b/P3b follow this recovery track in the requested order.
No completed comparison, family, or period theorem is assumed by these leaves.

T4c is further split into `FiniteFreeAdicComplete` (basis-coordinate proof),
`PadicLatticeCompletion` (p-adic scalar restriction and completion map), and
`TorsionTensorCompletion` (actual tensor quotient comparison). T4b's scalar
continuity and compactness are a separate `PDivisibleTateCompact` leaf.

T4d's topological identification is split into `TorsionTateHomeomorph`:
the recovered linear equivalence is continuous, and its inverse is continuous
by compactness of the original finite module and Hausdorffness of the Tate limit.

R5b is split before implementation: `SplitKummerModel` constructs the actual
split Kummer finite-flat levels and reads their geometric points;
`SplitKummerPointLaw` identifies addition and the field action on roots;
`SplitKummerCyclotomic` identifies the root action with local cyclotomic
scalars; `CyclotomicTrivialReduction` must compare these points with the actual
p-power tensor quotients; `CyclotomicTrivialFlat` must prove the existing
local flatness predicate, including its rational-place convention. A model
without these comparisons is not accepted as R5b completion.

The standard-member polynomial leaves are `CyclotomicTrivialPolynomial`
(integral determinant and Frobenius polynomial) and
`CyclotomicTrivialBaseChange` (extension and arbitrary framing).
`CyclotomicTrivialRamification` supplies unramifiedness away from p and the
actual second-coordinate tame quotient at two. These do not assert flatness.

For P3b, reuse Mathlib's `RingTheory/Perfectoid/Untilt.lean` and
`RingTheory/Perfectoid/FontaineTheta.lean`. They already construct
`PreTilt.untilt` and `WittVector.fontaineTheta`; the latter has a surjectivity
theorem under surjectivity of Frobenius on the residue quotient. First prove
`IsAdicComplete (Ideal.span {(p : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p]` and the required
Frobenius surjectivity for the actual integer ring. Galois continuity,
the principal kernel and the period-ring comparison remain separate leaves.
