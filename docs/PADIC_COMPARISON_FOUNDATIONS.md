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

## W27 R5b refinement (2026-10-03)

Each leaf below has a 150-line complete-file cap. The model comparison is
proved over a general characteristic-zero local field, so it applies directly
to the rational-place completion; no equality with Q_p is assumed.

| Leaf | Obligation |
|---|---|
| SplitKummerGeneralModel | Split Kummer levels over a ring and a characteristic-zero field, with actual geometric points. |
| SplitKummerGeneralPointLaw | Addition and field action for those points. |
| PrimitiveRootCoordinates | Additive coordinates on roots of unity from a chosen primitive root. |
| SplitKummerResidue | Additive residue coordinates on the actual geometric points, with cyclotomic action. |
| CyclotomicTrivialReduction | Actual p-power quotient-tensor coordinates and their action. |
| CyclotomicCharacterNaturality | Compatibility of the p-adic character with field embeddings and local restriction. |
| CyclotomicTrivialFlat | Apply the comparisons at the rational completion and the proved open-ideal cofinality criterion. |

R5e follows only after these local model obligations. Existing sorted-input
trace results must be transported, without invoking the admitted three_adic.

R5e universe transport is split before implementation (150 lines each):
`FlatCoefficientQuotientUniverses` transports actual quotient models through
a surjective coefficient map; `ThreeAdicTraceUniverses` shrinks the finite
coefficient algebra and frames the original module, applies the proved
sorted-input trace theorem, and descends trace/determinant through the
injective coefficient map. `ThreeAdicPolynomialUniverses` computes the
rank-two characteristic polynomial and its coefficient-extension/framing law.
`CyclotomicTrivialHardlyRamified` assembles the standard integral HR member
from the separately proved determinant, ramification, flatness and tame quotient.

R5f–g are split into `PadicOrderEmbedding` (construct an actual continuous
embedding into the algebraic closure), `RankTwoFraming` (frame scalar
extensions), `ThreeAdicFamily` (dependent family retaining the original at
three), `ThreeAdicFamilyCompatibility` (unramifiedness and common polynomial),
and `ThreeAdicFamilyIntegralModels` (integral witnesses and original-member
equality, with further universe splitting if needed). Each has cap 150.

`ThreeAdicFamily` is split further: `StandardFamilyMember` provides the
framed split member at each prime; the dependent switch then has short
separate equations at and away from three. No semisimplification replaces
the original member in that switch.

`PadicClosureScalars` is an additional 150-line prerequisite: prove the
canonical p-adic integer action on the algebraic closure is continuous by
factoring through Q_p. This is needed by both actual coefficient embedding
and standard-member scalar extension.

R5g universe packaging is split before implementation: `ULiftCoefficientTensor`
compares an actual tensor extension to independent coefficient/module lifts;
`ULiftHardlyRamified` transports the four clauses using the already proved
surjective-coefficient and coordinate-change results; `ULiftGenericRecovery`
proves cancellation of those lifts after coefficient extension. These feed
the family integral-witness package. All complete files are capped at 150 lines.

`StandardIntegralUniverses` packages the lifted standard witnesses before
`ThreeAdicFamilyIntegralModels` selects the original witness at three and
those standard witnesses elsewhere. The final p=3 family statement is a new
theorem; the existing general-prime admitted theorem is left unchanged.

## W27 F04 period prerequisites

The live API also contains `Mathlib/RingTheory/Perfectoid/BDeRham.lean`.
It defines `fontaineThetaInvertP`, `BDeRhamPlus` and `BDeRham`; it does not
prove the principal-kernel theorem, DVR structure, or comparison theorem.
Reuse these constructors rather than duplicating them. New capped leaves:

| Leaf (cap 150) | Required result |
|---|---|
| ComplexIntegerAdic | Identify p-power ideals with norm balls in O_C; deduce actual p-adic completeness. |
| ComplexIntegerFrobenius | Construct p-th roots in O_C using algebraic closedness of C_p; prove mod-p Frobenius surjective. |
| ComplexFontaineTheta | Instantiate sharp and theta on the actual tilt and prove theta surjective. |
| ComplexDeRhamRings | Instantiate the existing localized theta and completion constructors. No principal kernel or comparison claim. |

P1b's continuous Galois action, P3's principal kernel and D2's comparison
still require independent proofs; these constructions alone do not discharge them.

## W28 F04 action and period-ring gates (split before implementation)

Each new module is capped at 150 complete source lines. Work in this order:

1. `ComplexGaloisAction`: extend spectral-norm-preserving algebraic Galois
   automorphisms to ring automorphisms of the actual C_p; prove action laws.
2. `ComplexGaloisContinuity`: derive algebraic orbit continuity from open
   stabilizers, then joint continuity on C_p from density and isometry.
3. `ComplexIntegerGalois`: restrict the actual action to O_C; prove joint
   continuity and the inclusion comparison.
4. `ComplexTiltGalois`: induce actions on O_C/(p) and its perfection, with
   coordinate formulas and action laws.
5. `ComplexSharpEquivariance`: prove sharp commutes with the actual action
   using uniqueness of the multiplicative inverse-Frobenius lift.
6. `ComplexThetaEquivariance`: induce the Witt action and prove theta
   equivariance, retaining the actual maps.
7. Principal theta-kernel generator, followed by DVR/filtration structure:
   inspect the available proof API and split further before implementing.
   Localization at all hypothetical generators is not an existence proof.
8. General-prime character classification/reducible-residual route follows
   these F04 gates; split a concrete arithmetic leaf before implementing.

F07–F15 (potential modularity, geometric existence, common coefficients,
attached representations, Brauer and effective descent, general original
member packaging) remain large missing theory. Do not start them without a
bounded ready leaf. No new field may assume a target conclusion. The original
family admission is outside the permitted module-edit scope.

W28 topology refinement before implementation (cap 150):
`ComplexTiltContinuity` gives O_C/(p) its quotient topology and the actual
integral tilt its inverse-limit topology, then proves joint continuity of
the induced action by its coordinate formulas. Comparison with the tilt
valuation topology is a separate obligation, not assumed by an instance.

W28 principal-kernel refinement before implementation (each cap 150):
`ComplexSharpSurjective` constructs compatible integral p-power roots and
proves sharp surjective. `ComplexTiltDivisibility` constructs coordinatewise
quotients of multiplicative root sequences, deriving divisibility from
sharp. `ComplexThetaGenerator` chooses a sharp lift of p and proves that
its Teichmuller representative minus p is in the actual kernel, with the
correct mod-p divisibility criterion. `AdicPrincipalKernel` supplies the
bounded algebraic lifting lemma: a separated kernel over a complete source
is generated by a chosen element once the genuine mod-p reduction and
p-saturation properties are proved. `ComplexThetaPrincipal` applies it to
the actual Witt ring and theta. Split again if any proof exceeds the cap.

W28 localization/completion refinement before implementation (caps 150):
`ComplexThetaLocalized` identifies the existing localized theta with the
functorial localization map, transports surjectivity and the proved kernel
generator. `ComplexDeRhamFiltration` identifies the completion ideal with
the span of that actual element, proves adic completeness and identifies
all filtration powers with evaluation kernels. The DVR gate additionally
requires a field residue quotient, a nonzero regular completed generator,
and the resulting valuation-domain/PID argument; do not infer these from
principality or completeness alone.

W28 residue-field refinement before implementation (caps 150):
`ComplexIntegerInvertP` proves that inverting p in O_C gives the actual C_p,
using geometric decay of the p-adic norm. `ComplexDeRhamResidue` extends
theta to B_dR^+ with target C_p, proves surjectivity, identifies its kernel
and derives the local-ring structure. These do not assert regularity of
the completed parameter or a DVR without proving those separately.

W28 regularity/DVR refinement before implementation (caps 150):
`AdicCompletionRegular` proves that a nonzero generator in a domain stays
regular in its principal-ideal completion, by cancellation one level higher.
`AdicPrincipalDVR` derives unit-times-power factorizations from separatedness
and a principal maximal ideal, then derives the domain and DVR structure
when the generator is regular. `ComplexDeRhamDVR` proves the actual localized
theta generator nonzero and applies both results to the actual B_dR^+.

W28 F06 bounded follow-up after the F04 ring gates (caps 150):
`GeneralInertiaTwo` derives square-zero inertia at two for every odd prime
from the original HR quotient and cyclotomic determinant, generalizing the
existing three-adic arithmetic proof in a new module. Then
`CharacterFiltrationUnipotent` proves both actual characters of any exact
filtration trivial on a square-zero inertia element, and
`ResidualCharacterInertiaTwo` applies it to general-prime residual HR inputs.
This is a local arithmetic constraint, not global character classification
or generic reducibility. The general compatible-family route remains open.


### W28 checked result and remaining boundary

Checked at 2026-10-03T17:34:52.492118+00:00; evidence is the lane's untracked
`W28_FINAL_CHECKS.json`, individual foreground build/lint logs and
`W28_AXIOMS.log`. All 22 modules pass individual
`LEAN_NUM_THREADS=2 lake build MODULE` and `lake exe runLinter MODULE`.
All 116 new named declarations use only propext, Classical.choice and
Quot.sound. The largest complete source file is 84/150 lines.

The actual C_p action is jointly continuous; its integer-ring restriction
and the induced inverse-limit tilt action are constructed and continuous.
Sharp and theta are equivariant. The constructed element [p-flat]−p
actually generates the integral and localized theta kernels. The actual
B_dR+ has residue field C_p, a regular completed parameter, the corresponding
adic filtration, and a proved DVR structure. Recheck the ring endpoint by
building/linting `FLT.PadicHodgeTheory.ComplexDeRhamDVR`; recheck equivariance
through `FLT.PadicHodgeTheory.ComplexThetaEquivariance` and continuity through
`FLT.PadicHodgeTheory.ComplexTiltContinuity`.

The residual arithmetic endpoint is
`exists_reducible_character_filtration_inertia_two`: an actual exact
filtration with cyclotomic product and both characters trivial on inertia
at two, for every odd prime. It does not classify the characters globally
or make a reducible residual representation's generic fibre reducible.

Still missing: global general-prime character classification and compatible
families; tilt valuation-topology comparison; Galois action on the completed
period rings and the cyclotomic logarithmic period; period-field invariants
and graded-piece identifications; p-divisible comparison and per-embedding
weight multiplicities. F07–F15 remain large missing theory and were not
started. The boundary audit still finds sorryAx in the unchanged general
family theorem and sorryAx plus Mazur_statement in the FLT endpoint.

## W29 F04 continuation (split before implementation)

All leaves have a 150-line complete-file cap. Preserve the actual rings and
maps; no structure field may supply a comparison theorem or period identity.

| Leaf | Required result |
|---|---|
| ComplexLocalizedGalois | Extend the actual Witt action through inversion of p; prove group laws and equivariance of theta into C_p. |
| AdicRingFunctor | Construct the ring map on an ideal-adic completion from a ring endomorphism preserving that ideal; prove evaluation, identity and composition laws. |
| ComplexDeRhamGalois | Apply the completion construction to the actual localized action; prove group laws and extension of the source action. |
| ComplexDeRhamEquivariance | Prove completed theta equivariant and all parameter-ideal powers stable. |
| CyclotomicTiltRoots | Choose compatible primitive p-power roots, construct epsilon in the actual tilt, and prove sharp(epsilon)=1 and the Galois power formula. |
| CyclotomicLogConvergence | Construct the rational logarithmic series in the theta-adic completion and prove convergence and functoriality. |
| CyclotomicLogParameter | Prove the logarithm is a nonzero uniformizer and its cyclotomic transformation formula. |
| DeRhamFieldIdentification | Identify the existing B_dR localization with inversion of the proved period, then its fraction field and filtration. |
| DeRhamGradedTwists | Identify each graded piece with the actual cyclotomic twist of C_p. |
| DeRhamFixedField | Prove the fixed-field theorem with its analytic inputs; a DVR or residue field calculation alone is insufficient. |

The tilt valuation-topology comparison is needed only if a subsequent proof
uses it; the algebraic extension through ideal powers does not depend on it.
Before the cyclotomic leaves, inspect compatible-root and formal-logarithm
APIs and split again if a leaf would exceed its cap.

The p-divisible comparison remains a parent, refined into separate capped
obligations: rational-place/base-field transport; tangent/cotangent and dual
constructions; actual period pairing; its integrality; equivariance;
injectivity; surjectivity; filtration strictness. The coefficient-embedding
rank parent splits into coefficient tensor decomposition, compatibility of
the pairing on each component, the two-weight support bound, determinant
compatibility, and the rank-one conclusion in each degree. None is assumed
in a constructor. F06 global classification is attempted only after these
F04 gates if a bounded arithmetic route exists; residual reducibility is
never promoted to generic reducibility.

W29 cyclotomic-root refinement before implementation (caps 150):
`ComplexCyclotomicRoots` chooses an actual integral primitive p-th root,
extends it using integral p-th roots, and proves primitivity at every level.
`ComplexCyclotomicTilt` reduces that multiplicative sequence to epsilon,
proves sharp(epsilon)=1 and epsilon≠1, and locates [epsilon]−1 in ker(theta).
The coordinate Galois formula is a separate `ComplexCyclotomicAction` leaf;
a formula on finite roots is not yet the logarithm's p-adic scalar formula.

W29 logarithmic-sum refinement before implementation (caps 150):
`AdicSeries` proves existence, uniqueness and functoriality of sums with
nth term in the nth ideal power in a complete ring. `ComplexCyclotomicLog`
uses the actual completed [epsilon]−1 and proves all positive integer
denominators are units, then constructs the logarithmic sum and its finite
congruences. Nonvanishing, order one and the p-adic cyclotomic scalar law are
separate obligations; formal summability does not prove them.

`ComplexCyclotomicLogTransport` (cap 150) proves that the actual Galois action
fixes every rational logarithm coefficient and carries t to the adic sum at
the transformed argument. This is functoriality of the logarithmic sum,
not the still-required equality with the cyclotomic character times t.

### W29 comparison and coefficient-rank contracts

These remain proof obligations, not completed modules. Each prospective
complete module is capped at 150 lines; split any contract further before
implementation if its source proof needs more. Invariants and the logarithm's
order/character law are prerequisites, not facts supplied by these contracts.

| Prospective leaf | Required artifact | Prerequisite |
|---|---|---|
| PDivisibleRationalPlaceTransport | Actual field/integer/Galois identifications for the original system and standard Q_p. | Existing rational-place equivalences |
| PDivisibleCotangentTransitions | Cotangent modules and compatible level maps of the actual finite-flat system. | Original p-divisible system |
| PDivisibleTangentDuality | Tangent/cotangent limits and compatibility with Cartier duality. | Cotangent transitions and actual Cartier dual |
| PDivisiblePeriodPairing | Construct the actual pairing of Tate points with periods. | Tangent duality, period-ring theory |
| PDivisiblePeriodIntegrality | Prove the image and filtration bound for that pairing. | Actual pairing |
| PDivisiblePeriodEquivariance | Intertwine the original Galois action with the period action. | Actual pairing and the cyclotomic law |
| PDivisiblePeriodInjective | Prove injectivity of the resulting comparison map. | Pairing, Tate recovery |
| PDivisiblePeriodSurjective | Prove surjectivity from the integral theory. | Integrality, injectivity and dimension argument |
| PDivisibleComparisonStrict | Prove strictness for the specified filtrations. | Bijectivity, integral bounds |
| CoefficientEmbeddingDecomposition | Decompose the actual scalar extension by embeddings. | Original coefficient field and splitting field |
| CoefficientPairingComponents | Prove the comparison respects that decomposition. | Pairing, coefficient decomposition |
| CoefficientTwoWeightSupport | Prove each component has support in degrees 0,-1. | Strict comparison, tangent/dual bounds |
| CoefficientDeterminantWeights | Identify the determinant filtration at each embedding. | Component comparison and cyclotomic determinant |
| CoefficientGradedRanks | Deduce both graded ranks are one, retaining each embedding. | Support, determinant and original rank two |

No finite-flat quotient, residual filtration, total height, or abstract
comparison isomorphism can replace the obligations in this table.

### W29 result and next proof boundary

Checked at 2026-10-03T18:09:50Z by `W29_FINAL_CHECKS.py` (lane-local,
untracked): ten new modules, 68 audited declarations, maximum 94/150 lines.
Every new module passed an individual foreground build and lint. Reproduce
with `W29_VALIDATE.py`, `W29_MAKE_AUDIT.py`, `lake env lean W29_AXIOMS.lean`,
and `W29_FINAL_CHECKS.py`; the report records exact logs and hashes.

The actual localized and completed Galois maps satisfy the group laws.
Completed theta is equivariant and every nonnegative parameter-ideal
filtration level is preserved. These are algebraic statements, not joint
continuity for a topology on B_dR+; the tilt valuation-topology comparison
was not used or established.

The actual primitive p-power root sequence supplies epsilon, with sharp
one and epsilon nontrivial. Its multiplicative lift has the cyclotomic
coordinate formula for the original algebraic Galois character. The
logarithmic sum t is constructed in the actual B_dR+ using proved unit
denominators. It has all finite congruences, lies in the first filtration
step, and equals [epsilon]−1 modulo the square of the parameter ideal.
Galois carries it to the logarithmic sum at [sigma(epsilon)].

Still required before using t as a period uniformizer: prove that the
completed [epsilon]−1 has order one, prove the logarithm has the same order,
and prove the p-adic scalar formula sigma(t)=chi(sigma)t. The coordinate
formula is not that formula: passing from finite residues to p-adic
exponentiation requires a justified topology/limit argument. The local
formal-log API has coefficient, derivative and substitution results; it
does not supply this actual p-adic exponentiation bridge.

Consequently the B_dR identification via t, its graded cyclotomic twists
and fixed-field theorem, and all comparison/rank contracts above remain
open. The F06 source check still finds only an actual residual character
filtration and the explicitly three-adic `Assembly.CharacterInputs` route;
no general global classification was implemented. F07–F15 were not started.
The boundary audit still finds sorryAx in the unchanged general family
theorem and sorryAx plus Mazur_statement in the FLT endpoint.
