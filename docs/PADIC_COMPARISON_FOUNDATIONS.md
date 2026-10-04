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

## W30 cyclotomic order and scalar-law split (before implementation)

Each implementation leaf has a 150-line cap; split again before exceeding it.
The dependencies below are proofs to construct, never hypotheses to insert
into a period/comparison structure.

| Leaf | Concrete obligation | Prerequisite |
|---|---|---|
| CyclotomicShift | Construct shifted epsilon, its p-th power and actual sharp values. | W29 compatible roots |
| CyclotomicKernel | Construct the geometric sum in A_inf, prove theta vanishes and factor [epsilon]-1. | CyclotomicShift |
| CyclotomicReduction | Compute its zeroth Witt coefficient and establish its sharp valuation. | CyclotomicKernel; cyclotomic valuation calculation |
| CyclotomicPrincipal | Prove every theta-kernel element is divisible by that geometric sum. | CyclotomicReduction; adic division |
| CyclotomicCompleted | Transport principality, factor the completed argument, and prove the other factor is a unit. | CyclotomicPrincipal; sharp of shifted epsilon |
| CyclotomicLogOrder | Deduce that t and z generate the maximal ideal from their square-ideal congruence. | CyclotomicCompleted |
| CyclotomicScalarTopology | Construct scalar embeddings and the topology needed for p-adic exponent limits. | Actual period ring; separate from ideal-adic topology |
| CyclotomicScalarLog | Prove logarithm/exponent compatibility and sigma(t)=chi(sigma)t. | CyclotomicScalarTopology; W29 sum transport |
| DeRhamPeriodLocalization | Identify the existing B_dR with inversion of t and the fraction field. | CyclotomicLogOrder |
| DeRhamGradedAction | Identify graded pieces and their cyclotomic action. | CyclotomicScalarLog |
| DeRhamFixedField | Prove the fixed-field theorem on the actual ring. | Galois descent on the completed field |

The W29 comparison-contract split remains downstream; no comparison or
fixed-field conclusion follows just from kernel membership or a formal log.

W30 refinement before kernel-principality implementation: use Frobenius
instead of the separate sharp-valuation calculation. Add capped leaves
`AdicUnitReflection` (units lift through a surjection with adically small
kernel) and `ComplexThetaUnitReflection` (theta after Witt Frobenius detects
units). If the geometric sum is xi*b for the known generator xi, applying
theta after Frobenius gives p = (p^p-p)*theta(phi(b)). Cancel p to prove the
image of b is a unit and reflect that unit to A_inf. This proves actual
integral principality, without assuming or needing a tilt norm comparison.

W30 scalar prerequisite refinement (caps 150): `ComplexPadicScalars`
constructs the Z_p scalar map from W(F_p), then extends it to Q_p using
nonzero = unit * p^n. `ComplexPadicScalarAction` proves the actual Galois
action fixes this map. The separate topology leaf must then equip each
finite theta quotient with its p-adic coefficient topology and establish
compatible limiting maps. Ideal-adic convergence alone cannot implement
this step: p is a unit, so its powers do not approach zero in the ideal-adic
topology. This distinction must survive the logarithm/exponent bridge.

One further scalar leaf, `ComplexPadicScalarResidue` (cap 150), proves that
theta of the constructed scalar embedding is the standard inclusion into
C_p. Use natural approximations modulo p^n and p-adic separatedness of O_C
to identify the integral maps, then the fraction-ring universal property.
This supplies genuine scalar compatibility before any topological limit.

W30 implemented boundary: shifted epsilon and its actual sharp values;
the geometric-sum factorization and integral/localized kernel principality;
completed unit factor; z and t irreducible, nonzero and outside the square
of the maximal ideal; all nonnegative filtration powers generated by t.
The Q_p embedding is constructed from W(F_p), is Galois-fixed, and theta
agrees with the standard inclusion in C_p. No scalar-action law for t or
period-field invariant theorem is asserted by these results.

Next scalar/topology leaves, each capped at 150 lines and split again if
needed, in dependency order:

1. For each n, prove p-adic separatedness of A_inf/(xi^n) for the actual
   cyclotomic generator xi (including the closedness/regularity argument).
2. Construct compatible p-adic topologies on these integral quotients and
   their p-inverted quotients. Prove the scalar and quotient maps continuous.
3. Derive convergence of integer exponent approximants to the actual
   Galois-transformed epsilon from its compatible-root coordinate formula.
4. Prove the finite logarithm/power identity in every theta quotient, with
   the denominator and limit bounds needed for p-adic exponent convergence.
5. Pass to the separated inverse limit to prove sigma(t)=chi(sigma)t using
   the constructed scalar embedding, then resume period-field/graded/fixed
   field and the W29 comparison-contract leaves.

`complexDeRham_prime_pow_notMem` proves the precise obstruction to replacing
steps 1–4 by theta-adic convergence: every p^n is outside the first theta
ideal. Thus the usual p-adic decay is a separate topology obligation.

## W31 separatedness split (before implementation)

Every new module is capped at 150 lines. First prove cancellation modulo
powers of p from regularity modulo p, then use completeness of A_inf to
show divisibility by each power of the cyclotomic generator is closed.
No separatedness or closedness of a theta quotient is assumed.

| Leaf | Concrete obligation | Prerequisite |
|---|---|---|
| AdicRegularCancellation | Cancel a regular element modulo every power of a nonzero parameter. | Domain and explicit mod-parameter regularity |
| AdicPrincipalClosed | Lift arbitrarily accurate principal-ideal approximations to actual divisibility. | Cancellation and parameter-adic completeness |
| ComplexCyclotomicRegular | Prove actual cyclotomic-generator regularity modulo p and its power versions. | W30 association; nonzero prime tilt |
| ComplexThetaQuotientSeparated | Prove p-adic separatedness for every actual integral theta quotient. | Closed principal powers |
| ComplexThetaQuotientTopology | Equip integral quotients with Hausdorff p-adic topologies and continuous transitions. | Proved separatedness |

The p-inverted coefficient topology, exponent convergence, finite logarithm
bounds, scalar law, invariants and comparison obligations remain subsequent
leaves. Inverting p must not replace the coefficient topology by the
indiscrete topology of the unit ideal.

W31 topology refinement (before implementation, caps 150): add
`AdicQuotientComplete`, proving that a surjective linear image of an
adically precomplete module is precomplete using the existing completion
map surjectivity theorem. Combine this with the proved theta-quotient
separatedness to obtain completeness rather than postulating it.

W31 p-inversion refinement (before implementation, caps 150):
`AdicLocalizationBasis` constructs the ring-neighborhood basis p^k R inside
R[1/p], using actual denominator clearing for multiplication continuity.
`AdicLocalizationTopology` proves Hausdorffness and continuity from those
lattices, with injectivity supplied by the proved absence of p-torsion.
`ComplexThetaQuotientInvertP` instantiates this topology for the actual
integral theta quotients. These leaves do not use the unit-ideal topology.

W31 scalar refinement (before implementation, caps 150):
`PadicScalarTopology` compares the standard Z_p topology with its p-adic
ideal topology and proves continuity of integral homomorphisms into adic
rings. `ComplexThetaQuotientScalars` constructs actual Z_p and Q_p maps
into the new finite quotients and proves continuity using the open
inclusion Z_p → Q_p, without any asserted scalar-law hypothesis.

W31 compatibility refinement (before implementation, caps 150):
`AdicLocalizationEmbedding` proves that the integral inclusion is an open
embedding, so the localization induces exactly the original p-adic
topology. This rules out a merely continuous but weaker coefficient
topology and supplies the compatibility needed for later limit bounds.

W31 finite-quotient identification (before implementation, cap 150):
`ComplexThetaQuotientComparison` identifies (A_inf/(ker theta)^n)[1/p]
with A_inf[1/p]/(ker theta[1/p])^n by computing the surjective localized
quotient map and its kernel. This connects the coefficient construction
to the actual finite levels used by the existing de Rham completion.

W31 final topology transport leaf (before implementation, cap 150):
`ComplexFiniteThetaTopology` transports the Hausdorff coefficient ring
topology to the existing finite de Rham levels through the canonical
identification and proves continuity of their existing quotient transitions.

W31 scalar compatibility transport (before implementation, cap 150):
`ComplexFiniteThetaScalars` proves that the continuous finite scalar maps
are precisely the evaluations of the already constructed Q_p embedding
into B_dR+, by integral representatives and fraction-ring uniqueness.

W31 proof entry points: `complexTheta_ker_pow_isClosed` and
`complexIntegralThetaQuotient_isAdicComplete` establish closedness and
separated completeness from regular reduction of the actual cyclotomic
generator. `complexThetaQuotientInvertP_isOpenEmbedding` identifies the
integral coefficient topology inside the p-inversion. The canonical
`complexFiniteThetaQuotientEquiv` identifies these p-inversions with the
finite levels in the existing definition of B_dR+. Their quotient
transitions are continuous, and `complexFiniteThetaQuotientScalars_eval`
identifies the continuous Q_p maps with evaluations of the existing scalar
embedding. These are algebraic and topological prerequisites, not the
cyclotomic logarithm transformation law.

Next implementation leaves (each cap 150, split before exceeding):

1. Establish the p-adic bounds on the cyclotomic exponent differences in
   each integral theta quotient. Relate the integer approximants to the
   actual transformed epsilon via the compatible-root coordinate law;
   scalar continuity alone is not exponent continuity.
2. Prove the finite logarithm/power polynomial identity, then the required
   denominator and limit bounds in the coefficient topology at each level.
3. Use Hausdorff uniqueness at every finite level and separatedness of the
   theta inverse limit to prove sigma(t) = chi(sigma)t. The new coefficient
   topology must not be replaced by the theta-adic topology on B_dR+.
4. Continue the period-field localization, graded cyclotomic twists,
   fixed-field theorem, and comparison-contract split above. The general
   family admission cannot be removed just from quotient separatedness.

## W32 exponent convergence split (before implementation)

Each leaf has a 150-line cap. The generic estimate first raises differences
in powers of an ideal containing p; splitting powers of (p) + ker(theta)
then gives a p-adic estimate modulo each fixed theta power.

| Leaf | Concrete obligation | Prerequisite |
|---|---|---|
| IdealPowerDifference | Bound iterated p-power differences in powers of an ideal containing p. | Geometric sums and ideal multiplication |
| ComplexCyclotomicApproximation | Construct the two shifted Teichmuller roots with equal theta image and identify their p-power endpoints. | W29 coordinate action; actual sharp equivariance |
| ComplexCyclotomicPowerBounds | Bound the actual Galois/power difference by (p)^k + ker(theta)^r. | Generic estimate and shifted roots |
| ComplexCyclotomicPowerConvergence | Prove integral and localized finite-level convergence in the W31 coefficient topology. | Bounds and continuous integral inclusion |

Finite logarithm identities, denominator control, the cyclotomic scalar
law, fixed fields and comparison remain later leaves; none is a hypothesis
of these convergence statements.

W32 logarithm refinement (before implementation; each cap 150):
`PowerSeriesLogPower` proves the formal logarithm multiplication and
integer-power identities by derivatives and the constant coefficient.
`NilpotentSeriesEvaluation` constructs algebraic evaluation at nilpotents
and identifies it with any sufficiently long finite truncation.
`NilpotentLogPower` transports the formal identity to finite logarithms.
Finite-level continuity then handles fixed finite sums and their genuine
rational denominator inverses, without requiring completeness of the
localized coefficient quotients.

W32 substitution refinement (before implementation; cap 150):
`NilpotentSeriesSubstitution` proves that substitution by a nilpotent
constant gives a constant series and commutes with zero-constant formal
substitution. This keeps the finite-logarithm proof algebraic.

W32 scalar and finite-log refinement (before implementation; cap 150 each):
`PadicResidueConvergence` proves convergence of the natural representatives
of Z_p residues in the standard topology. `ComplexFiniteLogAlgebra`
constructs rational algebra structures from the existing scalar maps and
identifies the logarithm coefficients with their genuine inverse formula.
`ComplexFiniteLogEvaluation` identifies evaluations of t and sigma(t) with
finite logarithms. `ComplexFiniteLogLimit` combines the exponent and scalar
limits by Hausdorff uniqueness; the separated completion then gives the
actual scalar law in `ComplexCyclotomicLogCharacter`.

W32 limit refinement (before implementation; cap 150):
`FiniteLogContinuity` proves the polynomial continuity and a generic
Hausdorff limit theorem for natural powers and scalar approximants.
No infinite coefficient sum or uniform denominator estimate is needed at
a fixed nilpotent quotient: its logarithm is a finite polynomial.

W32 period-field refinement (before implementation; caps 150):
`DiscreteValuationLocalization` identifies localization at a uniformizer
with a fraction field. `ComplexDeRhamDenominators` proves that Mathlib's
actual generating set consists of nonzero associates of the completed
parameter and contains that parameter. `ComplexDeRhamFractionField`
identifies the existing B_dR with the fraction field and with inversion
of the already constructed t. These are algebraic identifications;
Galois fixed fields still require a separate descent theorem.

W32 nonnegative graded refinement (before implementation; caps 150):
`PrincipalGradedPiece` constructs the actual quotient (t^n)/(t^(n+1))
and its linear identification with R/(t), by cancellation in the domain.
`ComplexDeRhamGraded` identifies those quotients additively with C_p and
computes the cyclotomic twist on transformed representatives. Negative
levels, a full graded algebra, and fixed-field descent remain later leaves.

W32 graded-action refinement (before implementation; cap 150):
`ComplexDeRhamGradedGalois` descends the existing action on the actual
principal ideals to their quotient and proves the C_p coordinate formula
with cyclotomic weight n. This is not a fixed-field assertion.

W32 field-action refinement (before implementation; cap 150):
`ComplexDeRhamFieldGalois` extends the actual ring action to the identified
fraction field, proves the character formula for every integer power of
t, and proves that the existing Q_p scalars are fixed. The reverse
fixed-field inclusion is a separate missing theorem; scalar fixedness
must not be substituted for equality of the invariant field with Q_p.

## W32 downstream fixed-field and comparison obligations

The completed exponent/log bridge now has implementation entry points
`complexCyclotomicPower_tendsto_finite`, `finiteNilpotentLog_pow`,
`complexCyclotomicLog_character_finite` and
`complexCyclotomicLog_galois_character`. The finite logarithm is a polynomial
in every fixed theta quotient; its actual rational coefficient inverses
are identified by `complexLogCoefficient_eval`. Thus this argument needs
neither a denominator bound uniform in quotient order nor a completeness
assumption on the p-inverted coefficient quotients.

`complexDeRhamLogLocalizationEquiv` identifies the existing B_dR with
inversion of the existing t. `complexDeRhamGradedCoordinate_galois` computes
the actual descended action on (t^n)/(t^(n+1)) for n >= 0. The field action
fixes the existing Q_p scalars and has the integer-power character law.
These entry points do not establish the reverse fixed-field inclusion.
Check these statements by rebuilding their named modules and printing
their axioms; W32's handoff records the checked snapshot and logs.

Each following leaf retains the 150-line cap, and must be split again
before implementation if the source proof exceeds it:

| Next leaf | Required theorem, without an assumed conclusion | Prerequisite |
|---|---|---|
| CompletedComplexFixedScalars | The fixed elements of the actual C_p action are exactly the standard Q_p image. | Proved quantitative Galois approximation / Ax-Sen-Tate input |
| CompletedComplexTwistVanishing | The nonzero cyclotomic twists of C_p have no invariant vectors. | Actual character, norm estimates, and descent |
| DeRhamIntegerGraded | Extend the actual quotient-coordinate construction to every integer filtration level in B_dR. | Field identification, integer powers of t |
| DeRhamInvariantOrder | A nonzero invariant field element has filtration order zero. | Integer graded twists and their invariant vanishing |
| DeRhamFixedScalars | After subtracting the invariant residue scalar, positive order forces zero. | Invariant order and the completed-complex fixed-field theorem |
| PDivisibleRationalPlaceTransport | Transport the original rational-place system and Galois action to the standard Q_p setting. | Existing place equivalences; retain original system |
| PDivisibleCotangentTransitions | Construct levelwise cotangent objects and their actual transition maps. | Original finite-flat system, no comparison assumptions |

After these gates, continue the W29 comparison and coefficient-rank table:
tangent duality, the actual period pairing, integrality, equivariance,
injectivity, surjectivity, strictness, then per-embedding decomposition,
component pairings, two-weight support, determinant weights and ranks.
No comparison isomorphism is inserted as a record field. In particular,
the family admission remains downstream of these missing theorems.

## W33 analytic descent inputs (split before implementation)

The completed fixed-field and twist-vanishing endpoints require separate
arithmetic proofs. In particular, averaging a finite orbit loses the
p-adic norm of its cardinality; density alone does not bound that loss.
The following leaves have a 150-line source cap each. Split further before
exceeding a cap. This table is a proof plan, not a claim of completion.

| Leaf | Concrete output | Dependency / boundary |
|---|---|---|
| ComplexGaloisApproximation | Approximate a completed fixed vector by algebraic vectors whose entire Galois displacement is bounded by the approximation error. | Existing isometric action, ultrametric inequality, density |
| PadicGaloisOrbit | Construct the actual finite algebraic orbit and its invariant sum. | Minimal polynomial root finiteness and orbit permutation |
| PadicGaloisAverage | The normalized orbit sum lies in Q_p and bounds distance by the inverse norm of the orbit cardinality times the displacement bound. | Orbit sum; algebraic Galois fixed-field theorem |
| ComplexScalarClosed | The actual Q_p image in C_p is closed; arbitrarily close Q_p approximants give membership. | Complete Q_p, isometric scalar embedding |
| PadicAxEstimate | Replace the orbit-cardinality loss by a constant depending only on p, uniformly for every algebraic element and every displacement bound. | Missing arithmetic Ax estimate; ordinary averaging is insufficient |
| ComplexAxDescent | Apply that proved uniform estimate to algebraic approximants and closedness to obtain the completed fixed-field theorem. | PadicAxEstimate; do not assume completed fixed-field descent |
| CyclotomicTowerTraceBounds | Construct normalized traces in the actual cyclotomic tower and prove uniform bounds for the relevant transition maps. | Actual local ramification and different estimates; split these estimates separately |
| CyclotomicTwistDescent | Control character-weighted approximation errors and rule out nonzero eigenvectors of nonzero integral cyclotomic weight. | Tower trace bounds; requires proof, not a vanishing field in a structure |
| FractionalPrincipalFiltration | Construct the actual submodules t^n B_dR+ inside B_dR for every integer n, with coefficient equivalences and next-level inclusions. | Existing field and nonzero period |
| FractionalPrincipalGraded | Identify actual consecutive submodule quotients with the residue module. | FractionalPrincipalFiltration |
| ComplexIntegerGradedCompatibility | Specialize to C_p coordinates, prove scalar and multiplication compatibility and the descended character action. | FractionalPrincipalGraded, original theta and character law |
| ComplexInvariantOrder | Use the proved nonzero twist vanishing to force invariant order zero, then subtract the fixed residue. | Both analytic endpoints; no endpoint assumptions |

The comparison contracts in the W32 table remain after these leaves.

### W33 implementation boundary

The new approximation entry points are
`complexGalois_fixed_algebraic_approximation` and
`complexTwist_fixed_algebraic_approximation`. They use the original action,
actual algebraic approximants and a bound uniform over all automorphisms.
`padicGalois_exists_scalar_approximation` constructs a genuine Q_p scalar,
but its error bound is `norm(card(orbit(a)))⁻¹ * r`. The actual orbit is
proved finite from the minimal polynomial, and its average is descended
using the algebraic (not completed) Galois fixed-field theorem.

`complexGalois_fixed_mem_range_of_uniform_estimate` proves only the
completion reduction: it explicitly assumes `C > 0` and, for every
algebraic `a` and `r > 0`, a scalar `b` with distance at most `C*r` whenever
all conjugate displacements are at most `r`. The constant must be
independent of `a`. This arithmetic estimate remains unproved. The
closedness theorem `complexScalar_isClosed` supplies the final limit step;
it does not establish density of scalar approximants by itself.

The actual integer filtration now consists of the submodules `t^n B_dR+`
inside the existing field. `fractionalPrincipalNext_comap` identifies
the actual next level with the ideal `(t)` in coefficient coordinates.
`complexDeRhamIntegerGradedCoordinate` therefore identifies each actual
integer quotient with C_p. The product formula
`fractionalPrincipalGradedMul_mk` proves that its multiplication comes
from multiplication in the original field, including negative degrees.
The scalar action agrees with original theta; the linear equivalence
and finrank theorem give dimension one over the actual C_p. The algebra
laws retain the required degree reindexing. The original field action
descends and has weight n, is semilinear over C_p and preserves products.
These declarations can be checked by building their named modules,
running their individual linters and printing their axioms; the W33
handoff records the checked snapshot, commands and evidence logs.

Still open: the uniform arithmetic Ax estimate, actual cyclotomic tower
trace bounds and completed twist vanishing. Consequently invariant-order
control, the reverse period fixed-field inclusion and the comparison
contracts are not proved by W33. No uniform bound or completed invariant
vanishing has been installed as an instance, structure field or axiom.


## W34 elementary Ax proof split (before implementation)

Use Hasse derivatives of the actual minimal polynomial, not an assumed
trace bound. If all conjugates of a are within r, the (n-k)-th Hasse
derivative at a has norm at most r^k. Its degree is k and its leading
coefficient is choose(n,k), so one of its roots b satisfies
`distance(a,b)^k <= norm(choose(n,k))^-1 * r^k` and has degree at most k.
Galois isometry transfers the displacement bound to b. For n not a power
of p, Lucas supplies some 0 < k < n with unit binomial coefficient. For
n = p^(s+1), take k = p^s: the binomial valuation is one. Strong degree
induction with budget `2 - 2/n` gives the deliberately nonoptimal uniform
constant `p^2`. Every row is capped at 150 source lines; split
again before exceeding that limit. This is a plan until each lemma builds.

| Leaf | Concrete proof output | Dependency |
|---|---|---|
| UltrametricPolynomialCoefficients | Coefficients of products of linear factors with bounded roots have the corresponding power bound. | Ultrametric finite-sum inequality |
| PolynomialNearbyRoot | Small evaluation gives a nearby actual root, using the product of root distances. | Splitting in the algebraic closure |
| PadicHasseApproximation | The Hasse derivative of the original minimal polynomial supplies an actual smaller-degree approximant. | Previous two leaves, conjugacy, Hasse degree and leading coefficient |
| PadicBinomialDescent | Unit binomial coefficient off p-powers; valuation one for choose(p^(s+1),p^s). | Lucas and prime-power binomial factorization |
| AxDegreeBudget | Real-power budget inequalities and uniform upper bound. | Elementary ordered-field arithmetic |
| PadicAxDegreeStep | Combine actual Hasse roots, binomial losses and the real-power budget into a strict degree reduction. | Hasse approximation, binomial descent, degree budget |
| PadicAxEstimate | Strong degree induction with actual scalar witnesses and a uniform constant. | Hasse approximation, binomial descent, degree budget |
| ComplexAxFixedScalars | Discharge W33 hestimate and derive the completed fixed field. | PadicAxEstimate and ComplexAxDescent |
| CyclotomicTowerConstruction | Actual p-power-root subfields and inclusions. | Original character and roots of unity |
| CyclotomicDifferentBounds | Different estimates at finite tower levels. | Tower construction; split valuation computations separately |
| CyclotomicNormalizedTraceBounds | Uniform bounds for actual normalized trace transitions. | Different bounds |
| CyclotomicWeightedDescent | Descend completed weighted invariants along actual tower traces. | Trace bounds, W33 approximation |
| ComplexNonzeroTwistVanishing | Vanishing for every nonzero integral weight. | Weighted descent and character image |
| ComplexInvariantOrder | Invariant order zero and residue-scalar subtraction. | Both analytic endpoints and actual integer graded algebra |

The comparison split remains the W29/W32 contracts: rational-place
transport, cotangent transitions, tangent duality, actual pairing,
integrality, equivariance, injectivity, surjectivity, strictness, then
coefficient decomposition and both graded ranks. None is assumed as a
record field. The arithmetic and analytic leaves above take precedence.


### W34 cyclotomic arithmetic refinement (before implementation)

The Ax endpoint is separate from cyclotomic weighted descent. Before tower
trace estimates, split the local arithmetic into the following <=150-line
leaves: `PadicCyclotomicIrreducible` transports the integral Eisenstein
criterion to Z_p and proves irreducibility over Q_p;
`PadicCyclotomicTower` constructs the actual root-generated subfields,
their inclusions and finite-dimensional instances;
`PadicCyclotomicDegree` computes their degrees using the proved local
irreducibility; `PadicCyclotomicTrace` constructs actual normalized trace
projections and proves their finite-level compatibility. Trace operator
bounds still require separate different/valuation leaves; neither the
finite-dimensional instances nor formal trace transitivity proves them.


A further bounded leaf, `PadicCyclotomicRootNorm`, computes the norm of
zeta-1 from the actual minimal polynomial and the original isometric
Galois action. Coefficient control in that power basis and trace values
on root powers must then be separate leaves before a uniform trace bound.

`NormalizedTraceTower` is a separate <=150-line generic transitivity leaf:
proving it over abstract fields avoids expanding all p-adic field structures
inside the kernel when specializing to the actual cyclotomic tower.


### W34 implementation boundary

`padicAx_exists_scalar` proves the requested algebraic scalar estimate
with the element-independent constant `(p : Real)^2`. The proof chooses
an actual root of a Hasse derivative of the actual minimal polynomial,
then uses strong induction on its degree. A unit binomial coefficient
has no loss; at a p-power degree the loss is `p^(1/k)` and the exponent
budget `2-2/n` pays for it. No uniform estimate is a hypothesis of this
theorem. `complexGalois_fixed_iff_mem_range` consequently identifies the
fixed elements of the original C_p action with the original Q_p image;
`complexGalois_fixed_existsUnique_scalar` gives unique scalar descent.

`padic_cyclotomic_primePower_irreducible` proves local irreducibility by
transporting Eisenstein from Z to Z_p and applying Gauss over Q_p. The
actual root-generated tower is finite at each level, generated by any
primitive root there, has degree `p^s*(p-1)` at level s+1, and is strictly
increasing after its first level (including p=2). The original isometric
Galois action gives `padic_minpoly_eval_norm`; specialization computes
`norm(zeta-1)^(p^s*(p-1)) = p^-1`. The actual normalized traces fix their
target fields, are idempotent, agree with field trace divided by degree
on every finite subextension, and compose along tower inclusions.

These are arithmetic inputs, not a trace operator estimate. The remaining
analytic leaves, still <=150 source lines each, are:

1. Compute relative tower degrees and actual traces on root powers;
   prove coefficient control in the uniformizer power basis using the
   exact norm. Split the coefficient/orthogonality argument from the
   root-power trace computation.
2. Prove a uniform norm bound for normalized trace restricted to the
   cyclotomic union. The trace on the whole algebraic closure is not
   claimed uniformly bounded; that stronger assertion would be false.
3. Descend invariants of the cyclotomic-character kernel to the completed
   cyclotomic union (requires the relative Ax argument), extend the
   bounded projections, and prove convergence back to the vector.
4. Prove tail-character nontriviality and equivariance of the actual
   projections, then nonzero completed integral-twist vanishing.
5. Apply both analytic endpoints to actual integer graded pieces:
   invariant order, fixed-residue subtraction, and the reverse B_dR
   fixed-field inclusion. Continue the existing comparison split only
   after these gates.

The original general `IsHardlyRamified.mem_isCompatible` remains unchanged
and still depends on `sorryAx`; no general-family admission is discharged
by the fixed-C_p endpoint alone. Rebuild each named module, lint it alone,
and print its axioms to check these claims; the W34 handoff records the
checked snapshot and evidence logs.

## W35 cyclotomic trace split (before implementation)

Every new module below has a 150-line cap. Dependencies are proved from the
actual subfields, minimal polynomials and inherited norm; none of the
analytic conclusions is an input record field.

| Leaf | Concrete output | Dependencies |
|---|---|---|
| PadicCyclotomicRelativeDegree | Degree p^r from level n+1 to n+r+1; relative primitive-root degree. | W34 absolute degrees, tower law |
| PadicCyclotomicRelativeMinpoly | Relative minimal polynomial X^(p^r)-C(zeta^(p^r)). | Relative degree, root equation |
| PadicCyclotomicRootTrace | Normalized trace of primitive higher roots and arbitrary root powers. | Relative minimal polynomial, trace next coefficient |
| UltrametricDistinctTerms | A finite sum of terms with distinct nonzero norms dominates every term. | Ultrametric inequality |
| PadicUniformizerOrthogonality | Distinct norms for scalar multiples of successive uniformizer powers. | Discrete Q_p norms, W34 uniformizer norm |
| PadicCyclotomicCoefficientBound | Uniform bound on Q_p coefficients in the uniformizer power basis. | Orthogonality and actual power basis |
| PadicCyclotomicUniformTrace | Bound independent of source level on the cyclotomic union. | Root-power trace and coefficient bound |

After these leaves, split the relative Ax argument, completed union,
equivariant continuous projections and their convergence before proceeding
to nonzero twists and graded invariants. Those endpoints remain open until
their arithmetic and analytic hypotheses have actually been discharged.

W35 refinement: `UltrametricDistinctTerms` needs no new module: Mathlib's
`IsUltrametricDist.norm_sum_eq_sup'_of_pairwise_ne` supplies that leaf.
`PadicCyclotomicIntegralTrace` (cap 150) separates the trace bound for
integer polynomials in roots, and hence uniformizer powers, from the
coefficient argument and final operator estimate.

W35 relative Ax refinement (all caps 150): `PadicRelativeGalois` proves
integrality and isometry over any actual intermediate field;
`PadicRelativeHasseApproximation` repeats the actual Hasse-root construction
over that field, with the same Q_p binomial norm;
`PadicRelativeAxDegreeStep` applies the existing arithmetic budget;
`PadicRelativeAxEstimate` performs strong degree induction and yields a
uniform approximation by elements of the actual intermediate field.
This is the algebraic input for kernel descent, not an assumption of it.

W35 completion split (caps 150): `ComplexRelativeAxDescent` proves that
fixed vectors for all automorphisms over an actual intermediate field
belong to the closure of that field's actual image. `PadicCyclotomicKernel`
identifies the character kernel with automorphisms fixing the cyclotomic
union. `ComplexCyclotomicKernelDescent` specializes the proved relative
estimate and closure theorem to this kernel. Completed trace extensions,
equivariance and convergence are separate leaves after these.

W35 trace-extension split (caps 150): `ComplexCyclotomicClosure` realizes
the completed union as a closed subspace of the original C_p and proves
density of its algebraic union. `ComplexCyclotomicProjection` extends the
actual bounded traces to that space with the same uniform bound.
`ComplexCyclotomicProjectionConvergence` proves convergence to the original
vector by density, eventual stabilization on finite levels and the uniform
bound. Equivariance and finite-level range are separate arithmetic leaves.

W35 vanishing split (caps 150): `ComplexCyclotomicGalois` restricts the
original continuous linear action to the actual closure;
`ComplexCyclotomicTraceInvariant` proves invariance under automorphisms
fixing a target level by normalized-trace naturality and density.
`PadicCyclotomicTailAutomorphism` constructs automorphisms with prescribed
root action using the proved relative minimal polynomial;
`PadicCyclotomicTailCharacter` detects every nonzero integer weight at
every target level. `ComplexNonzeroTwistVanishing` combines these with
kernel descent and projection convergence. Actual graded-piece invariants
are a final separate leaf after this analytic endpoint.

W35 full-equivariance refinement (caps 150): `NormalizedTraceEquivariance`
proves normalized-trace naturality under compatible base and extension
field automorphisms from the minimal-polynomial formula.
`ComplexCyclotomicProjectionEquivariance` applies it to the actual normal
cyclotomic levels, then extends full Galois equivariance by density.
`ComplexIntegerGradedInvariants` proves nonzero-degree vanishing and unique
Q_p scalar coordinates in degree zero for the existing integer quotients.

### W35 implementation boundary

The W34 analytic gaps through integer graded-piece invariants are now
implemented in new modules. Recheck the named endpoints with foreground
module builds, individual module lint, and `#print axioms`; the W35 handoff
records the checked snapshot and logs.

- `padicCyclotomicProjection_union_norm_le` bounds every positive-level
  normalized projection on the actual algebraic union by `p * norm(x)`,
  independently of both source and target levels. Relative binomial minimal
  polynomials give the exact root-power trace formula. The exact norm of
  zeta-1 and the discrete Q_p value group prove orthogonality and the
  coefficient bound; integer-polynomial expansions finish the trace bound.
- `padicRelativeAx_exists_scalar` proves the uniform `p^2` approximation
  estimate over any actual intermediate field. It uses actual relative
  Hasse roots and relative automorphisms, with the original binomial budget.
  `complexCyclotomic_kernel_fixed_iff` identifies the original C_p kernel
  invariants with the actual closure of the cyclotomic union.
- `complexCyclotomicProjection` extends the actual traces to this closure;
  `complexCyclotomicProjection_norm_le`,
  `complexCyclotomicProjection_equivariant`, and
  `complexCyclotomicProjection_tendsto` prove the uniform bound, full Galois
  equivariance, and convergence to the original vector. Relative target
  automorphisms leave the corresponding projection unchanged.
- `padicCyclotomic_tail_character_zpow_ne_one` constructs a detector for
  every nonzero integer weight at every finite target level. Its prescribed
  root action has exponent `1+p^(n+1)`; sufficiently high finite residues
  distinguish each positive power from one. Negative weights follow in the
  units group. No character-surjectivity conclusion is assumed.
- `complexTwist_fixed_eq_zero` proves actual C_p twist-invariant vanishing
  for every nonzero integral weight. The actual integer graded quotient
  consequently has zero invariants away from degree zero, and unique
  original Q_p scalar coordinates at degree zero, in
  `ComplexIntegerGradedInvariants`.

Still downstream: invariant order zero in the original B_dR field,
fixed-residue scalar subtraction and the reverse B_dR fixed-field inclusion;
then the explicit comparison contracts, coefficient decomposition and both
graded ranks. The general family theorem is unchanged. These new analytic
and graded endpoints do not by themselves remove its `sorryAx` dependency.

## W36 invariant-order split (before implementation)

Each complete new module is capped at 150 lines. `ComplexInvariantOrder`
uses the DVR unit-times-integer-power decomposition in the original field,
passes its invariant representative to the actual graded quotient, and
uses the nonzero residue of a unit to force degree zero.
`ComplexFixedResidue` descends the resulting integral representative's
fixed residue to the original Q_p and subtracts that scalar; it proves
that a fixed integral element with zero residue must vanish.
`ComplexDeRhamFixedScalars` combines these proofs to identify the fixed
field with the image of the original Q_p embedding and proves uniqueness.
No fixed-field or comparison conclusion is added as an assumption.

W36 rational-place refinement (caps 150): `AlgebraicClosureGaloisTransport`
constructs conjugation of actual closure automorphisms along a base-field
isomorphism, with the commuting evaluation formula.
`PDivisibleRationalPlaceTransport` specializes the actual continuous field
and integer-ring identifications and their commuting square, and fixes one
compatible closure/Galois identification. `PDivisibleRationalTateAction`
uses this identification on the original system's coherent sequences and
proves evaluation equivariance; it does not replace those sequences with
an unrelated representation. Continuity and coordinate base transport
must be proved where used in the comparison construction.

W36 cotangent refinement (caps 150): `FiniteFlatCotangent` defines the
actual augmentation ideal modulo its square and induces maps from the
specified integral Hopf maps, proving identity, composition and
surjectivity for closed immersions. `PDivisibleCotangentTransitions`
specializes to both original level maps and proves their coherence and
multiplication factorizations. `PDivisibleCotangentLimit` constructs the
inverse limit along inclusions, with its actual projections and
functoriality. Finite-level cotangents are torsion: their integral linear
duals cannot be substituted for the tangent module of the p-divisible
group. Tangent/Cartier compatibility therefore remains a separate proof
obligation after these constructions.

W36 continuity refinement (cap 150): `AlgebraicClosureGaloisContinuity`
identifies the chosen conjugation with the continuous restriction map on
actual closures; compactness gives continuity of its same inverse.
The rational-place specialization and the action on the original Tate
module then retain their actual Krull and inverse-limit topologies.

W36 tangent refinement (caps 150): `AugmentationTangent` defines Leibniz
functionals with values in an arbitrary base module and proves descent
through the actual augmentation square. `AugmentationTangentEquiv`
identifies these functionals with linear maps from the actual cotangent
quotient. `CartierDualTangent` identifies scalar-valued tangent functionals
with primitive elements of the actual integral Cartier dual, using its
proved perfect coordinate pairing. These are finite-level algebraic
inputs; a p-divisible tangent/dual limit comparison and an actual period
pairing are further obligations, not consequences of giving these names.

W36 tangent naturality refinement (cap 150): `FiniteFlatTangentNaturality`
constructs precomposition by the original integral model map, proves
Leibniz and compatibility with the cotangent equivalence. The construction
retains arbitrary target modules, and so applies after taking torsion
coefficients. The Cartier identification is natural under the actual
transposed coordinate maps, rather than an independently chosen pairing.

W36 cotangent lifting refinement (cap 150):
`PDivisibleCotangentSurjective` constructs successive actual lifts of a
prescribed level cotangent and proves coherence at all ordered levels.
This proves each inverse-limit evaluation is surjective without imposing
finiteness of the underlying cotangent sets or assuming a limit-lifting
property. `FiniteFlatCartierTangent` specializes finite-level tangent and
Cartier naturality to the actual finite-flat models.

### W36 implementation boundary

The original period fixed-field endpoint now has unconditional entry points
`complexDeRham_fixed_unit_exponent_eq_zero`,
`complexDeRham_fixed_exists_unit`,
`complexDeRham_fixed_eq_residue_scalar`, and
`complexDeRham_fixed_iff_mem_range`. Nonzero field invariants have order
zero; subtracting their unique original Q_p residue scalar leaves a fixed
integral element with zero residue, which must vanish. Both B_dR and
B_dR+ have exactly the original Q_p image as their invariant elements.

The rational-place field and integer maps commute with their actual
inclusions. `rationalPlaceGaloisContinuousEquiv` uses one chosen compatible
closure map in both directions. `rationalTateAction` preserves the
original Tate module, with its original finite-level evaluations and
reductions, and is jointly continuous for its existing topology. No
unrelated representation or fresh finite-flat model replaces that system.

The actual augmentation cotangent quotients now have surjective inverse
transitions, coherent opposite pullbacks and both multiplication-morphism
factorizations. `cotangentLimit` is their actual inverse limit;
`cotangentEval_surjective` constructs compatible lifts of every level
cotangent. These facts do not yet identify the differential of
multiplication by n with scalar multiplication by n.

`augmentationTangentEquiv` represents tangent functionals with arbitrary
module coefficients by maps from the actual augmentation quotient.
`cotangentPrimitiveEquiv` identifies its scalar dual with primitive
elements of the actual integral Cartier dual. The finite-flat
specializations commute with the original integral morphisms and their
Cartier transposes. No interchange of inverse limits and duals, finite
freeness of the cotangent limit, or p-divisible tangent comparison is
asserted by these finite-level results.

Next bounded leaves before closing `PDivisibleTangentDuality`:

1. Prove the cotangent differential of convolution addition and of
   multiplication by n; specialize to the original p-power levels.
2. Prove the required integral cotangent-limit finiteness and reduction
   comparisons, then construct the corresponding tangent object. Split
   the needed formal-smoothness or deformation-theoretic input before
   implementation; it is not supplied by the inverse-limit definition.
3. Construct the Cartier-dual level/limit system and prove the required
   tangent/dual compatibility with those same integral identifications.
4. Construct the actual period pairing; prove integrality, equivariance,
   injectivity, surjectivity and filtration strictness in the existing
   comparison-contract order. Coefficient components, support,
   determinant compatibility and both graded ranks follow only after it.

All these are proof obligations. The general family theorem is unchanged;
the fixed-field and finite-level duality theorems do not remove its
`sorryAx`. Recheck every new module with its foreground module build,
individual lint and `#print axioms`; FAMILY_W36_DONE.md records the
checked snapshot and its local evidence files.

## W37 cotangent differential and limit split (before implementation)

Each complete module is capped at 150 lines. `AugmentationConvolution`
proves the Leibniz differential of convolution using the actual counit
identities. `FiniteFlatCotangentArithmetic` descends that identity to
original model cotangents, including zero and multiplication by n.
`PDivisibleCotangentArithmetic` computes both level composites as p-power
scalars and proves the actual level annihilators.

The limit comparison requires separate algebraic leaves before any
formal-smoothness assertion: identify the cotangent kernel of a closed
augmentation-preserving quotient; use the original system's integral
kernel equation to obtain the cotangent exact sequence; compare its image
with p-power multiples. Prove the inverse-limit reduction kernel using
compatible lifts, and finite generation over the complete DVR using
p-adic completeness and a finite generating set modulo p. Finite freeness
requires a further torsion-freeness or formal-smoothness theorem; neither
is implied by merely defining the inverse limit. A formal-smoothness route
must prove infinitesimal lifting from the original finite-flat exact
system, then establish the associated complete formally smooth coordinate
algebra and its finite free cotangent. These are separate capped proof
obligations, not extra fields of `PDivisibleSystem`.

The actual Cartier-dual limit compatibility and period pairing follow
these gates, in the previously recorded integrality, equivariance,
injectivity, surjectivity and strictness order.

W37 further refinement (caps 150): `FiniteFlatCotangentKernel` supplies
actual coordinate-kernel representatives; `FiniteFlatCotangentImage`
linearizes the extended augmentation ideal; `PDivisibleCotangentExactness`
uses these to identify restriction kernels with p-power multiples.
`FiniteFlatCotangentFinite` proves finite generation at each finite level;
`FiniteTorsionModule` and `PDivisibleCotangentFiniteSets` prove those sets
are finite over the original rational-place base. `PDivisibleCotangentLimitReduction`
uses finite compatible division fibres to identify the limit modulo p^m
with its actual level m, retaining the original evaluation map.

Finite generation of the limit splits further into nilpotent scalar
lifting of generators, continuity of finite-level scalar evaluation,
and a compact coefficient-fibre argument over Z_p transported by the
proved original integer-ring equivalence. This route proves finite
generation only; freeness and the formal-smoothness input remain distinct.

W37 final refinement (caps 150): `NilpotentGeneratorLifting` proves
surjectivity from generators modulo a nilpotent scalar;
`PDivisibleCotangentGenerators` lifts one finite family from level one
and proves that it generates every actual level. `PadicTorsionScalarContinuity`
factors the original scalar action through actual p-power residues.
`PDivisibleCotangentLimitFinite` uses compact nonempty coefficient fibres
in a finite power of Z_p to obtain generators of the actual inverse limit.
`PDivisibleCotangentComplete` identifies the evaluation kernels with the
standard adic filtration and constructs limits of coherent Cauchy sequences.
`PDivisibleTangentReduction` represents torsion-valued limit functionals
by the original finite-level Leibniz functionals;
`PDivisibleTangentNaturality` retains original system morphisms.
`PDivisibleIntegralTangent` defines the integral linear dual of the limit
and proves it finite free over the original DVR.
`PDivisibleRationalCotangent` specializes reduction, completeness and
integral tangent finiteness/freeness to the original rational-place base.

### W37 implementation boundary and next proof obligations

The new modules prove convolution and multiplication differentials,
p-power annihilators, the exact finite-level cotangent sequence, finite
level sets, limit reduction and finite generation, and adic completeness.
All identifications retain the original integral coordinate maps and
original level evaluations. The integral tangent constructed here is
`Hom_R(cotangentLimit,R)`. Its freeness is a property of this dual over a
DVR, and does not prove that `cotangentLimit` is free. The torsion-valued
comparison is `Hom_R(cotangentLimit,M) = Hom_R(LevelCotangent n,M)` when
p^n kills M; it does not assert that reducing the integral dual gives
all such functionals.

The next unproved gate needs its own source proof and the following
separate capped leaves before period comparison:

1. Establish infinitesimal lifting for the connected formal object
   associated to the original finite-flat p-divisible levels. A proof
   must construct the formal object or state and prove an equivalent
   level-system lifting theorem; the required lifting property may not
   be supplied as a new field of the input system.
2. Deduce torsion-freeness and finite freeness of the actual cotangent
   limit, identifying it with the cotangent of that same formal object.
   The currently proved finiteness and completeness do not imply this.
3. Prove reduction of its integral dual equals the already constructed
   torsion-valued tangent functor, with the original evaluation pairing.
4. Construct the Cartier-dual level system and its limit transition maps;
   identify its relevant tangent/dual data using those same maps. The
   scalar-valued finite-level primitive equivalence is not a limit theorem.
5. Construct the period pairing and prove integrality, equivariance,
   injectivity, surjectivity and strictness in the existing D2 contract
   order. No new code in this wave proves these endpoints.

Checked by the per-module foreground builds, individual lints and named
axiom audits recorded in `FAMILY_W37_DONE.md`; rerun those commands for a
current status. The unchanged general family theorem remains outside
these cotangent/tangent results and still requires admission removal.

## W38 infinitesimal lifting split (committed before implementation)

Every leaf below has a 150-line complete-module cap. The first target is
an actual lifting theorem, retaining the original coordinate algebra:
for a square-zero ideal J in a test R-algebra B, with N J = 0, every
B/J-valued point x of a finite-flat level has a B-valued lift of [N]x.
Lift x R-linearly using projectivity and take its N-th convolution power.
The multiplicativity defect disappears by the square-zero binomial formula.
This theorem lifts multiplication of points; it is **not** formal smoothness
of the level, nor lifting of x itself into a higher level.

| Leaf / proposed module | Proof obligation | Cap |
|---|---|---:|
| S1 / SquareZeroConvolution | Congruent linear maps have equal N-th convolution powers when J² = 0 and N J = 0. | 150 |
| S2 / ConvolutionTensorPower | Precomposition with multiplication and tensor-square followed by multiplication commute with convolution powers. | 150 |
| S3 / SquareZeroConvolutionLift | The convolution power of an arbitrary linear lift is an actual algebra map. | 150 |
| S4 / FiniteFlatSquareZeroLifting | Obtain linear lifts from the original finite-free coordinate module; prove the quotient identity with the original multiplication morphism. | 150 |
| S5 / PDivisibleSquareZeroLifting | Specialize to the original p-power levels, preserving their original maps. | 150 |

The remaining geometric gate needs separate proofs, not an input lifting
field: (S6) construct the connected formal functor or actual level-colimit
functor; (S7) prove that every point across a square-zero thickening lifts
at some higher original level, using the finite-flat exactness and
p-divisibility; (S8) pass from square-zero to nilpotent thickenings.
S7 is large missing theory: S1–S5 alone lift [N]x, and division in an fppf
sheaf does not itself produce a section over B or a lift of x. No such
surjectivity is to be inferred from the binomial calculation.

After this gate: identify the formal cotangent with the existing inverse
limit, prove torsion-freeness and finite freeness, and prove that reducing
the integral dual gives all torsion-valued tangents with the same pairing.
Then construct the actual Cartier-dual level/limit comparison and period
pairing, in the existing integrality/equivariance/injectivity/surjectivity/
strictness order. These remain distinct proof obligations; none is to be
assumed as a record field or inferred from finite generation alone.

W38 refinement before further implementation (cap 150):
`SquareZeroPointLift` makes the S4 construction canonical: two linear lifts
of the same point have identical convolution powers, and an existing
algebra lift is sent to its original N-th power. It retains the exact
quotient map. This independence result is needed for future descent; it
does not assert that a division point or a descent datum exists.

W38 naturality refinement (cap 150): `SquareZeroLiftNaturality` proves
compatibility of the canonical lift with actual bialgebra source maps and
commuting maps of square-zero test-algebra thickenings. The convolution
precomposition identity is a separate lemma in `ConvolutionTensorPower`,
still within its cap. These are equalities of the constructed points, not
new coherence hypotheses on a p-divisible system.

### W38 implementation boundary

`FF.exists_multiply_lift` and `PDivisibleSystem.exists_pow_point_lift`
construct actual algebra-valued lifts of multiplication. Both ordered
transition composites have corresponding lifting theorems using the
system's specified inclusion and reduction maps. `squareZeroPointLift`
is independent of all linear-lift choices, reduces to the original
convolution power, agrees with the N-th power of any existing algebra
lift, and commutes with source bialgebra morphisms and maps of test-algebra
thickenings. No replacement integral model is chosen.

The full infinitesimal-surjectivity gate remains open. A geometric route
must construct local division points across a lifted flat cover and then
descend their lifts. Merely knowing fppf-local divisibility on the quotient
does not provide that cover or a descended point. Identifying differences
of local lifts with a quasi-coherent infinitesimal kernel and proving its
descent on affine test schemes are additional mathematical obligations.
These require separate capped source proofs before implementation.

Accordingly, this wave does not identify a formally smooth object's
cotangent, prove cotangent-limit torsion-freeness, prove reduction of the
integral dual, or construct the Cartier-dual limit/period pairing. S1–S5
are prerequisites for S7, not a proof of S7. The admission-removal target
is unchanged. Validation commands, checked time, and explicit remaining
obligations are recorded in the untracked `FAMILY_W38_DONE.md`; per-module
builds, individual lints, and named axiom audits must be rerun to refresh
its snapshot.

## W39 source-matched formal-functor lifting split

The exact target is: for a surjective test-algebra map q : B → C with
square-zero kernel J killed by p^r, every x : A_n → C has some m ≥ n
and y : A_m → B with q ∘ y = x ∘ inclusion(n,m). Here A_n is the
original coordinate ring. On nilpotent p-test algebras such an r exists.
Neither same-level multiplication lifting nor a local division point
alone proves this target. The following leaves use the indicated actual
source APIs; every proposed complete module has a 150-line cap.

| Leaf / module | Source and proof, retaining original maps | Readiness |
|---|---|---|
| L1 / PDivisiblePointColimit | `PDivisibleSystem.inclusion_refl`, `inclusion_comp`, `closed`; Mathlib `Order.DirectedInverseSystem.DirectLimit`. Form the pointwise filtered colimit of A_n-valued points with the specified inclusions; construct test-algebra maps and identity/composition laws. | Ready. This is a functor of sets, not a claim of fppf sheafification or connected representability. |
| L2 / PDivisibleColimitLifting | `DirectLimit.setoid`, representative induction. Prove that surjectivity on this colimit is equivalent to the exact higher-level lifting target above. Move both representatives to their common comparison level. | Ready; a criterion, not a proof of its sides. |
| L3 / SquareZeroAugmentationPoints | `AlgHom.augmentationTangent`, `augmentationTangentEquiv`; the square-zero product identity. Identify points reducing to the actual augmentation with tangent functionals valued in J by f ↦ f−ε and d ↦ ε+d. | Ready; applies to the actual infinitesimal kernel at every original level. |
| L4 / SquareZeroPointDifference | Actual Hopf convolution inverse and `AlgHom.comp_convMul_distrib`; translate two local lifts with equal reduction to an augmentation point. Identify that difference using L3, not the coordinatewise difference at an arbitrary point. | Ready after L3. |
| L5 / FaithfullyFlatPointDescent | Mathlib `Algebra.IsEffective.of_faithfullyFlat` in `RingTheory.TensorProduct.IncludeLeftSubRight`. Descend each coordinate of a point whose two pullbacks agree, and prove the resulting map is an algebra map by injectivity. | Ready; proves effective descent of an existing datum, not existence of that datum. |
| L6a / DivisionCover | Base-change the system's original faithfully flat reduction along x to obtain a cover of Spec C with the tautological division point. | Requires explicit tensor-base-change/point comparison; finite-level exactness alone is not a lifted cover of Spec B. |
| L6b / LiftedDivisionCover | Construct a faithfully flat B-algebra D whose reduction supports the specified division point. A flat C-algebra need not have a given flat B-lift for free; prove the needed local presentation/deformation result. | Large missing theory: no source theorem in the current import closure supplies this existence. Split its presentation and obstruction proofs before implementation. |
| L7a / LocalLiftDifferenceCocycle | On D⊗_B D use L4 to identify the discrepancy of local lifts with actual J-valued tangents and prove the triple-overlap cocycle equation, compatible with original inclusions. | Depends on L6b and a comparison of kernels under flat base change. |
| L7b / InfinitesimalCocycleCorrection | Prove affine faithfully flat degree-one exactness for that quasi-coherent kernel; construct a correction killing the discrepancy at a common finite level. | Large missing theory: L5 is degree-zero equalizer exactness only; it does not kill a cocycle. No correction is assumed as a record field. |
| L8 / PDivisibleFormalLifting | Correct the actual local points, descend with L5, retain q∘y=x∘inclusion, and use L2. | Blocked on L6b and L7b; W38's canonical lift does not bypass either. |
| L9 / NilpotentFormalLifting | Factor a nilpotent thickening into square-zero quotients and compose the finite-level lifts, keeping ordered inclusion maps. | Blocked on L8. |

This is the algebraic source-level expansion of the geometric route
recorded in W38, not a claim that a cited general p-divisible-group
smoothness theorem has already been formalized. In particular, L6b and
L7b are explicitly unproved mathematical inputs, not permitted hypotheses
of the final smoothness theorem. A different proof that avoids either
must be split and source-checked before replacing this route.

After L8/L9, the connected formal object's representability and its
cotangent identification with `cotangentLimit` still need separate proofs.
Then prove torsion-freeness, finite freeness, integral-dual reduction,
Cartier-dual limit compatibility, and period pairing in the existing D2
order. A pointwise colimit definition or a finite-level kernel equivalence
does not establish any of those claims or remove the family admission.

### W39 implementation boundary

L1–L5 and L6a now have capped modules. `PDivisiblePointColimit` constructs
the functor with injective original level maps. `PDivisibleColimitLifting`
proves the exact higher-level lifting criterion, without asserting
surjectivity. `SquareZeroAugmentationPoints` identifies the actual kernel
of reduction with J-valued tangents and hence with maps from the original
augmentation cotangent quotient. `SquareZeroPointDifference` translates
equal-reduction points using the original antipode, proves recovery and
the group cocycle identity, and identifies that discrepancy with a tangent.
It does not establish the flat-base-change or quasi-coherent comparisons
required in L7a/L7b.

`FaithfullyFlatPointDescent` constructs the unique affine algebra point
from equal overlap pullbacks and proves that a prescribed reduction can
be checked after an injective comparison. `PDivisibleDivisionCover`
constructs the actual tensor-product cover of C carrying a division point
for the specified reduction. It proves faithful flatness, without claiming
that this cover lifts to B or that it is finitely presented.

L6b (a lifted division cover) and L7b (affine infinitesimal cocycle
correction, with flat-base-change and finite-stage compatibility) remain
large missing theory. L8/L9, connected formal representability, cotangent
limit identification/freeness, integral-dual reduction and all period
comparison gates remain open. No new premise or record field supplies
any of these conclusions. The family admission is unchanged.

Validation is reproducible through `W39_FINAL_CHECKS.py` and the commands
in untracked `FAMILY_W39_DONE.md`; that report carries the checked time,
local commits and evidence. New modules are built in the foreground,
linted individually, and all named declarations receive an axiom audit.

## W40 cover-deformation and infinitesimal-descent split

Source check: Mathlib revision `c32e1ec0d1eb5237ba344eee50162f45d5b0fc76`.
Every row is a complete new module capped at 150 lines. Ready rows are
implemented in table order; dependencies still missing are stated explicitly.
No row supplies formal smoothness or a correcting cochain as an input field.

| Leaf / module | Exact obligation and source match | Readiness / dependencies | Cap |
|---|---|---|---:|
| L6b.1 / MonicCoverLifting | Lift a positive-degree monic polynomial through a surjection, retaining its degree; its root algebra is a faithfully flat finite free cover and maps to the original root algebra. Mathlib `Polynomial.lifts_and_natDegree_eq_and_monic`, `Monic.free_adjoinRoot`, `AdjoinRoot.mapAlgHom`. | Ready. This is a monic local-presentation case, not a presentation theorem for the division cover. | 150 |
| L6b.2 / DivisionCoverPresentation | Refine the actual L6a cover by local presentations whose equations admit flat lifts; retain the map from the original division algebra and jointly surjective charts. | Missing mathematical proof. Arbitrary finite-flat algebras cannot simply be declared liftable. Monic presentations from L6b.1 cannot be assumed for L6a. | 150 |
| L6b.3 / DivisionCoverDeformation | Lift each chosen presentation, prove flatness via its relation criterion and lift the covering condition across the nilpotent ideal. | Depends on L6b.2; Mathlib smooth lifting requires an already formally smooth source and does not establish this obligation. | 150 |
| L6b.4 / LiftedDivisionCover | Assemble the lifted charts into a faithfully flat B-cover and identify its reduction with a refinement supporting the original division point. | Depends on L6b.2–3; retain all quotient and division maps. | 150 |
| L7a.1 / FlatReductionKernel | Identify the kernel of the actual tensor algebra map with the tensor of the original reduction kernel, including evaluation on pure tensors. Mathlib `LinearMap.tensorKerEquiv` in `Flat.Equalizer`. | Ready independently of L6b. | 150 |
| L7a.2 / SquareZeroReductionBaseChange | Prove surjectivity, square-zero kernel and annihilator preservation for the actual base-changed reduction. Mathlib `Algebra.TensorProduct.lTensor_ker`, `Ideal.map_pow`, tensor map surjectivity. | Ready after L7a.1; uses the actual ring map, not an abstract replacement module. | 150 |
| L7a.3 / AugmentationKernelNaturality | Construct maps on the actual reduction kernels and augmentation points for a commuting square; prove tangent extraction and reconstruction commute pointwise. | Ready after the W39 kernel equivalence; does not assert Hom/tensor commutation. | 150 |
| L7a.4 / InfinitesimalConvolutionAddition | Show convolution of augmentation points corresponds to addition of tangents using square-zero products and the counit identities. | Separate tensor-induction proof; needed before transporting the group cocycle to an additive one. | 150 |
| L7a.5 / InfinitesimalKernelQuasiCoherent | Identify the colimit kernel with a tensor module, respecting base change, original inclusions and the actual cotangent pairing. | Requires a justified Hom/base-change argument; finite-level cotangent modules are not assumed projective. L7a.1 alone does not prove this. | 150 |
| L7b.1 / AmitsurDegreeOneMaps | Define the two alternating coface maps on module-valued double/triple tensors and prove their composite is zero. | Ready source algebra: tensor universal property and associativity. | 150 |
| L7b.2 / AmitsurSplitContraction | Given a linear retraction of the unit, contract a degree-one cocycle by evaluating its first tensor factor; prove the correcting coboundary identity. | Depends on L7b.1. The retraction will come from multiplication after base change, not be assumed on a general cover. | 150 |
| L7b.3 / AmitsurFaithfullyFlatExact | Tensor the complex with the cover, use multiplication to contract it, and reflect exactness. Mathlib `Module.FaithfullyFlat.lTensor_reflects_exact`. | Depends on L7b.1–2 and explicit associativity comparisons. The degree-zero `IsEffective` theorem does not suffice. | 150 |
| L7b.4 / InfinitesimalFiniteStageCorrection | Apply degree-one exactness to the actual discrepancy; represent the resulting colimit correction and all equalities at a common original finite level. | Depends on L6b.4, L7a.4–5, L7b.3 and the original directed-colimit equality criterion. | 150 |

Mathlib `Smooth.Basic` (`FormallySmooth.exists_lift`,
`FormallySmooth.iff_comp_surjective`) assumes the formal smoothness that
this gate seeks to prove. `Smooth.Quotient` lifts smoothness of an already
flat algebra across a thickening; it does not construct that flat algebra.
`Flat.FaithfullyFlat.Descent` reflects injectivity/surjectivity, and
`TensorProduct.IncludeLeftSubRight` proves degree-zero exactness only.
The Cech files found under `CategoryTheory.Sites.SheafCohomology` and
`AlgebraicTopology` do not directly supply this affine module-valued
Amitsur degree-one calculation. These are API matches and explicit gaps,
not a citation to an unverified general smoothness theorem.

L8/L9 and all W39 cotangent/period-comparison gates remain downstream.

W40 refinement before L7b.2–3 implementation: use the multiplication
contraction directly on the complex after tensoring with S. Its map
`S ⊗ (S ⊗ M) → S ⊗ M` multiplies the first two factors. Thus the
`AmitsurSplitContraction` leaf proves this explicit base-changed homotopy,
without introducing a hypothetical linear retraction of S → R. The
`AmitsurFaithfullyFlatExact` leaf then reflects exactness. This avoids a
separate change-of-base-ring identification and keeps both caps at 150.

### W40 implementation boundary

L6b.1, L7a.1–4 and L7b.1–3 are implemented in the eight named modules.
The monic-cover theorem constructs a finite free faithfully flat root
algebra over B with the original root and coefficient comparison to C.
It does not turn L6a's division cover into a monic presentation, or assert
that an arbitrary flat cover lifts.

The base-change comparison identifies the actual tensor algebra kernel,
with its pure-tensor formula. Surjectivity and the square-zero property
survive arbitrary base change; the kernel comparison and annihilator
transport use flatness. Tangent extraction/reconstruction commute with
actual maps of thickenings, and convolution becomes addition on the
actual augmentation kernel. These statements do not commute Hom with
tensor for a nonprojective cotangent module.

The Amitsur modules prove degree-one exactness for every module M and
every faithfully flat R-algebra S, with explicit double/triple tensor
maps and a multiplication contraction after base change. In particular,
each cocycle in S tensor S tensor M has an actual correcting cochain in
S tensor M. No quasi-coherence or correction-existence hypothesis is
hidden in a record. This removes the abstract affine degree-one
exactness gap, but does not identify the original colimit point kernel
with such a tensor module or put its correction at an original finite
level.

Remaining in order: L6b.2–4 (presentation/refinement, deformation and
assembly of the lifted division cover), L7a.5 (the actual quasi-coherent
kernel identification), L7b.4 (original finite-stage correction), L8/L9,
and the previously listed formal-cotangent and period-comparison gates.
The family admission is unchanged. Reproduce the validation via
`W40_MODULES.txt`, individual build/lint commands, `W40_AXIOMS.lean`,
`W40_BOUNDARY_AXIOMS.lean` and `W40_FINAL_CHECKS.py`; the untracked
`FAMILY_W40_DONE.md` records the checked time and exact local commits.

## W41 refinement: flat tensoring of actual tangent relations

The L6b.2 presentation theorem is still absent: finite flatness of the
original cover does not exhibit liftable equations. No flat deformation
or formal smoothness is inferred from the monic special case.

For L7a.5, nonprojectivity of the cotangent is not by itself an obstruction.
Use the original finite free coordinate algebra A. The Leibniz relation
map A tensor A -> A sends a tensor b to ab - epsilon(a)b - epsilon(b)a.
Its precomposition kernel is exactly the module of augmentation tangents.
Both coordinate sources are finite projective, so Mathlib
`TensorProduct.lTensorHomEquivHomLTensor` applies to their Hom modules;
`LinearMap.tensorKerEquiv` then commutes this kernel with flat tensoring.
This proves a canonical finite-level comparison without asserting that
the cotangent quotient is projective. The original cotangent pairing
must be retained by an evaluation lemma.

| Leaf | Obligation | Cap |
|---|---|---:|
| L7a.5a / FlatTensorHomKernel | Flat tensor comparison for kernels of precomposition between Hom modules with finite projective sources; pure-tensor evaluation. | 150 |
| L7a.5b / AugmentationTangentRelations | Original Leibniz relation map and its exact tangent-kernel identification. | 150 |
| L7a.5c / FlatAugmentationTangent | Combine the two comparisons and preserve the original cotangent pairing and source maps. | 150 |

The comparison is initially over the same base ring. For a cover of a
test algebra B, the required specialization uses B tensor_R A and its
augmentation to B. Passage through the original directed colimit,
overlap transport and finite-stage correction remain separate obligations.
These leaves do not supply L6b or assemble formal smoothness.

W41 additional source refinement: `cotangentRestriction_ker_scalar` already
identifies the kernel of restriction to level r with p^r multiples. Thus
for coefficients killed by p^r, precomposition with restriction is an
isomorphism at every level >= r. This uses only the original finite-level
exactness, not finiteness of the underlying cotangent sets or an inverse
limit argument. Split into `PDivisibleTangentStabilization` (150), original
augmentation-kernel inclusion compatibility (150), and identification of
the actual colimit augmentation kernel with level-r tangents (150).

The stage/colimit leaves are named `PDivisibleInfinitesimalStages` and
`PDivisibleInfinitesimalColimit`. The latter must prove bijectivity of the
map from the actual level-r kernel into the actual point-colimit kernel;
it cannot define a substitute colimit or assume representative existence.

L6b.2 splits further: `FinitePresentationPointCover` (150) proves the
actual tensor division cover is finite and finitely presented, using the
finite free original coordinates, restriction of finite presentation and
base change (`Finiteness.ModuleFinitePresentation`, `FiniteStability`).
This is not yet a liftable local presentation: a finite set of arbitrary
relations does not prove flatness of their lifts. The regular-sequence or
other liftable refinement remains the next geometric obligation.

L7b.4 also separates transport from existence: `InfinitesimalTangentCocycle`
(150) converts the actual group discrepancy cocycle into an additive
identity of original kernel-valued tangents. `CotangentAmitsurComparison`
(150) transports the tensor differentials through the proved finite-level
cotangent comparison; `CotangentAmitsurExact` (150) constructs a correcting
cotangent functional from that cocycle. Specializing to a flat cover of B
still needs the relative B-linear comparison and the actual overlap maps.

To address the test-algebra base precisely, add `RelativeHomRelations`
(150): the tensor/Hom adjunction identifies R-linear relation functionals
with B-linear functionals on B tensor_R coordinates. Then
`RelativeFlatHomKernel` (150) applies flat kernel comparison over B to
that finite free presentation. `RelativeFlatCotangent` (150) specializes
to the original augmentation relation and cotangent pairing. No flatness
of B over R is required: only the actual cover S over B is flat.

`FlatCoverReductionKernel` (150) removes the redundant tensor-with-B
factor from the reduction kernel: for the actual cover D over B, identify
D tensor_B ker(B -> C) with ker(D -> D tensor_B C). This is needed to
apply the relative cotangent comparison to actual test-algebra points,
rather than points of an isomorphic but unrecorded algebra.

`FlatCoverSquareZero` (150) transports the square-zero condition and its
p-power annihilator to the actual cover reduction. Then
`PDivisibleInfinitesimalFlatCover` (150) identifies the actual colimit
kernel over D with D tensor_B Hom_R(original level-r cotangent, J), and
records the original pairing. This is the required coefficient base B,
with no assumption that B or D is flat over R.

Final W41 refinement: the Amitsur comparison and correction leaves use
B throughout, via `relativeFlatCotangentHomEquiv`, rather than assuming
flatness over R. `RelativeCotangentNaturality` (150) retains original
cotangent transitions and maps of flat B-covers. Finally,
`PDivisibleInfinitesimalCorrection` (150) converts a cotangent cocycle into
an actual augmentation point of the specified original level r on D;
its original cotangent functional is a correcting cochain. The cocycle
condition remains a mathematical input about the supplied discrepancy,
not an assumption that a correction exists. The outstanding application
must form that discrepancy from actual local division lifts and identify
its three overlap pullbacks with these differentials.

### W41 implementation boundary

The new leaves prove finite presentation of the actual division cover,
but do not give it a liftable refinement. L6b.2's remaining presentation
argument and L6b.3–4 are still open. In particular no lifted flat B-cover
or formal-smoothness theorem has been constructed.

The infinitesimal representation has advanced beyond W40. Kernel-valued
tangents killed by p^r stabilize at original level r, using the existing
finite-level cotangent exactness. The actual point-colimit augmentation
kernel is equivalent to that original level kernel. On any flat B-cover
D its actual reduction kernel is D tensor_B J, and the actual colimit
infinitesimal kernel is D tensor_B Hom_R(Cotangent_r, J). The equivalence
retains the original cotangent pairing. Source inclusions, cotangent
transitions and maps of flat covers have their explicit comparison
lemmas. No projectivity of Cotangent_r, flatness of B over R, or finiteness
of the underlying cotangent sets is assumed.

For descent, actual equal-reduction point differences satisfy an additive
tangent/cotangent cocycle identity. The relative cotangent comparison
intertwines the first two Amitsur differentials over B. Every such
cotangent cocycle has a correcting cochain, and
`exists_original_infinitesimal_correction` represents that cochain by an
actual augmentation point at the specified original level r on D.

The remaining L7b.4 application must still start with actual local
inclusion lifts, form their double/triple-overlap discrepancy, and prove
that its pullbacks match the displayed relative Amitsur maps. It must
then correct those original local points and descend them. The additive
cocycle identity and the correction theorem are not themselves that
application. L8/L9, the connected formal object and its cotangent, and
all earlier period-comparison gates remain open. The family admission
has not been edited or removed.

Reproduce the source/object, cap, per-module build/lint and named-axiom
checks with `W41_FINAL_CHECKS.py`; `FAMILY_W41_DONE.md` records the checked
snapshot and local commits. These artifacts remain untracked outside FLT/.

## W42: source proof for the lifted-presentation gate

The relevant source is Stacks **00T0** (lifting syntomic algebras), with
**00SY** (local relative complete-intersection presentations), **00ST**
(localizing a lifted presentation) and **00SW** (relative global complete
intersections are syntomic). The statements and proofs were checked in
`algebra.tex` of stacks/stacks-project on 2026-10-04. These are source
proofs to formalize, not available Lean theorems.

For a syntomic C-algebra E, 00SY gives finitely many principal charts
E[1/s_i] presented as relative complete intersections. Lift their finitely
many equations to B and form D_i. The reduction of D_i is the specified
chart, by the quotient universal property, without any flatness assertion.
00ST localizes D_i at an element reducing to 1 to make it a relative
complete intersection; 00SW proves flatness. If ker(B -> C) is nilpotent,
every B-prime comes from a C-prime; hence the jointly surjective reduced
charts are still jointly surjective over B. A finite product of the flat
D_i is then faithfully flat. The chart identifications transport the
*specified* map from the original division algebra to this reduction.

The unresolved premise is that the actual division cover is syntomic.
It is a torsor under a finite flat kernel group, so a route is to trivialize
geometric fibres, use finite group-scheme complete-intersection structure,
and descend the fibre property. `HopfAlgebra.exists_minimal_square_presentation`
is a starting theorem only for a **local Hopf algebra over a perfect field
of positive characteristic**. It does not prove the torsor statement,
the regular-sequence property, characteristic-zero fibres, or descent of
complete-intersection fibres. None of these may be inferred from finite
presentation or from the existence of equally many generators and relations.
A general fppf-to-syntomic refinement is not asserted here.

Every implementation leaf below has a 150-line whole-module cap. The
large leaves must be further split before implementation if that cap
cannot be met; the table does not declare unproved source lemmas ready.

| Leaf / proposed module | Exact obligation and source | State before implementation |
|---|---|---|
| L6b.2b.i / DivisionTorsorFibres | Identify each geometric fibre of the actual reduction pullback with its original kernel group after choosing a point; retain the action and coordinate maps. | Missing group/torsor theory. |
| L6b.2b.ii / FiniteHopfFibreCI | Extend the existing local perfect-field square-presentation theorem to geometric fibres, and prove regularity of their relations. | Missing fibre decomposition and commutative algebra. |
| L6b.2b.iii / DivisionSyntomicCharts | Descend the fibre property and extract a finite unit-ideal family of relative CI presentations (00SY). | Missing syntomic and relative CI APIs; depends on i–ii. |
| L6b.3a / LiftedPresentationReduction | Lift the equations of a specified finite presentation through a coefficient surjection; construct its quotient map and compute its kernel. | Ready: `MvPolynomial.map_surjective`, ideal map/comap and quotient APIs. No flatness conclusion. |
| L6b.3b / LiftedPresentationBaseChange | Identify the actual reduction of the lifted quotient with the original presented algebra, retaining polynomial representatives and the original point. | Ready after 3a; quotient and tensor universal properties. |
| L6b.3c / RelativeCIDeformation | Prove the fibre-dimension/regular-sequence flatness theorem, then the localization step of 00ST/00SW. | Large missing theory; flatness is to be proved, not put in a presentation record. |
| L6b.4a / NilpotentCovering | Prove surjectivity on spectra across a nilpotent quotient and lift faithful covering in a commuting square once flatness is proved. | Ready: prime map/comap and `FaithfullyFlat.of_comap_surjective`. |
| L6b.4b / LiftedChartCover | Assemble finitely many flat lifted charts and transfer the actual division point to their reduction. | Product flatness and chart assembly after 2b.iii/3c. |
| L7b.4 / OriginalOverlapAssembly | Instantiate W41's original kernel/cotangent equivalences on these double/triple overlaps and apply its original correction. | Blocked on an actual flat lifted cover. |
| L8–9 / OriginalFormalSmoothness | Descend corrected local lifts and iterate along a nilpotent filtration. | Blocked on the preceding construction; family admission unchanged. |

This split is committed before the implementation. In particular a
conditional covering lemma must not be reported as existence of flat
lifts, and a lifted quotient presentation must not be reported as a
relative complete intersection.

W42 implementation subdivision (all caps 150): 3a uses
`PolynomialCoefficientKernel`, `LiftedQuotientReduction`, and
`LiftedPresentationReduction`; 3b uses `SurjectiveReductionBaseChange` and
`LiftedPresentationBaseChange`; 4a–b use `NilpotentCovering` and
`LiftedChartCover`. In the last module every individual chart's flatness
is still an input; joint covering of the product is proved. The point
transport theorem is over the original coefficient ring R, not B, since
original coordinate rings need not be B-algebras.

For nilpotent coefficient kernels the element reducing to 1 in 00ST is
already a unit. Thus this special case can avoid the open-locus step by
proving invariance of fibres under the nilpotent quotient and applying
00SW directly. **00SW remains unimplemented.** The current Mathlib has
regular-local-ring definitions and stability under polynomials, but no
Cohen–Macaulay or syntomic API giving this relative flatness result. For
p-nilpotent test algebras only characteristic-p geometric fibres occur;
a characteristic-zero branch is needed only for the more general claim.
The first unresolved mathematical gate is still 2b.i–iii, followed by
3c's relative-CI flatness theorem. These are substantial missing theory,
not an external authorization issue or a missing typeclass instance.

The source dependency behind 3c is not just 00SW's short statement:
00SV proves regularity and flatness of successive relation quotients;
its Noetherian case uses the fibrewise regular-sequence flatness criterion,
and its arbitrary-base case uses 00SU's Noetherian approximation followed
by filtered-colimit exactness and flatness. The present tests B,C are
arbitrary algebras, so silently adding Noetherian hypotheses would not
close the target. A next wave must split this dependency itself into
proof-sized leaves before attempting 3c; W42 does not call it implemented.

Checked implementation boundary: the seven W42 modules prove 3a, 3b,
and the conditional covering/finite-product part of 4a–b. Each is below
150 lines; individual build/lint and complete named axiom audits are in
the untracked W42 validation artifacts. They do not supply 2b's charts,
3c's flatness, the point on a *faithfully flat* lifted cover, the original
overlap application, or formal smoothness. The existing family admission
is untouched. See `FAMILY_W42_DONE.md` for the checked commit and evidence.

## W43: proof-sized split of torsor fibres and relative-CI flatness

This split uses the pinned Mathlib sources, checked 2026-10-04:
`Regular.RegularSequence`, `Regular.Flat`, `Flat.EquationalCriterion`,
`Algebra.Colimit.Module`, and `TensorProduct.Maps`. Every implementation
module below has a **150-line whole-file cap**. “Ready” means the proof can
be built from those APIs; it does not mean the final smoothness gate is
ready. No extra field may package CI or flatness as an assumed conclusion.
The split is committed before code. The order within each dependency chain
is mandatory; independent ready leaves can proceed while theory is missing.

### L6b.2b: identify the actual fibres, then prove and descend CI

| Leaf / module | Exact obligation and proof route | Dependencies / initial state |
|---|---|---|
| F1 / NilpotentGeometricCharacteristic | For a ring map B → Ω to a field, nilpotence of p in B forces `CharP Ω p` for prime p. Also every map to a reduced ring kills a nilpotent coefficient kernel. | Ready: map nilpotence, reducedness, `CharP` prime criterion. |
| F2 / HopfPointedFibre | For Hopf B → A, an A-algebra S identifies S ⊗_B A with S ⊗_R (A/augmentationIdeal). Base-change `torsorEquiv`, cancel tensor factors; prove the coordinate formula using the original coaction. | Ready: `HopfTorsor`, `cancelBaseChange`, `congr`. |
| F3 / PDivisibleKernelFibre | Identify the augmentation quotient of level m+n over level n with the original level m via the *original inclusion*. Compose F2 and prove evaluation on pure tensors, retaining that inclusion. | Ready after F2: `X.kernel`, `X.closed`, quotient-kernel equivalence. |
| F4 / GeometricFibrePoint | A nonzero finite algebra over an algebraically closed field has a rational point (maximal quotient and algebraicity); apply to a finite faithfully flat fibre to get a lift of the specified point. | Ready: maximal ideal, algebraically closed field and finite tensor-product APIs. |
| F5 / DivisionGeometricFibre | For an arbitrary geometric point of the actual division target, use F4 to install the point-compatible scalar tower and apply F3. State the equivalence on the specified pullback and retain its coordinate map. | F3–F4; requires careful scalar-tower transport. |
| F6 / FiniteHopfIdentityComponent | For a finite Hopf algebra over an algebraically closed field, construct its identity local factor with induced comultiplication and antipode. Show the quotient to this factor preserves the counit. | Missing: restrict the Hopf operations to the identity component; Artinian idempotent decomposition alone is insufficient. |
| F7 / FiniteHopfComponentTranslation | Each local factor has a rational point; translation by it identifies that factor with F6's identity factor. Prove the induced maps and inverse. | F4, F6; missing component restriction of translation. |
| F8 / PolynomialLocalDimension | At a rational maximal ideal in an n-variable polynomial ring over a field, compute local dimension n and identify the variable differences as a regular sequence. | Missing commutative algebra; use Mathlib `IsRegular` rather than a new predicate. |
| F9 / ParameterSequenceRegular | In the polynomial local ring of F8, an n-element ideal with Artinian quotient is a regular sequence. Prove the parameter-sequence criterion, not merely equality of generator and relation counts. | F8; missing Cohen–Macaulay parameter theorem. If the proof exceeds 150 lines, split its depth/parameter induction before implementation. |
| F10 / LocalHopfRegularPresentation | Apply F9 to `exists_minimal_local_quotient_presentation`; finite-dimensionality makes the quotient Artinian. | F9; existing square presentation alone is not enough. |
| F11 / GeometricDivisionLocalCI | Translate local factors using F7, transfer F10's regular presentations across F5, and cover the geometric fibre by these factors. | F5, F7, F10. Positive characteristic supplied by F1. |
| F12 / FibrePresentationDescent | Descend finite presentation coefficients and regularity from the algebraic closure to a finite field extension and then by faithful flatness. | Missing finite-data descent and faithful-flat reflection of regularity; preservation is in `Regular.Flat`. |
| F13 / RelativeCIChartNeighbourhood | Spread a regular fibre presentation to a principal neighbourhood of the corresponding point of the original finitely presented division algebra, retaining the quotient map. | F11–F12 and the flatness/localization chain below; source 00SY. |
| F14 / FiniteDivisionCICharts | Extract finitely many F13 neighbourhoods by quasicompactness and prove their defining elements generate the unit ideal. | F13; W42 `LiftedChartCover` consumes this conclusion. |

F6–F14 are mathematical proof obligations (W44 results recorded below), not new structures
whose fields assert the desired property. The broad parameter theorem in
F9 may need another internal split; no implementation is scheduled until
its depth argument is specified. All other rows name a single coordinate,
local-algebra, descent, or finite-cover step. Characteristic-zero fibres are
not needed on the p-nilpotent test algebras of this task.

### L6b.3c: regular sequences, approximation, and flatness

| Leaf / module | Exact obligation and proof route | Dependencies / initial state |
|---|---|---|
| C1 / DirectLimitFiniteRelation | Every finite tuple in a directed module colimit has representatives at one stage; a finite linear relation holds at a later common stage. No injectivity of transition maps. | Ready: `Module.DirectLimit.exists_of`, directed upper bounds, `of.zero_exact`. |
| C2 / FlatModuleDirectLimit | A directed colimit of flat modules over one fixed ring is flat. Trivialize the relation from C1 at its stage and map its witnesses into the limit. | Ready after C1: `Flat.of_forall_isTrivialRelation`. |
| C3 / FibreRegularBaseChange | Transport a given regular sequence under faithfully flat field extension and localize a weakly regular sequence at a prime containing it. | Already supplied by `Regular.Flat`; reuse directly, do not duplicate wrapper modules. |
| C4 / NoetherianFibreRegularElement | For a flat local map of Noetherian local rings, fibre-regular x is regular upstairs and the quotient by x is flat over the base. | Missing local flatness criterion (00MG). Prove using the ideal/tensor criterion and Krull intersection; neither regularity nor quotient flatness is an input. |
| C5 / FibreRegularSequenceInduction | Iterate C4 on successive quotients; keep the original list order and the quotient by each prefix. | C4, `isWeaklyRegular_cons_iff`, `QuotSMulTop`. |
| C6 / NoetherianRelativeCIFlat | Localize at all primes and apply C5 to a finite polynomial presentation whose fibre relations are regular; deduce global flatness. | C5 plus flatness locality; Noetherian case of 00SV. |
| C7 / PresentationCoefficientStage | Put finitely many polynomial coefficients and finitely many presentation identities in one finitely generated ℤ-subalgebra of B, with exact reconstruction after base change. | Missing finite-data approximation, source 00SU. No Noetherian hypothesis on B. |
| C8 / RelationRegularityStage | Spread the relative-CI fibre condition to a sufficiently large Noetherian coefficient stage, including the required principal localization. | C7 and F12–F13; source 00SU, not an automatic consequence of finite coefficients. |
| C9 / LiftedQuotientColimit | Identify the presented B-algebra with the directed colimit of the base-changed coefficient-stage quotients, with equality on polynomial representatives. | C7; missing algebra-colimit/quotient comparison. |
| C10 / ArbitraryBaseRelativeCIFlat | Use C6 and C8, base-change flatness to the fixed final base B, then C2 and C9. | C2, C6, C8–C9; arbitrary-base part of 00SV/00SW. |
| C11 / NilpotentFibreComparison | Field-valued maps kill the nilpotent coefficient kernel; identify the fibres of W42's lifted quotient with those of its specified reduction. | F1, W42 `LiftedPresentationBaseChange`, tensor cancellation. |
| C12 / LiftedRelativeCIFlat | Transfer the chart's fibre-regular presentation by C11 and apply C10; a localization element reducing to 1 is a unit for a nilpotent kernel. | C10–C11; completes 3c for the charts produced by F14. |

C4's local criterion and C8's spreading lemma remain major source-proof
dependencies. Before implementing either, split the ideal-adic criterion
and regularity-spreading argument into capped modules. This is recorded
explicitly rather than treating 00SV as a one-line library application.
C2 is a fixed-base theorem: a varying-ring approximation cannot use it
until stage flatness has been base-changed to B. W42's reduction and
covering lemmas apply only after F14 and C12. L7b.4/L8/L9 and
`IsHardlyRamified.mem_isCompatible` remain untouched by these foundations.

### Internal leaves for the remaining large source arguments

The following replaces the provisional “split before implementation” notes
on F9, C4 and C8 above. Source checked against Stacks commit
`89afc779ad518678546d4209d41e00ae072f680a`, `algebra.tex`, specifically
`lemma-mod-injective`, `lemma-grothendieck`, `lemma-lci`,
`lemma-relative-global-complete-intersection-Noetherian`, and
`lemma-colimit-rings-flat`. Every row has a 150-line module cap and remains
unproved. A parent row is an assembly milestone, not an implementation leaf.

| Internal leaf | Single proof obligation | Dependencies |
|---|---|---|
| F9a / LocalParameterAvoidance | In a Noetherian local Cohen–Macaulay ring, the first member of a system of parameters avoids every associated prime; state the depth hypothesis via lengths of Mathlib regular sequences. | Associated-prime dimension/depth comparison. |
| F9b / ParameterFirstRegular | Convert F9a's avoidance into `IsSMulRegular` using the zero-divisor/associated-prime criterion. | F9a; finite-module associated-prime API. |
| F9c / ParameterQuotientDepth | Quotient by a regular parameter decreases dimension and maximal regular-sequence length by one. | F9b; dimension inequality and lifting regular sequences across one quotient. |
| F9d / ParameterRegularInduction | Induct on the parameter list with F9b–c and `isRegular_cons_iff`; the terminal quotient remains nonzero. | F9b–c. |
| F9e / PolynomialLocalParameterCriterion | Supply the dimension/depth equality for the polynomial local ring in F8, then apply F9d to an Artinian quotient with n generators. | F8, F9d. This is the actual input to F10. |
| C4a / AdicGradedTensorComparison | Identify M⊗(m^n/m^(n+1)) with (M/mM)⊗_(R/m)(m^n/m^(n+1)), with quotient maps. | Tensor/quotient universal properties. |
| C4b / AdicQuotientExactRow | Construct the exact row from the graded piece to M/m^(n+1)M to M/m^nM; flatness of M makes its first map injective. | C4a, tensor right exactness and `Flat` preservation of injectivity. |
| C4c / AdicInjectivityInduction | A map N→M injective modulo m is injective modulo m^n for every positive n, with M flat. | C4b and injectivity after tensoring vector spaces over R/m. |
| C4d / AdicSeparatedInjectivity | If S is Noetherian local and N finite over S, use Krull intersection for mS to deduce injectivity of N→M from C4c. | C4c and the existing Krull intersection theorem. |
| C4e / QuotientBaseInjectivity | Apply C4d to R/I→S/IS and N/IN→M/IM for every proper ideal I; prove the residual injectivity and quotient finiteness hypotheses. | C4d, quotient tensor comparison. |
| C4f / FlatCokernelIdealCriterion | For an injective N→M with M flat, injectivity modulo every ideal implies flatness of the cokernel. Use the tensor ideal criterion, avoiding a new Tor theory. | Tensor exactness; `Flat.iff_rTensor_injective'`. |
| C4g / FibreRegularElementAssembly | Apply C4d–f to multiplication by f on S. Identify its cokernel with S/(f) and obtain both regularity and quotient flatness. | C4d–f. This closes C4; C5 is list induction. |
| C8a / FibreDimensionFieldExtension | Finite-type fibre dimension is invariant under field extension; retain the residue-field comparison of coefficient stages. | Noether normalization and integral-extension dimension. |
| C8b / FibreDimensionPrincipalNeighbourhood | A point with fibre dimension ≤d has a principal neighbourhood where the fibre dimension stays ≤d. | Quasi-finite presentation over d polynomial variables and dimension of its fibres. |
| C8c / ApproximationFiniteNeighbourhoods | Apply C8b at the images of primes from the final algebra and choose finitely many neighbourhoods covering its spectrum. | C7, C8a–b, quasicompactness. |
| C8d / UnitIdealCertificateStage | Descend a finite equation Σ a_j g_j=1 in the final presented algebra to one enlarged finitely generated coefficient stage. | C7; finite coefficients of the a_j and of the relation-ideal membership witnesses. |
| C8e / RelativeCIApproximationAssembly | C8c's fibre-dimension bounds plus C8d's unit ideal give the relative global CI condition at the enlarged Noetherian stage. | C8a–d and base-change invariance of relative CI. |
| C9a / PolynomialCoefficientColimit | Every polynomial and every equality of polynomials occur at a finite coefficient stage. | Finite support and directed bounds. |
| C9b / RelationQuotientColimit | Quotient by the fixed finite relation list commutes with the coefficient-stage colimit; prove representative formulas. | C9a; ideal membership has finite witnesses. |
| C9c / LocalizedQuotientColimit | Localizations at the primes induced from the final prime commute with C9b's colimit. | Fraction representatives and denominator equality witnesses. |
| C10a / FixedBaseStageComparison | Compare the varying-base module colimit with the fixed-B colimit of B⊗_(B_i)M_i; construct both maps on representatives. | Semilinear transitions, finite-stage equality. |
| C10b / VaryingBaseColimitFlat | Each B⊗_(B_i)M_i is B-flat; apply C2 and C10a. | C2, C10a, `Flat` base change. |
| C10c / RelativeFlatnessAssembly | Apply Noetherian C6 at stages from C8e and use C9c/C10b for every localized prefix quotient. | C6, C8e, C9c, C10b. |

These rows expose further foundational assumptions rather than silently
calling them library results: F9a needs a depth/associated-prime theorem,
F9c needs the regular-element dimension/depth theorem, and C8a–b need
fibre-dimension theory. F9 is proved in W44 below; C8a–b remain research dependencies whose
150-line budgets are planned, not validated line counts. The ready leaves
implemented in W43 do not establish any of those assumptions.

W43's C11 implementation is subdivided into `ReductionGeometricFibre`
(quotient-base equivalence and further tensor base change) and
`LiftedPresentationGeometricFibre` (the original presentation and polynomial
representative formula). F1 supplies unique factorization of reduced-valued
points through a nilpotent surjection. C1–C2 concern a fixed base; C10a–b
are explicitly still required for the varying-base source argument.

### W44: dimension and depth foundations first

F8 is split into the following new-module leaves (150 lines each):
`MvPolynomial.VariableRegularSequence` proves regularity of distinct variables
by the monomial-ideal membership criterion; `MvPolynomial.TranslatedVariables`
transfers this to variable differences at any rational point;
`PolynomialLocalDimension` localizes these sequences and computes dimension
from their length and the polynomial dimension upper bound.
For F9c, use `KrullDimension.Regular` for dimension and `Depth.Rees` for
regular-sequence existence; the deprecated `Regular.Depth` file supplies
neither a depth definition nor a Cohen–Macaulay theorem. The depth/associated
prime comparison in F9a and the parameter theorem in F9d remain proof
obligations, not consequences of the `IsRegularLocalRing` typeclass.

F9a is further split into `Regular.AssociatedPrimeQuotient` (Krull
intersection gives a surviving annihilator witness and a strictly larger
associated prime in the regular quotient), `Regular.AssociatedPrimeDimension`
(iterate to construct a prime chain and bound depth at every associated
prime), and `Regular.ParameterIdealDimension` (Krull's height theorem bounds
the dimension after removing a parameter lying in a prime). Together these
supply parameter avoidance; `Regular.QuotientDepth` supplies F9c's depth
induction via Rees. Each implementation leaf retains the 150-line cap.

W44 validation checkpoint: F8, F9a–e and F10 are proved in new modules.
The proof uses explicit regular-sequence witnesses, Krull intersection to
lift associated primes, prime chains for the depth bound, Krull height for
the parameter bound, and Rees for the regular-quotient depth drop.
`LocalHopfRegularPresentation.exists_minimal_local_regular_presentation`
(in namespace `HopfAlgebra`) applies this to the actual minimal local Hopf
presentation. All 13 foundation modules passed individual build and lint;
all 34 named declarations have only the standard three axioms.
F6–7 and F11 are now implemented in the leaves below. F12–13 have partial
foundations; F14 and the flatness/assembly milestones remain outstanding.

### W44: geometric local factors and descent foundations

The identity factor is the quotient by its complementary primitive
idempotent. Its comultiplication, counit and antipode descend from the
original Hopf algebra. Translation by a rational point restricts to an
isomorphism from that point's local factor to the identity factor.
`GeometricDivisionLocalCI` applies the resulting regular presentations to
W43's actual geometric division fibre, retaining the original
comultiplication formula and kernel inclusion. The geometric factor
idempotents generate one, and each factor is its principal localization.
This is a cover over the geometric field; it does not supply F14's relative
charts over the original base.

| Item | New-module leaves (each at most 150 lines) | Result |
|---|---|---|
| F6 | `FiniteAlgebraComponents`, `FiniteAlgebraPointComponent`, `FiniteHopfIdentityAntipode`, `FiniteHopfIdentityComponent` | Identity local factor with the induced Hopf structure and surjective bialgebra map. |
| F7 | `FiniteAlgebraComponentMap`, `FiniteAlgebraComponentPoint`, `HopfPointTranslation`, `FiniteHopfComponentTranslation` | Rational points on factors, restricted translations and formulas on representatives. |
| F11 | `LocalHopfRationalRegularPresentation`, `FiniteHopfComponentRegularPresentation`, `FiniteAlgebraPrincipalComponents`, `GeometricDivisionLocalCI` | Regular presentations of all actual geometric fibre factors and their finite principal cover. |
| F12a | `Regular.FaithfullyFlatDescent` | Faithfully flat reflection of regularity, including all quotient injectivity tests. |
| F12b | `MvPolynomial.FiniteFieldDescent` | Finite polynomial relation lists descend to a finite subextension of an algebraic field extension; regularity descends with them. |
| F13a | `Regular.LocalizationInjectivity`, `Regular.FiniteLocalizationInjectivity` | Finitely many maps with finite kernels that are injective at a prime are injective on one principal neighbourhood. |
| F13b | `Regular.LocalizationRegularity`, `Regular.PrincipalNeighbourhood` | A regular sequence on a Noetherian module at a prime is regular on a principal neighbourhood; includes the ring form. |

F12 still needs descent of the localized presentation, its quotient
isomorphism and its coordinate map, and comparison with a presentation
over the residue field. F13b spreads a specified list of original-ring
elements; it does not spread the relative fibre condition or produce the
original algebra's chart presentation. That requires clearing localized
relations, controlling the presentation kernel and the relative flatness
criterion. F14's finite relative chart family, C4–C12's remaining flatness
leaves and the covering/lifting assembly are not proved here.

Recheck this checkpoint with the individual module builds, individual
`lake exe runLinter MODULE` calls and `#print axioms` for each named
declaration. W44's untracked handoff records the exact module counts,
commits, checked-at timestamp and validation logs.


### W45: localized descent and Noetherian principal ideal charts

The following are implementation leaves, each capped at 150 whole-module
lines. They refine F12–F14; they do not close the formal-smoothness gate.

| Leaf | Module | Obligation |
|---|---|---|
| F12c | `MvPolynomial.OriginLocalizationMap` | Construct the original-coordinate local coefficient map; prove flatness and faithful-flat reflection of regularity. |
| F12d | `MvPolynomial.LocalizedFiniteFieldDescent` | Descend numerators and denominators of a finite localized relation list to one finite field, retaining order, length and regularity. |
| F12e | `MvPolynomial.LocalizedQuotientDescent` | Reconstruct the quotient after extending the localized source, with its explicit tensor coordinate formula and injectivity of the descended quotient map. |
| F12f | `FaithfullyFlatPresentationDescent` | Reflect the kernel, regularity and quotient isomorphism through a specified faithfully flat coordinate square. |
| F12g | `GroupScheme.FiniteHopfComponentFiniteFieldPresentation` | Apply finite coefficient-field descent and reconstruction to W44's actual geometric Hopf components. |
| F12h | `LocalRing.AlgebraicTensor` | Prove that algebraic coefficient extension preserves locality for a local algebra with rational residue field. |
| F12i | `MvPolynomial.OriginResidue` | Compute the rational local residue field, evaluation map and coefficient-compatible local map. |
| F12j | `MvPolynomial.OriginTensorMaps` | Construct both coefficient-tensor/localization maps, proving all new denominators invertible. |
| F12k | `MvPolynomial.OriginTensorEquiv` | Prove those maps inverse, with the original coefficient and fraction formula. |
| F12l | `MvPolynomial.FiniteFieldPresentationDescent` | Descend the localized regular quotient to a finite field, reconstruct it by coefficient-field base change, and retain the quotient coordinate formula. |
| F13c | `Regular.UnitMultiples` | Unit changes preserve each prefix ideal and regularity test. |
| F13d | `Regular.ClearLocalizedRelations` | Clear a localized regular relation list using numerators in the original ideal. |
| F13e | `Localization.PrincipalIdealComparison` | Spread equality of finite ideals from a prime, controlling the entire localized kernel; retain equality after denominator refinement. |
| F13f | `Regular.PrincipalRefinement` | Refine principal regularity neighbourhoods while preserving the nonzero quotient at the original prime. |
| F13g | `Regular.PrincipalIdealPresentation` | Produce one Noetherian principal neighbourhood with regular numerators and the full relation ideal. |
| F14a | `Localization.QuotientAwayPresentation` | Identify these quotients with the actual principal localizations of the original quotient, preserving coordinates. |
| F14b | `Regular.FinitePrincipalIdealCover` | From regular presentations at every prime over an ideal, extract a finite principal unit-ideal cover and its coordinate-compatible presentation isomorphisms. |

F12e extends the localized polynomial source. F12h–l prove the stronger
coefficient-field reconstruction: algebraic field extension commutes with
the rational polynomial local ring, and hence with the quotient by the
descended relation list. The quotient isomorphism retains its original
coordinate formula. F12g applies this to the geometric Hopf components.

F12f proves reflection for a specified commuting square. Constructing the
comparison with a presentation over the original residue field, including
any change of polynomial presentation, remains an obligation. Descent to
a finite extension is not yet descent of the CI property to that residue
field. No conclusion-assuming record is used.

F13g and F14b concern a Noetherian ring and an ideal whose regular local
presentations are already supplied. They prove denominator clearing,
kernel control, principal charts and finite extraction in that setting.
They do not spread the relative fibre condition over an arbitrary base,
or supply those hypotheses for the actual division algebra.
C4–C12 and the original lifting/formal-smoothness assembly remain separate.

### W46: prescribed geometric coordinates and constructed coefficient squares

These F12 leaves have a 150-line whole-module cap. They reduce the
presentation-comparison obligation; the all-fibres residue-field CI application remains open.

| Leaf | Module | Obligation |
|---|---|---|
| F12m | `MvPolynomial.GraphIdeal` | Compute the entire kernel after adding redundant polynomial coordinates: graph equations plus the extended original kernel, with an explicit finite ordered relation list. |
| F12n | `MvPolynomial.GraphRegularSequence` | Identify the graph quotient with the coefficient ring; prove that graph equations followed by the original regular relations are regular in that order. |
| F12o | `MvPolynomial.OriginPresentationBaseChange` | Construct coefficient base change of a specified rational local presentation, prove surjectivity and extension of its full kernel, and reflect a specified original relation list with its quotient coordinates. |
| F12p | `GroupScheme.RationalCoordinateRegularPresentation` | Identify the rational point attached to arbitrary local coordinates, and convert a square kernel into regular localized relations and the original quotient map. |
| F12q | `GroupScheme.LocalHopfArbitraryCoordinates` | Translate by the counit internally to construct square relations for arbitrary generating coordinates of a finite local Hopf algebra over a perfect field. |
| F12r | `GroupScheme.LocalHopfCoordinateRegularPresentation` | Apply F12p–q to every specified generating tuple, retaining the full localized kernel and coordinate-compatible quotient isomorphism. |
| F12s | `GroupScheme.FiniteHopfComponentCoordinatePresentation` | Apply translation to the identity Hopf component to produce square kernels and regular local presentations in arbitrary prescribed coordinates of every geometric component. |
| F12t | `LocalRing.ResidueGenerators` | Lift a basis of the residue module to a generating family of a finite module over the original local ring. |
| F12u | `LocalRing.GeneratorDescent` | Compare residue dimensions under local base change and descend a bound on the number of generators; the geometric generators need not descend. |
| F12v | `FlatIdealBaseChange` | Identify the tensor of an ideal with its actual extended ideal under a flat map, preserving original elements. |
| F12w | `LocalRing.IdealGeneratorDescent` | Apply F12u–v to construct an original n-element relation list from n generators of the extended ideal. |
| F12x | `MvPolynomial.OriginRegularDescent` | Descend a square geometric kernel to regular original relations for an Artinian quotient at the rational origin, with the specified quotient map. |

F12s strengthens the existential geometric presentation from W44: its
input is the specified coordinate tuple and its surjective evaluation map.
It does not replace those coordinates by minimal generators. F12m–n
handle stabilization by redundant variables, including regularity; they do
not prove cancellation or arbitrary change-of-presentation invariance.

F12o constructs the commuting coefficient square in the rational-origin,
algebraic-field-extension case. F12t–w supply the missing generator bound:
flat local base change identifies the extended ideal as a module tensor;
residue dimensions agree, and Nakayama lifts an original residue basis.
F12x then applies the rational polynomial parameter criterion. Its input
is an n-element generating family of the geometric kernel; neither a
descending relation list nor geometric regularity is assumed. The output
includes n original regular relations, the full kernel and the original
quotient-coordinate formula.

The remaining F12 application must identify the actual geometric fibre
presentation with this constructed comparison. Non-rational residue
points require the appropriate localization after field extension; the
origin equivalence alone does not supply that comparison. F12s supplies
relations for each specified geometric component, while F12x handles the
specified rational-origin coefficient square. Their hypotheses have not
yet been connected for all fibres of the original division algebra.

F13 still requires relative presentations and a fibre-regularity
neighbourhood over the original base, including arbitrary-base
approximation. F14's finite relative cover, C4–C12's relative flatness and
the formal-smoothness assembly remain unproved. None of these statements
follows solely from the new absolute geometric presentations.


### W47: actual residue-field fibre comparison

F12 now applies to each specified polynomial presentation of the actual
characteristic-p residue division fibre at every prime over its kernel.
`DivisionResidueLocalCI.exists_residue_division_regular_relations_atPrime`
constructs a list with exactly as many relations as polynomial variables,
generating the original localized kernel and regular over the original field.
There is no rational-residue hypothesis and no assumed geometric kernel square.

The implementation leaves (whole-module cap 150) are:

| Leaf | Module | Result |
|---|---|---|
| F12y | `MvPolynomial.GeometricPointLocalization` | Flat local coefficient map at any geometric point and its contraction; comparison of the extended original ideal. |
| F12z | `MvPolynomial.GeometricRegularDescent` | Descend the generator bound through the flat local map, apply the geometric parameter criterion, and reflect regularity. |
| F12aa | `MvPolynomial.CoefficientPresentation` | Extend a specified polynomial presentation with its coordinates, surjectivity and entire kernel. |
| F12ab | `GroupScheme.ComponentLocalizedKernel` | Projecting onto a pointed component preserves the original kernel after localization; prove this using the primitive idempotent. |
| F12ac | `GroupScheme.GeometricHopfLocalizedKernel` | Square generators and the actual component quotient for the original geometric presentation. |
| F12ad | `GroupScheme.HopfGeometricPresentationDescent` | Connect the geometric component kernel to the original localized presentation and descend regular relations. |
| F12ae | `GroupScheme.HopfGeometricPointDescent` | Retain a specified original fibre point through the geometric comparison. |
| F12af | `GroupScheme.DivisionResidueFibreComparison` | Construct the comparison for the actual residue division fibre by tensor cancellation and division translation. |
| F12ag | `MvPolynomial.ResidueGeometricPoint` | Construct a geometric point above each original prime, with exactly that contracted ideal. |
| F12ah | `GroupScheme.DivisionResidueRegularPresentation` | Apply the constructed comparison at every specified geometric point of the actual residue fibre. |
| F12ai | `GroupScheme.DivisionResidueLocalCI` | Apply the geometric-point construction at every prime of the original residue-field presentation. |

This replaces the rational-origin restriction of F12x in the actual fibre
application: F12z uses `Ideal.exists_ofList_of_map_eq_span` and faithfully flat
reflection directly at the contracted geometric point. F12x remains a valid
specialized interface. The result concerns characteristic-p residue fields,
as required for p-nilpotent test algebras.

F13 still requires spreading these presentations over the original arbitrary
base. A finite chart cover of an individual residue fibre does not imply
F14's relative chart cover. C4–C12 and the formal-smoothness assembly remain
unproved; the family admission has not been replaced.


W47 further leaves (cap 150 each):

| Leaf | Module | Result |
|---|---|---|
| F14c | `Regular.FinitePresentationCover` | Extract finite principal charts of a specified algebra presentation, retaining the number of equations and the original coordinate map to each actual localization. |
| F12aj | `GroupScheme.DivisionResidueFiniteCharts` | Apply finite extraction to the actual residue division fibre; the chart denominators generate the unit ideal in that fibre. |
| F12ak | `GroupScheme.DivisionPullbackFibreLocalCI` | Apply F12ai to every field-valued fibre of the actual division pullback over an arbitrary p-nilpotent test algebra. Derive the characteristic from nilpotence and construct the tensor cancellation. |
| F13h | `Flat.PresentationKernelIntersection` | Use the flat target's equational criterion to prove that the original kernel intersects any extended base ideal in their product. No Noetherian or principal-ideal assumption. |
| F13i | `Flat.FibreRelationLifting` | Nakayama lifts generators through any extended base ideal contained in the presentation source's Jacobson radical, using the proved intersection formula. |
| F13j | `Flat.ReducedPresentation` | Construct the actual reduced algebra map, compute its entire kernel, and lift reduced generators to a coordinate-compatible presentation of the original flat target. |

The exact F12 application theorem is
`ThreeAdicPlan.PDivisibleSystem.exists_division_pullback_fibre_regular_relations`.
Its inputs are the actual system, a point into a p-nilpotent test algebra,
a field-valued specialization, and any surjective polynomial presentation of
that fibre. It proves regularity and generation at every prime of that
original presentation. It assumes neither a geometric comparison nor an
original regular list. Taking the field to be a residue field includes
non-rational points of the original base.

F13j lifts generators modulo a base ideal, under an explicit finite-kernel
hypothesis. Applying it to F12ak still requires the localized residue-fibre
comparison over the original base, finite generation for that localized
presentation, clearing denominators, and simultaneous fibre regularity on
the resulting neighbourhood. F13j does not assert those conclusions or
flatness of a newly lifted chart. F14c/F12aj cover a single residue fibre;
F14's relative cover is still missing. C4–C12's adic criterion, approximation,
relative flatness and the later formal-smoothness assembly remain open.

## W48: actual relative charts and Noetherian coefficient reconstruction

The original relative presentation and finite-cover part of F13/F14 is now
proved over an arbitrary test algebra. `DivisionRelativeCICover` constructs
an ordinary polynomial presentation internally, then finitely many principal
charts of the **actual division pullback**. The defining elements generate one
in that pullback. Each chart has exactly as many equations as polynomial
variables, retains the original coordinate map, and its specified equation
list is regular at every point of every field-valued fibre on the chart.
This is a relative cover over the original test algebra, extending W47's
cover of one residue field. It is not a flatness theorem for newly lifted
quotients or a formal-smoothness theorem.

The finite-target argument supplies simultaneous fibre regularity directly:
any square list generating a local presentation kernel of a finite field
algebra is regular. The proof passes to a geometric point, applies the
rational polynomial parameter criterion to the actual Artinian quotient,
and reflects the regularity of the **specified list** by faithful flatness.
An ideal equality on a principal open survives any coefficient map where
the denominator is a unit. Consequently the same original relation list
works on every field fibre of that chart. No Noetherian assumption is
introduced on the original base, and no stage-regularity assertion is used
as a replacement for C8.

### New capped leaves

All names below are under `FLT.Mathlib.RingTheory` unless prefixed
`GroupScheme`. Each new module has at most 150 whole-file lines.

| Leaf | Module | Proved obligation |
|---|---|---|
| F13k | `Flat.LocalizedFinitePresentation` | Original local presentation map, surjectivity, full kernel, finite generation from finite presentation, and the contracted base prime's radical inclusion. |
| F13l | `Flat.LocalizedRelationLifting` | Apply arbitrary-base-ideal relation lifting with the actual finite kernel and radical inputs. |
| F13m | `Flat.LocalizedResidueQuotient` | Localized residue-fibre/quotient equivalence, preserving original coordinates. |
| F13n | `Flat.LocalizedResidueKernel` | Tensor right exactness identifies the entire fibre kernel with the reduced original local kernel. |
| F13o | `Flat.ResidueRelationLifting` | Lift actual fibre relation generators through that comparison. |
| F13p | `Flat.ResiduePresentationPoint` | Construct the fibre point with the required contraction and kernel containment. |
| F13q | `Flat.ResidueRegularLifting` | Retain equation count, full generation, order, and regularity after reduction. |
| F13r | `MvPolynomial.BaseChangePresentation` | Base change of a specified polynomial presentation over arbitrary coefficient rings. |
| F13s | `Regular.LocalPresentationTransport` | Transport local ideals and regular lists through coordinate equivalences. |
| F13t | `MvPolynomial.TensorLocalRelations` | Transfer polynomial-fibre relations to tensor-product coordinates. |
| F13u | `MvPolynomial.RelativeLocalRelations` | Assemble original local equations from the actual residue-fibre relations. |
| F13v | `GroupScheme.DivisionRelativeLocalRelations` | Apply F13u to the actual division pullback, deriving finiteness and flatness inputs. |
| F13w | `Regular.CommonDenominatorRelations` | Clear one common denominator inside the original ideal and preserve a regular reduction. |
| F13x | `Regular.RelativePrincipalRelations` | Spread full-kernel generation to a principal neighbourhood without Noetherian hypotheses. |
| F14d | `Localization.PrincipalPresentationEquiv` | Identify a principal relation quotient with the actual target chart and original coordinates. |
| F13y | `GroupScheme.DivisionPrincipalRelations` | Construct those principal charts for the actual division pullback. |
| F13z | `Localization.ArtinianPresentation` | Localized kernels of presentations of Artinian algebras have Artinian quotient. |
| F13aa | `MvPolynomial.GeometricParameterRegularity` | Reflect regularity of a specified square geometric parameter list. |
| F13ab | `MvPolynomial.FiniteFibreParameterRegularity` | Every square local kernel list of a finite field algebra is regular. |
| F13ac | `Localization.PrincipalIdealBaseChange` | Transport principal-open ideal equality along any map inverting its denominator. |
| F13ad | `MvPolynomial.PrincipalFibreRegularity` | Prove simultaneous field-fibre regularity on the entire principal chart. |
| F14e | `Regular.FiniteRelativePresentationCover` | Extract a finite principal cover, retaining the full kernels, equation counts and coordinate equivalences. |
| F14f | `GroupScheme.DivisionRelativeFiniteCharts` | Finite relative fibre-regular cover for any specified original division presentation. |
| F14g | `GroupScheme.DivisionRelativeCICover` | Construct that original polynomial presentation internally; no presentation input is required. |
| C7a | `MvPolynomial.NoetherianCoefficientStage` | Descend finite polynomial data to a finitely generated integer subalgebra and reflect all polynomial identities among it. |
| C7b | `MvPolynomial.RelationBaseChange` | Relation quotients commute with arbitrary coefficient base change, on original polynomial representatives. |
| C7c | `MvPolynomial.NoetherianRelationStage` | Reconstruct a finite relation quotient exactly from the chosen Noetherian coefficient stage. |

### Remaining flatness and assembly boundary

C7a–c construct a Noetherian coefficient stage; they do **not** assert that
the fibre-regularity property holds at that stage. W49 below proves the Noetherian local
flatness criterion C4a–g, regular-sequence quotient induction C5, and local
to global flatness C6. C8's eventual regularity-stage
spreading and C9's varying-stage colimit comparison also remain. Principal
localization must be included in these approximation comparisons. C10–C12
then need to prove flatness of the actual **lifted** relation charts.

W42's finite-product/cover lemmas can use the new original principal cover
only after that lifted-chart flatness and the compatible reduction maps
are supplied. Local point lifts, overlaps, descent, nilpotent iteration,
and the subsequent family-realization obligations remain. In particular,
`IsHardlyRamified.mem_isCompatible` has not been replaced or edited.

Validation evidence is recorded in the untracked `FAMILY_W48_DONE.md`,
`W48_VALIDATION.json`, `W48_AXIOMS.log`, and `W48_BOUNDARY_AXIOMS.log`.
The read-only reproducible checks are individual `lake build MODULE`,
`lake exe runLinter MODULE`, and `#print axioms` for every new declaration;
the final handoff records their checked-at time, source hashes and the
single post-merge root build.


## W49: adic local flatness and Noetherian relative complete intersections

The C4–C6 proof chain is now implemented. Its strongest local statement,
`Module.Flat.injective_and_flat_of_local_residue`, starts with a right exact
sequence `N → M → Q`, a flat `R`-module `M`, and an `N` finite over a
Noetherian local `R`-algebra `S`. For a local map `R → S`, injectivity of
`N → M` on the residue fibre implies injectivity upstairs and `R`-flatness
of `Q`. No target-quotient flatness is assumed. The base `R` need not itself
be Noetherian in this criterion.

The graded comparison includes the actual quotient `M/IM` and a formula
on quotient representatives. Tensor right exactness supplies the successive
adic rows; flatness of the original target supplies their left injectivity.
An exact-sequence argument propagates residual injectivity through powers.
Krull intersection then separates the finite source.

C4e uses an equivalent proof that avoids rebuilding scalar structures over
`R/J`: it proves injectivity modulo `J + m^n`, using a transition kernel
annihilated by `m`. Applying Krull intersection to `N/JN` reflects membership
in `JN`. Thus the original map remains injective after tensoring with `R/J`
for every ideal `J`. A tensor diagram chase with `J → R → R/J` and
`Flat.iff_rTensor_injective'` proves cokernel flatness.

| Leaf | Module under `FLT.Mathlib.RingTheory` | Proven output |
|---|---|---|
| C4a | `Flat.AdicGradedTensorComparison` | Graded tensor and module-quotient comparisons, including representative formulas. |
| C4b | `Flat.AdicQuotientExactRow` | Exact adic rows and injectivity of their left tensor map for flat modules. |
| C4c.1 | `Flat.TensorInjectivityExtension` | Injectivity across a short exact tensor sequence. |
| C4c.2 | `Flat.AdicInjectivityInduction` | Injectivity modulo all positive powers. |
| C4d | `Flat.AdicSeparatedInjectivity` | Krull-separated injectivity, including the local-map corollary. |
| C4e.1 | `Flat.AdicBaseIdealInduction` | Injectivity modulo `J + m^n`. |
| C4e.2 | `Flat.AdicSubmoduleClosed` | Closedness of each submodule in the finite Noetherian module. |
| C4e.3 | `Flat.QuotientTensorInjectivity` | Tensor injectivity is reflection of ideal-multiple membership. |
| C4e.4 | `Flat.QuotientBaseInjectivity` | Injectivity modulo every base ideal. |
| C4f | `Flat.FlatCokernelIdealCriterion` | The flat-cokernel ideal criterion. |
| C4g.1 | `Flat.LocalFlatCokernel` | Local injectivity and flat cokernel assembly. |
| C4g.2 | `Flat.NoetherianFibreRegularElement` | Regularity and flat scalar quotient; also the actual ring quotient `S/(x)`. |
| C5a | `Flat.RelativeQuotSMulTensor` | Scalar quotient/tensor comparison over the smaller base, linear over the ambient algebra. |
| C5b | `Flat.FibreRegularSequenceInduction` | Ordered regular-sequence induction and flatness of every original prefix quotient. |
| C6a | `Flat.LocalizedQuotientFlatness` | Relative quotient flatness checked in ambient maximal localizations. |
| C6b | `Flat.NoetherianRelativeCIFlat` | Stalk induction and global flatness, requiring regularity only on the zero locus. |
| C6c | `Flat.StalkFibreQuotient` | The stalk fibre as a quotient by the original contracted prime. |
| C6d | `Flat.FibreRegularityAtStalk` | Transport of the specified fibre equations to that stalk fibre. |
| C6e | `Flat.NoetherianFibreCIFlat` | Global flatness from regularity at fibre points on the zero locus. |
| C6f | `MvPolynomial.NoetherianFibreQuotientFlat` | The criterion in finite polynomial coordinates over a Noetherian base. |

Every leaf is a new module of at most 150 lines. The verification entry points
are `W49_VALIDATE.py` (individual foreground builds and module-only lint),
`W49_AXIOMS.lean` (all new declarations), and `W49_BOUNDARY_AXIOMS.lean`.
The untracked `FAMILY_W49_DONE.md` records checked-at timestamps, source hashes,
commits, and the required post-merge root build.

### Remaining formal-smoothness boundary

C4–C6 do not prove that a finite coefficient stage inherits the required
fibre regularity. C7 still needs principal-localization data, C8 must spread
fibre regularity to a suitable Noetherian stage, and C9–C10 must construct
and use the varying-stage comparison to obtain arbitrary-base flatness.
The general C6 ambient-algebra criterion applies to a Noetherian principal
localization when its fibre condition is supplied; the coefficient-stage
and lifted-chart comparisons must still supply that condition.

C11–C12 must transfer regularity through the nilpotent coefficient kernel
and prove the actual lifted charts flat before W42's cover assembly applies.
Local point lifts, compatible overlaps, descent, nilpotent iteration, and
later family-realization obligations remain. No new theorem in W49 asserts
formal smoothness or removes the existing `mem_isCompatible` admission.

## W50: zero-dimensional approximation and the actual lifted flat chart cover

The finite division charts admit a shorter route through the C8–C10 gate:
all their fibres have dimension zero, and their presentations are square.
The new proof uses that specialization; it does not assert the general
positive-dimensional version of C8b. Each module below is capped at 150
lines. Validation commands, checked source hashes, axiom results and local
commits are recorded in the untracked `FAMILY_W50_DONE.md` and
`W50_VALIDATION.json` handoff artifacts.

### Coefficient stages and dimension

C7 is completed by `Localization.PrincipalBaseChangeEquiv`,
`MvPolynomial.PrincipalRelationBaseChange`, and
`MvPolynomial.NoetherianPrincipalStage`. Relations and the principal
denominator descend simultaneously. Tensor base change reconstructs the
actual localized quotient and preserves every polynomial representative.
W48's coefficient-identity reflection still applies to this finite data.

C8a is proved in `KrullDimension.IntegralExtension`,
`TensorProduct.IntegralMap`, `KrullDimension.FieldBaseChange`, and
`KrullDimension.FibreFieldExtension`. Going up lifts finite prime chains;
incomparability bounds them in the other direction. Noether normalization
remains integral and injective after tensoring with a field extension.
Consequently finite-type Krull dimension, including the zero ring case,
is invariant under arbitrary field extension. The residue-field comparison
uses the prime actually contracted along the coefficient-stage map.

For C8b, `QuasiFinitePrincipalNeighbourhood` uses Mathlib's proved Zariski
main theorem to produce a principal quasi-finite neighbourhood.
`ZeroDimensionalFibreNeighbourhood` supplies its hypothesis from the
dimension of the **whole residue fibre** at the contracted base prime.
It does not substitute the dimension of a local ring for dimension near
a fibre point: for example, the generic stalk of an affine line has
dimension zero, although every nonempty open of that line has dimension
one. `KrullDimension.QuasiFiniteBound` also supplies the general dimension
bound for a quasi-finite algebra over a polynomial ring; constructing that
polynomial map near a point of a positive-dimensional fibre remains open.

C8c's zero-dimensional application is in `QuasiFiniteBaseChangeFibre`,
`FiniteImagePrincipalCover`, and `QuasiFiniteImageCover`. A quasi-finite
final base change gives dimension-zero stage fibres at the primes seen
by that final base. Principal neighbourhoods at those points have a finite
subfamily whose images generate the unit ideal in the final algebra.
Primes outside that image are not assumed good.

C8d is in `MvPolynomial.EnlargedCoefficientStage`,
`Ideal.QuotientUnitCertificate`, and `MvPolynomial.UnitIdealCertificateStage`.
The proof lifts the equation for a quotient cover, adds the coefficients
of the relation-ideal membership witnesses, and enlarges the original
finitely generated integer subalgebra. Injectivity of the coefficient map
reflects the polynomial certificate. The strengthened statement retains
the canonical images of the originally chosen relations and opens.

C8e's zero-dimensional assembly is in `QuasiFiniteUnitCover`,
`QuasiFiniteCertificateStage`, and `NoetherianQuasiFiniteStage`.
Good principal charts remain quasi-finite after coefficient base change;
the descended unit-ideal certificate makes them a cover of the enlarged
stage. Thus the enlarged Noetherian relation quotient is itself
quasi-finite. This property is proved, not included as a field in an
approximation record. The finite-variable index may be in `Type`; the
coefficient ring is universe-polymorphic.

### Flatness and the lifted cover

`NoetherianQuasiFiniteSquareFlat` uses the finite-fibre kernel parameter
criterion to prove regularity of the specified square equations at every
residue-fibre prime, then applies W49's Noetherian flatness theorem.
`QuasiFiniteSquareFlat` obtains a good Noetherian stage from C8e and
transports its flatness through the exact relation-base-change equivalence.
This proves arbitrary-base flatness of quasi-finite square quotients.
For this route, a directed-colimit comparison (C9/C10a–b) is unnecessary:
one flat stage reconstructs the entire fixed finite presentation after
base change. The general colimit statements have not been implemented.

C11/C12 are instantiated by `LiftedPresentationQuasiFinite` and
`LiftedSquarePresentationFlat`. Every residue field kills the nilpotent
coefficient kernel, so W43's exact presentation-fibre comparison proves
quasi-finiteness of the actual lifted equations. Arbitrary-base square
flatness then proves those equations define a flat algebra upstairs.

`RelationQuotientPresentation` and `PrincipalSquarePresentation` retain
the original principal chart by adding one inverse variable and one
relation. They convert d equations in d localized polynomial variables
into d+1 equations in d+1 polynomial variables. This includes the
principal denominator in the presentation before lifting it.

`LiftedSquareChartCover` proves faithful flatness of the finite product
using the original reduced covering condition. `LiftedPrincipalSquareCover`
constructs the square presentations and coefficient lifts, proves this
faithful flatness, and supplies the exact tensor-reduction equivalences.
Finally `DivisionLiftedFlatCharts.exists_division_lifted_flat_charts`
applies these constructions to W48's original division pullback, without
asking the caller for chart presentations, regularity, or lifted flatness.
Its witnesses retain the original quotient map, denominators, chart
presentations, lifted equations and reduced-chart equivalences. W42's
`exists_point_on_lifted_reduction` transfers original division points to
these particular reduced charts with their coordinate composites intact.

### Remaining formal-smoothness boundary

The lifted flat cover does not supply local inclusion lifts of the
p-divisible-system points. Those must still be constructed and compared
on the actual double and triple overlaps. W41's cotangent/Amitsur
correction theorem must then be applied to those discrepancies, followed
by affine point descent and nilpotent iteration (L7b.4/L8–9). Formal
smoothness, the later cotangent/duality/period gates, and the replacement
of `IsHardlyRamified.mem_isCompatible` remain unproved. The existing
admission module is unchanged, as required by this task's edit boundary.

## W51: local inclusion lifts, actual overlap correction, and formal smoothness

The W50 boundary is resolved by the following capped leaves. Every module
below has at most 150 lines. The proofs use the original level coordinate
maps throughout; they introduce no hypothesis asserting liftability,
formal smoothness, or existence of a correcting cochain.

| Leaf | Modules | Proof obligation |
|---|---|---|
| L7b.4a | `LiftedPresentationPoint`, `PrincipalDivisionPoint` | Preserve C-coefficients and the original reduction-map composite when transferring a principal division-chart point through W42's specified presentation equivalence. |
| L7b.4b | `FiniteProductReductionPoint`, `DivisionLiftedReductionPoint` | Assemble those points on the actual tensor reduction of W50's faithfully flat product cover. |
| L7b.4c | `DivisionLocalInclusionLift` | Lift the p-power multiple of that division point across the square-zero cover reduction; the original reduction/inclusion equation identifies its reduction with the required inclusion of the original point. |
| L8a | `FlatCoverPointOverlap`, `FlatCoverDiscrepancyCocycle` | The actual local lift has equal reductions on double overlaps. Its three actual pullbacks satisfy the triple-overlap group/tangent identity. |
| L8b | `FlatCoverKernelAmitsur`, `FlatCoverKernelDifferential`, `PointDifferenceCotangentEvaluation` | Identify the double-overlap kernel with D tensor D tensor J, retain coordinate evaluations, and intertwine both Amitsur differentials with the actual overlap maps. |
| L8c | `FlatCoverCotangentDiscrepancy`, `FlatCoverAugmentationMap`, `PDivisibleOverlapCorrection` | Construct the cotangent-valued discrepancy, prove its Amitsur cocycle equation, and apply W41's `exists_original_infinitesimal_correction` to this particular cocycle. |
| L8d | `InfinitesimalPointCorrection`, `PDivisibleCorrectedLocalPoint` | Translate by the correcting point to obtain equal overlap pullbacks without changing the original reduction. |
| L9a | `PDivisibleLocalLiftDescent`, `PDivisibleSquareZeroFormalSmoothness` | Faithfully flat affine descent gives a global inclusion lift; consequently the original point colimit is surjective across square-zero thickenings of p-nilpotent algebras. |
| L9b | `PDivisiblePointEquiv`, `PDivisibleFormalSmoothness` | Iterate along nilpotent ideals and transport through the original quotient-kernel equivalence, retaining an explicit higher-original-level inclusion lift. |
| Cotangent identification | `PDivisibleInfinitesimalPairing`, `PDivisibleFormalCotangent`, `PDivisibleNilpotentCotangent` | Identify the actual colimit infinitesimal kernel with Hom from the original cotangent inverse limit, with every original finite-level pairing and independence of the chosen annihilating power. |

### Precise lifting theorem

`PDivisibleSystem.pointColimitMap_surjective_nilpotent` proves that, for
an original system X over the local base R and every surjective R-algebra
map q : B -> C with nilpotent kernel and nilpotent p in B, the induced map
`X.PointColimit B -> X.PointColimit C` is surjective.
`exists_nilpotent_inclusion_lift` states the equivalent original-level
result: each point x at level n has a lift y at some level m >= n with
`q.comp y = x.comp (X.inclusion h).toAlgHom`.

The square-zero proof constructs W50's cover internally, transfers its
specified division point, and applies the multiplication lift on the
original higher level. It then forms that lift's discrepancy, verifies
its triple-overlap identity, and identifies its actual kernel-valued
cotangent cocycle. W41's Amitsur theorem produces a correcting original
level point. Translation gives equal overlaps, and faithfully flat point
descent returns a point over B with the prescribed reduction. Nilpotent
iteration uses successive square-zero quotients and actual test-algebra
composition. It does not assume a smooth representing algebra.

### Precise cotangent identification

`formalInfinitesimalCotangentEquiv` identifies the actual augmentation
kernel of the same original point-colimit functor across q with
`X.cotangentLimit ->ₗ[R] RingHom.ker q`, when q has square-zero kernel
annihilated by a power of p and the original level cotangent sets are
finite. `formalInfinitesimalCotangentEquiv_mk` retains the original
coordinate cotangent functional composed with `X.cotangentEval n` for
**every** original level n. The equivalence is independent of the
annihilating power, not merely an equivalence for one chosen level.

`nilpotentInfinitesimalCotangentEquiv` obtains the exponent internally
from p-nilpotence of B. At the original rational place,
`rationalPlaceFormalInfinitesimalCotangentEquiv` discharges finite-level
finiteness using the previously proved theorem. Thus this identification
has no extra finiteness premise for that original base.

### Boundary after these leaves

These statements prove formal smoothness in the equivalent original
level-system sense requested in W37's first obligation, and identify its
infinitesimal functor with the existing cotangent limit. They do not
construct a complete representing coordinate algebra, nor prove that
the cotangent limit is torsion-free or finite free. The later dual
reduction, Cartier-dual limit, period pairing, and family-realization
gates remain. In particular the existing `mem_isCompatible` admission
is not replaced; its module is outside this task's edit boundary.

Recheck the implementation with the foreground module builds, individual
module lints, and named axiom audits recorded in `FAMILY_W51_DONE.md`.
The handoff records timestamps, commits, and the post-merge root build;
this section specifies the theorem boundary rather than a live CI status.

## W52: cotangent freeness and reduction of the original integral tangent

The first two obligations after W51 are proved. Formal smoothness is applied
to actual split square-zero test algebras to obtain functional lifting;
freeness is a consequence, never a hypothesis in the system-level results.
Every new module below is capped at 150 whole-file lines.

| Leaf | Module | Proved output |
|---|---|---|
| F1 | `AugmentationCotangentNaturality` | Changing test algebras postcomposes the original cotangent functional with the specified reduction-kernel map. |
| F2 | `PDivisibleCotangentKernelLifting` | W51's nilpotent lifting theorem lifts every represented kernel-valued functional across a surjective square-zero map of test algebras. |
| F3 | `Mathlib.RingTheory.SplitSquareZeroTest` | The kernel of S plus M is M; module surjections give surjective algebra maps with square-zero kernel, preserving p-nilpotence. |
| F4 | `PDivisibleCotangentFunctionalLifting` | For every p-nilpotent R-algebra S and every surjection of S-modules M to N, each R-linear functional from the original cotangent limit to N lifts to M. |
| F5 | `Mathlib.RingTheory.PrincipalPowerTorsion` | In a free module over R/(a^(n+1)), a-torsion is divisible by a^n, by cancellation in the domain R. |
| F6 | `PDivisibleCotangentPrimeInjective` | Functional lifting into free modules over R/(p^(n+1)) proves multiplication by p injective on the original cotangent inverse limit. |
| F7 | `PDivisibleCotangentFree` | DVR factorization gives torsion-freeness; prior finite generation gives finite freeness, also at the original rational place. |
| D1 | `Mathlib.LinearAlgebra.FreeDualReduction` | The integral dual of a free module modulo a is all R/(a)-valued functionals, with the original evaluation formula. |
| D2 | `PDivisibleIntegralTangentReduction` | The original integral tangent modulo p^n is all functionals on the original level-n cotangent, equivalently its already defined Leibniz tangents. |
| D3 | `PDivisibleIntegralTangentReductionNaturality` | Reduction preserves original system maps and is independent of the auxiliary base identification; includes the original rational-place pairing. |
| D4 | `PDivisibleIntegralTangentCoefficients` | Tensoring the integral tangent with any coefficient module gives all cotangent-limit functionals, and all original level functionals for p-power torsion coefficients. |
| D5 | `PDivisibleIntegralInfinitesimal` | Tensoring the integral tangent with an actual square-zero reduction kernel represents the actual original infinitesimal point colimit and retains its finite-level pairing. |
| D6 | `PDivisibleIntegralPairingPerfect` | The original integral evaluation pairing is perfect; the cotangent is its tangent's full integral dual. |

### Why infinitesimal lifting proves torsion-freeness

Let x in the original limit satisfy p*x = 0. At each n, equip the original
level-(n+1) cotangent with its R/(p^(n+1))-action and choose a finite free
surjection onto it. F4 lifts the original evaluation map through that
surjection. The lifted image of x is killed by p. Coordinate cancellation
in F5 makes it divisible by p^n. Its image in the original level-n
cotangent therefore vanishes. The original inverse-limit extensionality
then gives x = 0. Factoring every nonzero p-adic scalar as a unit times a
power of p proves full torsion-freeness. This argument constructs no
complete representing coordinate algebra and needs none.

The dual reduction comparison sends the class of an integral functional d,
evaluated on the original level-n image of x, to d(x) modulo p^n. Its
surjectivity follows from the proved cotangent freeness. For arbitrary
module coefficients M, the tensor comparison sends d tensor a to the
functional x ↦ d(x)*a. W51's identification then gives the actual
infinitesimal-point comparison for every square-zero reduction with
p-nilpotent source. These are integral tangent statements; they do not
identify Tate sequences with a period-module basis.

### Remaining Cartier and period boundary

The W29 D2 contracts still require a Cartier-dual level system and a period
comparison. In particular, `RaynaudCartierDual` supplies individual local
Cartier-dual models and transposed maps, but does not assemble a dual
`PDivisibleSystem`. Several existing extension-duality theorems concern
`FiniteFlatObject` with generic field Q, so they cannot be applied to the
original rational-place completion without proving the corresponding local
statements. The next proof-sized split is:

| Next leaf, cap 150 each | Required artifact |
|---|---|
| C1 | Transpose the original reduction/inclusion maps; prove identity, composition and both multiplication factorizations on the actual dual coordinate algebras. |
| C2 | Prove dual closedness and faithful flatness over the local base, including the actual residue-base-change maps. |
| C3 | Prove the actual dual augmentation-kernel equation, annihilation and coordinate rank; assemble the dual p-divisible system. Split this leaf further before exceeding the cap. |
| C4 | Construct the dual Tate limit, its original transition/evaluation pairings and compatibility with integral tangent coefficient extension. |
| P1 | Construct the period pairing from these particular points and the existing period rings; prove its coefficient and level compatibilities. |
| P2–P6 | Prove integrality, original Galois equivariance, injectivity, surjectivity and filtration strictness, respectively; each remains a separate proof obligation. |
| W1–W3 | Prove coefficient-embedding decomposition, the two-weight support and the determinant calculation forcing rank one in each prescribed degree. |

No record introduced here assumes a comparison isomorphism or any of these
remaining conclusions. `IsHardlyRamified.mem_isCompatible` is unchanged
and still has the existing admission. The later compatible-family
realization and the final delegation of that admission remain outstanding.

Validation is reproducible with the individual foreground builds, sequential
module-only lints and named axiom audits recorded in the untracked
`FAMILY_W52_DONE.md`, `W52_VALIDATION.json` and `W52_AXIOMS.log`.

## W53: actual Cartier-dual system and Tate evaluation

The W52 C1–C3 obligations are implemented over a principal domain with an
arbitrary characteristic-zero fraction field. They therefore apply to the
original rational-place completion. No generic-Q extension theorem is used
to assert local exactness. The complete modules below each have a 150-line cap.

| Leaf | Module | Proved output |
|---|---|---|
| C1a | `CartierDualConvolution` | Transposition reverses composition and preserves convolution and its natural powers. |
| C1b | `RaynaudCartierArithmetic` | Actual integral duals preserve multiplication, annihilation and coordinate rank. |
| C1c | `PDivisibleCartierTransitions` | The original transposed inclusions/reductions satisfy identity, composition and both multiplication factorizations. |
| C2 | `CartierDualSurjection` | A surjective coordinate map has faithfully flat transpose, using split injectivity after every residue base change. |
| C3a | `HopfExactPair` | An actual augmentation-kernel presentation gives the original kernel torsor and its faithfully flat invariants. |
| C3b | `HopfExactPairAnnihilator` | The annihilator of the actual dual augmentation ideal is exactly the original quotient coordinates. |
| C3c | `HopfExactPairDualKernel` | The dual augmentation quotient is flat and pairs perfectly with the original quotient coordinates. |
| C3d | `HopfExactPairDuality` | Integral biduality identifies that quotient with the intended dual; proves dual closedness and the actual dual kernel equation. |
| C3e | `PDivisibleCartierSystem` | Assembles the actual dual p-divisible system with all structure obligations proved. |
| C4a | `CartierPairingNaturality` | Geometric evaluation tensors and characters respect transposition of the given Hopf maps. |
| C4b | `RaynaudCartierPairing` | The specified original and dual local point groups carry their actual Cartier pairing, natural for integral maps. |
| C4c | `RaynaudCartierPairingLaws` | Additivity in original points and the actual annihilating exponent of each Cartier value. |
| C4d | `RaynaudCartierPairingGalois` | Original local Galois equivariance of that pairing. |
| C4e | `PDivisibleCartierTatePairing` | The dual Tate limit, its p-adic linear evaluations, inclusion compatibility, and the paired cyclotomic transition law. |
| C4f | `PDivisibleCartierTateGalois` | The actual paired sequence lies in the inverse limit of p-power roots and is Galois equivariant. |
| C4g | `PDivisibleRationalCartier` | Instantiates the actual rational-place dual system and applies the proved integral tangent coefficient comparisons to its own cotangent limit. |
| C4h | `RaynaudCartierCharacters` | The actual dual point group is the full character group; finite evaluation is additive in both arguments and separates dual points. |

The finite exactness proof takes the original coordinate maps, surjectivity,
faithful flatness and augmentation-kernel equation. It introduces no new
record assuming a dual extension or a comparison. Faithfully flat descent
identifies original quotient coordinates as kernel invariants. Their pairing
with the dual augmentation quotient is perfect. That quotient is finite
projective because the transposed inclusion is faithfully flat; integral
biduality then proves both dual closedness and the required equality of ideals.

For a dual Tate vector y and an original Tate vector x, the value at level n
is the original Cartier evaluation on their actual n-th coordinates. It is
killed by p^n, and raising its level-n value to p^(n-m) gives its level-m
value. The same evaluation on a fixed original point is unchanged by its
inclusion into a higher level. Galois acts on these values through its
original action on the algebraic closure of the actual fraction field.

### Remaining C4 and period boundary

The root-valued Tate pairing and the integral tangent coefficient pairings
are proved separately. Their infinitesimal compatibility has **not** been
proved. Applying W52 to the dual system gives its integral coefficient
comparison; it does not identify a Tate vector with an integral tangent
functional. Consequently C4 as a whole, the period comparison and the family
admission remain open. The original `mem_isCompatible` module is unchanged.

The next required refinement, with each complete module still capped at 150
lines, is:

| Next leaf | Required artifact |
|---|---|
| C4i | Extend actual finite Cartier characters from generic points to the appropriate integral test algebras, retaining the original coordinate maps. |
| C4j | Extract their infinitesimal differential/logarithmic derivative and prove independence of representatives and compatibility with the original level transitions. |
| C4k | Identify that differential with the already proved original integral tangent coefficient evaluation; establish the level/limit formula. |
| P1a | Construct the period-valued map from those specific Tate vectors and the existing period rings, with the original rational-place field and Galois transport. |
| P1b | Prove independence and coefficient/level compatibility of the period construction. |
| P2–P6 | Integrality, original Galois equivariance, injectivity, surjectivity and filtration strictness, separately. |
| W1–W3 | Coefficient-embedding decomposition, two-weight support and determinant rank-one calculation, followed by compatible-family realization. |

The untracked `FAMILY_W53_DONE.md` records the checked commits and evidence.
Recheck with the individual foreground builds, module-only lints and named
axiom audit listed there. No period comparison or removal of the existing
admission is claimed by these finite and Tate-level constructions.

## W54: integral test characters, their differential, and actual root periods

Every complete new module below is capped at 150 lines. No existing proof
module is edited. C4i–C4k now have original-coordinate constructions and
finite/limit evaluation formulas. A separate construction sends the original
Cartier root sequences into the existing de Rham period ring. **The equality
between the period's first-order term and the integral cotangent construction
is still unproved.** Consequently the full P1 comparison and P2–P6 are not
claimed, and `mem_isCompatible` retains its existing admission.

| Leaf | Module | Proved output |
|---|---|---|
| C4i.1 | `CartierTestAlgebra` | Canonical dual tensors for arbitrary integral test algebras; multiplicative Cartier characters valued in actual units. |
| C4i.2 | `CartierTestNaturality` | Basis-independent evaluation, original coordinate-map naturality and equality with the existing geometric character. |
| C4i.3 | `CartierTestCoefficients` | Coefficient specialization and original transposed morphisms preserve characters. |
| C4i.4 | `CartierTestBaseChange` | Original dual bases and Cartier evaluation commute with scalar extension. |
| C4i.5 | `RaynaudGeometricIntegralPoints` | Every specified geometric point extends uniquely to the actual integral closure; no lifting hypothesis. |
| C4i.6 | `RaynaudIntegralCartier` | Actual local dual points give integral test characters whose generic values equal the original finite pairing. |
| C4j.1 | `CartierCotangentTensor` | Canonical original-coordinate representing element and actual augmentation-cotangent tensor; contraction differentiates evaluation. |
| C4j.2 | `CartierSquareZeroDifferential` | Character minus one equals the linear logarithmic differential on every square-zero point; values lie in the actual reduction kernel. |
| C4j.3 | `CartierDualElementNaturality` | Coordinate and coefficient transport of representing elements and cotangent tensors. |
| C4j.4 | `FiniteFlatCartierDifferential` | The original model morphisms preserve the dlog tensors and tangent contractions. |
| C4j.5 | `PDivisibleCartierDlogLimit` | Actual dual Tate vectors give coherent integral dlog tensors under the original cotangent restrictions, with coefficient compatibility. |
| C4k.1 | `PDivisibleCartierDifferential` | Original W52 integral tangent coefficient contraction equals the actual differential; limit representatives exist and contraction is independent of them. |
| C4k.2 | `PDivisibleCartierDlogPairing` | Instantiates that equality and the square-zero character formula on the specified actual dual Tate coordinates. |
| P1 roots | `PDivisibleRationalCartierRoots` | Original rational-place roots become integral C_p roots, a compatible perfection sequence and a sharp-one element of the existing tilt. |
| P1 logarithm | `ComplexSharpOneLog` | Any specified sharp-one tilt element has an actual convergent de Rham logarithm, finite truncations, first-order formula and Galois transport. |
| P1 values | `PDivisibleRationalCartierPeriods` | Period values of pairs of original Tate vectors, finite-precision formulas, uniqueness and first-filtration membership. |
| P3 values | `PDivisibleRationalCartierPeriodGalois` | Original local Galois equivariance through the fixed rational-place transport, from roots through tilt to actual period values. |

The dlog output is a coherent sequence of **cotangent tensors**. Its
contraction with integral tangents is proved; it is not asserted to be an
integral tangent vector. Similarly, the period output is a value attached
to two Tate vectors. Linearity in those vectors, a comparison isomorphism,
and any identification of its kernel or image are not inferred from the
existence of that value.

### Remaining proof obligations, in order

| Next capped leaf | Required artifact |
|---|---|
| P1c | Prove additivity and p-adic linearity of the actual Tate dlog/period constructions, including any completion needed in the integral cotangent target. |
| P1d | Construct the period-to-cotangent first-order identification for these specific original Tate vectors; show the Teichmuller linear term contracts to the C4k integral pairing. This is the next comparison gap. |
| P1e | Assemble the required one-vector comparison map from that identification, with coefficient and original level compatibility. |
| P2 | Prove the lattice/integrality statement for that comparison. Integral roots and first-filtration membership of their logarithm do not establish this statement. |
| P3 | Lift the proved equivariance of root period values to the actual comparison map. |
| P4–P6 | Prove comparison injectivity, surjectivity and filtration strictness separately. |
| W1–W3 | Coefficient-embedding decomposition, two-weight support and determinant rank-one calculation, then compatible-family realization. |

The finite cotangents are p-power torsion. Scalar extension directly to a
ring in which p is invertible therefore loses their tangent information.
The integral inverse limit and its coefficient completion must precede
rationalization; the root-period construction alone does not supply that
comparison.

Only an axiom-clean replacement permits the later delegation of the
existing admission, whose module is outside this task's edit scope.
Validation evidence and exact local commits are in the untracked
`FAMILY_W54_DONE.md`, with reproducible per-module builds/lints and named
axiom audits. No whole-library lint is used.

## W55: integral coefficient completion and p-adic linearity

P1c now has an integral coefficient comparison and proved linearity for both
actual Tate constructions. The complete new modules listed below are each
at most 150 lines. The period/cotangent first-order identification P1d is
still open; neither that comparison nor removal of `mem_isCompatible`'s
admission follows from linearity.

| Leaf | Module | Proved output |
|---|---|---|
| P1c.1 | `PDivisibleCotangentTensorReduction` | Tensor right exactness identifies the original finite cotangent tensor with the p-power quotient of the integral limit tensor, for arbitrary coefficient algebras; no flatness hypothesis. |
| P1c.2 | `PDivisibleCotangentTensorCompletion` | The actual coherent cotangent tensors are linearly equivalent to the p-adic completion of the integral coefficient tensor; completed dlog recovers every original finite tensor and is unique. |
| P1c.3 | `PDivisibleCompletedDlogCoefficients` | The standard adic completion of coefficient specialization preserves the actual completed dlog and every original finite evaluation. |
| P1c.4 | `CartierDualElementMultiplication` | Integral biduality identifies convolution with multiplication of original representing tensors, with augmentation one. |
| P1c.5 | `CartierDlogAdditivity` | The integral augmentation differential satisfies tensor Leibniz; actual dual-point convolution adds dlog tensors. |
| P1c.6 | `RaynaudIntegralPointAddition` | Unique integral extensions preserve original point addition and the identity. |
| P1c.7 | `PDivisibleCartierDlogAdditivity` | Actual finite, coherent and completed Tate differentials are additive maps. |
| P1c.8 | `PDivisibleCartierDlogLinearity` | Finite p-power annihilation and actual p-adic residues prove semilinearity under the specified base identification, also in the completed integral tensor. |
| P1c.9 | `PDivisibleCartierPairingBilinear` | The original finite Cartier pairing and its original Tate evaluations are additive in both variables. |
| P1c.10 | `PDivisibleCartierPairingScalars` | P-adic scalars act by the actual finite residue exponent in either argument; the root pairing is p-adically balanced. |
| P1c.11 | `NilpotentLogProduct` | Finite logarithms of products add in a principal nilpotent ideal, proved by formal-series evaluation. |
| P1c.12 | `ComplexSharpOneLogAdditivity` | Actual sharp-one logarithms add on products in the existing de Rham ring, using its finite theta quotients. |
| P1c.13 | `PDivisibleRationalCartierPeriodAdditivity` | Original roots, tilt elements and logarithmic periods respect addition in both original Tate vectors. |
| P1c.14 | `ComplexRootSequenceShift` | Shifts of arbitrary actual integral root sequences retain the original sharp values and p-power identities. |
| P1c.15 | `ComplexRootPowerBounds` | Original rootwise power equalities give integral p/theta precision bounds before inverting p. |
| P1c.16 | `ComplexRootPowerConvergence` | These bounds prove convergence of integer powers in integral theta quotients and the existing finite de Rham quotients. |
| P1c.17 | `ComplexRootLogLinearity` | Actual rootwise p-adic exponentiation multiplies the convergent logarithm by the existing p-adic scalar embedding. |
| P1c.18 | `PDivisibleRationalCartierPeriodLinearity` | The actual original period pairing is p-adic bilinear, with the original rational-place transport. |

The completion comparison uses finiteness of the original level cotangent
sets. This is already proved for a base identified with Z_p by
`levelCotangent_finite_of_equiv`, including the actual rational place.
It does not assert that an uncompleted tensor is complete, nor does it
extend an individual torsion cotangent to a ring where p is invertible.

### Remaining work, in order

| Next capped leaf | Required artifact |
|---|---|
| P1d.1 | Construct the integral theta/p-power square-zero coefficient thickenings and their maps from the original rational-place base; verify the actual reduction kernels and nilpotence. |
| P1d.2 | Use original finite-level formal smoothness to construct compatible integral/infinitesimal lifts of the specified Tate points in these thickenings. Existing `exists_nilpotent_inclusion_lift` supplies individual higher-level lifts, not the required simultaneous compatibility. |
| P1d.3 | Evaluate the original Cartier characters on those lifts and identify the resulting first-order Teichmuller term with the C4k integral cotangent contraction; prove independence of lifts and passage through the coefficient completion. |
| P1e | Assemble the one-vector comparison with coefficient, original-level and transport compatibility. A bilinear period value is not this comparison. |
| P2–P6 | Comparison integrality, original Galois equivariance, injectivity, surjectivity and filtration strictness. |
| W1–W3 | Coefficient-embedding decomposition, two-weight support, determinant rank-one calculation and compatible-family realization. |

Only then can the existing family admission delegate to an axiom-clean
replacement. Its module remains outside this task's permitted edit scope.
The untracked `FAMILY_W55_DONE.md` records checked commits and reproducible
validation; `W55_FINAL_CHECKS.py` checks the source hashes, individual
build/lint records, named axiom audit, line caps, edit scope and merged root
build. No whole-library lint is used.

## W56: integral thickenings and simultaneous original Tate lifts

P1d.1 and P1d.2 are now constructed. For every positive theta order r and
p-power precision s, the coefficient ring is the actual
`Ainf p / (ker(theta)^r + (p^s))`. Its theta reduction onto `O_C/(p^s)`
is surjective with kernel the image of the original theta kernel, whose
r-th power vanishes. Each positive single theta or p step is square-zero;
rectangular reductions between positive precisions have nilpotent kernels.
The original rational-place base acts through its fixed integral p-adic
identification, and all coefficient squares commute over that base.

The canonical square-zero convolution lift descends through the original
finite-level inclusions to the point colimit. Its composites with reduction
are both multiplication by the annihilating p-power. Shifting inverse-p
sequences therefore proves unique simultaneous lifting. Induction through
nilpotent ideals extends this to all positive theta orders. Applying this
to the uniquely extended original integral Tate coordinates gives lifts
compatible in theta precision, p precision and Tate index. At first order,
the n-th lifted coordinate has an explicit representative at original
level n+s. It is not asserted to stay at level n.

The zeroth lifted coordinate is an actual infinitesimal point. The existing
original cotangent equivalence now supplies its integral tangent tensor
and cotangent functional, with the same evaluation pairing and compatibility
under p-precision reduction. This constructs the infinitesimal input to the
comparison; its equality with the original Teichmuller/logarithmic period
is still unproved.

| Capped leaf | Module | Proved output |
|---|---|---|
| P1d.1a | `IntegralThickeningReduction` | Exact quotient reduction kernels and power containment criterion. |
| P1d.1b | `ComplexIntegralThickening` | Actual two-precision rings, surjective theta, exact kernel and nilpotence. |
| P1d.1c | `ComplexThickeningTransitions` | Rectangular compatibility, nilpotence and individual square-zero steps. |
| P1d.1d | `RationalPlaceThickening` | Original-base algebras and commuting maps, with proved kernel annihilation. |
| P1d.2a | `PDivisiblePointMultiplication` | Original multiplication on the actual point colimit. |
| P1d.2b | `ShiftLimitEquivalence` | An inverse up to a finite shift gives an equivalence on compatible sequences. |
| P1d.2c | `PDivisibleSquareZeroColimitLift` | Canonical multiplication lifts and both reduction identities. |
| P1d.2d | `PDivisibleUniversalCover` | Unique compatible inverse-p lifts across square-zero reductions. |
| P1d.2e | `RationalPlaceIntegralCoefficients` | The original closure transport maps actual integral coefficients into O_C. |
| P1d.2f | `PDivisibleIntegralTateCover` | Specified original Tate vectors give integral inverse-p sequences. |
| P1d.2g | `RationalPlaceTateThickeningLift` | Actual first-order Tate lifts, finite representatives and p-precision compatibility. |
| P1d.2h | `PDivisibleNilpotentUniversalCover` | Unique compatible lifting through arbitrary nilpotent reductions when p is nilpotent. |
| P1d.2i | `RationalPlaceTatePrecisionLift` | Simultaneous original Tate lifts at every positive theta order. |
| P1d.3a | `PDivisibleTateInfinitesimal` | The zeroth lifted coordinate is genuinely infinitesimal. |
| P1d.3b | `RationalPlaceTateInfinitesimal` | Its actual original integral tangent tensor and cotangent functional, retaining the pairing. |
| P1d.3c | `PDivisibleInfinitesimalNaturality` | Cotangent extraction commutes with maps of coefficient kernels. |
| P1d.3d | `RationalPlaceTateCotangentPrecision` | The actual Tate cotangent functionals form a compatible integral system. |

### Remaining work, in order

1. P1d.3: evaluate the original dual characters on the constructed
   infinitesimal Tate points and identify the original Teichmuller linear
   term with the cotangent contraction. Prove the coefficient-completion
   passage. No coefficient section `O_C → Ainf/(ker(theta)^2,p^s)` is assumed.
2. P1e: prove additivity and p-adic linearity in the Tate argument, then
   assemble and identify the period comparison from these functionals, with
   original-level and coefficient transport compatibility.
3. P2–P6: comparison integrality, original Galois equivariance, injectivity,
   surjectivity and filtration strictness.
4. W1–W3: coefficient embeddings, two-weight support, determinant rank-one
   calculation and compatible-family realization.
5. Only an axiom-clean replacement permits delegation of the existing
   admission; its module remains outside this task's edit scope.

The untracked `FAMILY_W56_DONE.md` records the local commits and validation;
`W56_FINAL_CHECKS.py` rechecks hashes, line caps, per-module build/lint logs,
axiom coverage, edit scope and the required merged root build. No
whole-library lint is used. The untracked `W56_COMPARISON_PLAN.md` describes
one proposed route for the remaining character calculation; it is not a proof.


## W57: reduced Cartier evaluation and linearity of the actual tangent

The original dual Tate character now has a choice-independent differential
on the actual infinitesimal colimit. Dual coefficients lift linearly by
finite freeness. Their contraction with a kernel-valued tangent is
independent of the lift because the coefficient kernel is square-zero.
Original inclusions preserve the pairing, so every finite representative
computes the same value. This does not assert that a dual character lifts
as an algebra character.

For the actual Tate infinitesimal, the zeroth simultaneous lift has the
specified original level-s representative. Its reduced Cartier value is
contraction of the original integral tangent tensor with any linear lift
of the original dual dlog coefficients. Reduction of those coefficients
is the original dlog tensor.

The canonical square-zero multiplication lift preserves convolution.
Consequently the constructed cotangent functional and integral tangent
tensor are additive in the original Tate vector. At p-precision s they
depend only on its level-s coordinate; residue scalar comparison proves
p-adic linearity over the specified original integral base. P1e's linearity
obligation is proved. Identifying this map with the period comparison is
still part of the open P1d.3 comparison.

Independently, the first-order Teichmuller difference of the original
Cartier roots is now expressed as a^(p^s)-1 for *any* lift a of the original
level-s Cartier value. The reduced finite character is proved to be that
same original Cartier root. These results identify both sides of the
remaining equation; they do not prove equality between the sides.

| Capped leaf | Module | Proved output |
|---|---|---|
| P1d.3e | `CartierLinearEvaluation` | Basis-free linear coefficient pairing and independence on square-zero tangents. |
| P1d.3f | `CartierLinearCotangent` | Lifted cotangent tensor, contraction and reduction to original dlog. |
| P1d.3g | `CartierReducedDifferential` | Existence of linear coefficient lifts and choice-independent differential. |
| P1d.3h | `CartierReducedNaturality` | Original morphism naturality and arbitrary-lift cotangent contraction. |
| P1d.3i | `PDivisibleReducedCartierPairing` | Actual dual Tate differential on the infinitesimal colimit, independent of representative. |
| P1d.3j | `RationalPlaceTateInfinitesimalFinite` | Specified original level-s representative and its cotangent functional. |
| P1d.3k | `RationalPlaceTateReducedCartier` | Reduced original Cartier differential on the constructed Tate point. |
| P1d.3l | `RationalPlaceTateTangentEvaluation` | Its contraction against the actual original tangent tensor. |
| P1d.3m | `ComplexThickeningRootPower` | Any lift of a finite root computes the unshifted Teichmuller value. |
| P1d.3n | `RationalCartierFirstOrder` | Original finite character/root identification and first-order Teichmuller difference. |
| P1e.1 | `SquareZeroPointLiftMultiplication` | Canonical lifts preserve convolution and augmentation. |
| P1e.2 | `InfinitesimalCotangentAddition` | Cotangent extraction takes convolution to addition. |
| P1e.3 | `RationalPlaceTateTangentAdditivity` | Actual Tate cotangent functional and tangent tensor are additive. |
| P1e.4 | `RationalPlaceTateTangentLinearity` | Actual Tate tangent maps are p-adic linear and factor through finite coordinates. |

### W58: the proposed linear-lift calculation is false

W57 proposed proving
`rationalPlaceTateReducedCartier X s y x = rationalCartierFirstOrder X s y x`
by a general convolution/linear-coefficient identity. That supporting identity
is false under its stated square-zero and kernel-annihilation hypotheses.
It must not be used as a proof obligation for the next implementation leaf.

The kernel-checked counterexample uses the constant group of order two over
ZMod 16, with reduction to ZMod 8. Its kernel has square zero and is killed by
two. The original generator already lifts as an algebra point and its square
is the augmentation, so its canonical doubled lift has zero tangent. The
reduced dual character sends the generator to three. Its explicitly
constructed linear coefficient lift really reduces to that algebra character,
but its pairing with the generator has square minus one equal to eight.
`linear_convolution_identity_fails` proves the two proposed sides unequal.
`reducedCharacter_has_no_algebra_lift` also rules out repairing this example
by silently replacing the linear lift with an algebra lift.

The issue is not removed just by requiring two to kill the entire coefficient
ring. `SquareZeroCharacteristicTwoRoot` constructs
B = F₂[T]/(T⁴), J = (T²), q:B → B/J. It proves J² = 0, 2B = 0,
q(1+T)² = 1, and that every lift of this reduced root has square different
from one. Applying the constant order-two group construction to this root
gives the same mathematical obstruction. The module checks these coefficient
and root claims; the full Hopf counterexample module uses ZMod 16 → ZMod 8.

Separately, `rationalPlaceTateReducedCartier_unramified` proves a fact about
the actual rational-place construction: its reduced pairing is zero whenever
the original level-s coordinate algebra is formally unramified. This follows
from uniqueness of lifting over the actual square-zero coefficient kernel,
without any extra assumption about a comparison or a period.

| Capped leaf | Module | Proved output |
|---|---|---|
| W58.1 | `CartierLinearEvaluationBase` | Linear evaluation over the base ring is ordinary dual evaluation. |
| W58.2 | `CartierLinearLiftCounterexampleData` | Actual finite free constant coordinates, square-zero reduction, reduced algebra character and linear lift. |
| W58.3 | `CartierLinearLiftCounterexample` | Failure of the proposed identity and nonexistence of an algebra character lift. |
| W58.4 | `CartierReducedUnramified` | Unramified augmentation points and their reduced Cartier differentials are zero. |
| W58.5 | `RationalPlaceTateReducedUnramified` | The actual rational-place reduced pairing vanishes at unramified levels. |
| W58.6 | `SquareZeroCharacteristicTwoRoot` | A genuine nonlifting quadratic root even with 2B = 0. |

### Remaining comparison work after W58

P1d.3 needs a mathematical redesign before coefficient completion or the
logarithmic period identification can proceed. First check the proposed
specialized equality on the constant étale p-divisible system: the reduced
pairing is zero by the theorem above, whereas its original Cartier roots
are cyclotomic. A complete Lean instantiation of that system and a nonzero
first-order cyclotomic period have **not** been proved in W58. Thus W58
formally refutes the general calculation, not the specialized equality.

A replacement comparison must account for the étale contribution before
claiming equality with the full Cartier period. No corrected identity,
universal-extension construction, or additional comparison hypothesis is
asserted here. P2–P6, W1–W3, the family admission, and the final FLT boundary
remain unfinished. The prior tangent additivity and p-adic linearity results
remain valid but do not resolve this obstruction.

Validation evidence and checked-at times are recorded in the untracked
`FAMILY_W58_DONE.md` and `W58_FINAL_CHECKS.json`; the read-only recheck is
`python3 W58_FINAL_CHECKS.py`. That command checks individual build/lint logs,
source hashes, complete named-declaration axiom coverage, line caps, edit scope,
and the required post-merge root build.

## W59: constant-system calculation and connected levels over the original base

The constant height-one p-divisible system is now constructed at the original
rational place for every `2 < p`. The restriction comes from the existing
integral exactness API; it is not a mathematical restriction on constant
p-divisible groups. Its levels are the actual constant models on
`Z/(p^n)`, including level zero. All coordinate inclusions, reductions,
faithful-flatness statements, kernel equations and ranks are proved.

The compatible residue classes of one and a constructed Cartier-dual Tate
vector pair to the repository's *same chosen* cyclotomic root sequence.
Their logarithmic period is exactly `complexCyclotomicLog p`. At integral
first-order precision s, their period is `[epsilon]-1` modulo
`ker(theta)^2 + (p^s)`. This value is nonzero for some positive s: the
cyclotomic difference is not in `ker(theta)^2`, and that ideal is p-adically
closed by the already proved cyclotomic regularity theorem. Nonvanishing
at every s is neither needed nor asserted.

On these very same Tate vectors, `rationalPlaceTateReducedCartier` is zero
at every precision, because the original coordinate algebras are etale.
`ConstantRationalPower.firstOrder_comparison_fails` therefore refutes the
specialized W57 equality on an actual rational-place p-divisible system.
This strengthens W58's abstract linear-lift counterexample. The nonzero
Cartier period pairs the etale factor with its multiplicative Cartier dual;
it does not assign weight -1 to the constant representation.

### Correct comparison target

Use the connected-etale sequence, retaining the original nonsplit group
and the original Galois action. This sequence is not a direct-product
identification over the original base. The connected part can itself have
both Hodge-Tate weights: connectedness does not mean multiplicative type.
Thus restricting the disproved full-period identity to all Tate vectors
of the connected part is not yet a justified replacement theorem.

The expected covariant Hodge-Tate exact sequence is

```
0 -> Lie(G) tensor C_p(1) -> T_p(G) tensor C_p
  -> (Lie(G^vee))^* tensor C_p -> 0.
```

Both Lie terms must be retained. For the constant etale system the left
term is zero and the degree-zero term accounts for the Tate module; its
dual supplies the cyclotomic pairing. For a connected height-two,
dimension-one group the right term need not vanish. A formula using only
the tangent of G can at most describe the corresponding Hodge-Tate
component after that component has actually been identified. No such
identification is supplied as a constructor field or hypothesis here.

P1d.3 must consequently be split into construction of the Hodge-Tate maps,
proof of their exactness, and compatibility of the Cartier pairing with
both components. The original one-sided equality is retired. The
Hodge-Tate sequence alone also does not prove de Rham admissibility:
the filtered de Rham comparison still requires a period realization, for
example through the universal extension or the Dieudonne crystal.

Source boundary: [T] remains the source for the Hodge-Tate sequence.
A fresh inspection of [BC], pp. 93-95, confirms that Thm. 7.2.8 concerns
full faithfulness and discusses Tate's discovery of the decomposition;
Thm. 7.2.10 gives the Honda classification. Neither is a preexisting
Lean comparison theorem. [BC] Thm. 12.3.2 still uses the crystallinity
input identified above. The exact sequence displayed here is a corrected
mathematical target, not a theorem claimed to have been formalized in W59.

### Original-system connected-etale leaves

Every complete new Lean file remains capped at 150 lines. The component
construction uses the actual rational-place integer ring, not an implicit
identification with Z_3. Its special-fibre ideal is the extension of the
original maximal ideal. Finite flatness gives completeness and Henselian
idempotent lifting; the finite residue algebra is Artinian. These provide
actual connected finite-flat algebra factors. The counit selects one;
inversion and comultiplication descend to it, giving a connected finite-flat
Hopf model with its original closed embedding.

| Leaf / module | Construction and status |
|---|---|
| CE1 / `RationalComponentLifting` | Proved completeness, Henselian lifting and Artinian special fibres over the original base. |
| CE2 / `RationalConnectedComponents` | Constructed the full algebra decomposition into connected finite-flat factors. |
| CE3 / `RationalIdentityComponent` | Constructed the counit-selected identity factor and its actual counit. |
| CE4 / `RationalIdentityComponentAntipode` | Proved antipode stability and the counit kernel condition. |
| CE5 / `RationalIdentityComponentHopf` | Constructed the Hopf quotient, using connectedness of its tensor square. |
| CE6 / `RationalIdentityComponentModel` | Constructed the finite-flat connected model, its closed embedding and injective original point map. |
| CE7 / `BialgebraSurjectiveFactor`, `RationalIdentityComponentMaps` | Descended original morphisms to those same quotient models; proved uniqueness and functoriality. |
| CE8 / `RationalConnectedLevelTower` | Constructed both connected transitions, their coherence, closed inclusions, inherited p-power annihilators and both multiplication factorizations. |
| CE9 / `RationalIdentityMapFaithfullyFlat`, `RationalConnectedKernel` | Proved faithful flatness of the actual connected reductions and their integral scheme-kernel equations. |
| CE10 / `RationalConnectedRanks`, `RationalConnectedSystem` | Proved the common connected height, bounded by the original height, and all level ranks; bundled the original connected p-divisible system. |
| CE11 / `RationalComponentQuotient` | Constructed the original finite-flat quotient by contraction, its faithfully flat projection and its exact connected kernel ideal. |
| CE12 / `RationalComponentQuotientEtale` | Proved finite etaleness over the original base by faithfully descending idempotence of the augmentation ideal. No constant-group replacement is used. |
| CE13 / `RationalEtaleClosed`, `RationalEtaleGenericKernel`, `RationalEtaleKernel`, `RationalEtaleSystem` | Proved closed quotient inclusions for every prime, generic exactness with the actual maps, and integral kernel equations using flatness. Bundled the original quotient system with its proved complementary height. |
| CE14 / `RationalEtaleSystemProjection`, `RationalConnectedEtaleSystemExtension` | Constructed the quotient system morphism and identified its Tate module and projection with the previous original inverse limit. Proved surjectivity, the connected kernel and original Galois equivariance. The level extensions retain the same maps and torsors; no splitting is chosen. |
| HT1 / `RationalConnectedLie`, `RationalPlaceCompletedCotangent`, `RationalPlaceHodgeTateRight` | Partial: identified the original connected Lie module, proved the quotient Lie module is zero, removed integral completion over actual O_C, and constructed the right lattice differential into the dual Lie module of the actual Cartier dual over C_p. W62 proves full C_p scalar extension and original Galois equivariance, constructs the Lie transpose and its positive-twist source action, and proves separation of dual Tate vectors. The left map into the original Tate realization remains open. |
| HT2 / connected comparison | Open: prove the connected Hodge-Tate exact sequence; split kernel, image and dimension arguments. Connectedness alone supplies none of these conclusions. |
| HT3 / full Cartier compatibility | Open: compute the pairing on both Hodge-Tate components and assemble it through CE14. The W59 constant calculation is a required test. |
| DR1 / period realization | Open: construct the universal-extension/Dieudonne period realization with the original generic fibre and filtration. |
| P2-P6 | Open: integrality, original Galois equivariance, injectivity, surjectivity and filtration strictness for that actual de Rham map. |

The existing `PDivisibleSystem.Hom` fixes the same height on source and target.
W60 adds `VariableHeightHom` and constructs the actual connected inclusion
with source height `rationalConnectedHeight`. Its induced Tate map is p-adic
linear and injective. The quotient level ranks are
`p ^ (n * (height - rationalConnectedHeight))`.

Both the connected tower and its original finite etale quotient are now
`PDivisibleSystem`s. Closedness is proved from reflection of the connected
kernel and etale rigidity. Integral exactness uses the proved actual generic
sequence and flatness, rather than inferring it from ranks alone.
The exact inverse-limit sequence was proved directly: finite nonempty fibres
have compatible choices, and levelwise exactness plus injectivity identifies
the kernel with the original connected Tate module. Both maps commute with
the original Galois action. The level extensions and torsor maps retain the
original extension; no product decomposition or section is constructed.

HT1 is partially constructed; HT2-HT3, DR1, P2-P6, W1-W3 and the original
family admission remain open.
The connected-etale exact sequence is not the Hodge-Tate sequence displayed
above. In particular, nothing here restores W57's refuted full-period identity
or establishes de Rham admissibility. No edit of an existing admitted module
is authorized by this task.

Validation, source hashes, exact commits and checked-at times are recorded in
the untracked `FAMILY_W61_DONE.md`, `W61_VALIDATION.json` and
`W61_AXIOM_RESULT.json`. Recheck with `python3 W61_FINAL_CHECKS.py`;
`python3 W61_VALIDATE.py` builds each new module in the foreground and lints
one module at a time. `python3 W61_RUN_AXIOMS.py` audits the new declarations
and the original family boundary. The final root build follows merging
origin/main; no whole-library lint is used.

## W61: original Lie modules and completed right differential

`RationalConnectedCotangentLevels` proves that the actual connected embedding
induces a cotangent isomorphism, because its coordinate kernel is idempotent.
`PDivisibleVariableHeightCotangent` lifts these isomorphisms through the actual
inverse systems. Dualizing gives `rationalConnectedLieEquiv`. The actual etale
quotient has zero cotangent and Lie modules. Neither statement identifies the
connected group with a multiplicative group.

`AdicFiniteFreeCoefficients` proves completeness using finite free coordinates,
without a Noetherian assumption on O_C. The resulting
`rationalPlaceCompletedCotangentEquiv` identifies the completed cotangent tensor
with the actual integral O_C tensor and inverts the canonical completion map.
`rationalPlaceHodgeTateDlogIntegral` retains every original finite Cartier
differential. Only after this completion comparison are coefficients mapped
to C_p, using the fixed original closure transport.

`PDivisibleCartierBidual` constructs the integral system map into the actual
double dual. Composing its Tate map with the differential of the Cartier dual
and the original cotangent/Lie biduality gives
`rationalPlaceHodgeTateRight` on the original Tate lattice. This is a semilinear
lattice map into `(Lie(G^vee))^* tensor C_p`. W62 extends it over C_p and
proves its equivariance as described below. The twisted left map into the
original Tate realization and exactness remain open.
The W59 constant-system counterexample remains a required sanity check.

Read-only evidence for these implementation claims is the W61 source and
per-module logs, checked-at timestamps and axiom coverage in
`W61_VALIDATION.json` and `W61_AXIOM_RESULT.json`; rerun
`python3 W61_FINAL_CHECKS.py` for the source/hash, scope and final-build check.

## W62: full right realization and original Galois equivariance

`RationalPlaceComplexScalarExtension` proves the original integral scalar
identification agrees with the standard Z_p embedding in C_p. It constructs
and characterizes the unique C_p-linear extension of an original semilinear
lattice map. `RationalPlaceHodgeTateRealization` applies this to the actual
right differential and identifies its source with C_p tensor over Q_p of
the rationalized original Tate module. Swapping the target tensor factors
does not replace the original Cartier-dual Lie module.

`RationalPlaceCoefficientGalois` fixes the original integral base inside the
actual coefficient action. `RationalPlaceCartierDlogGalois` proves finite
Cartier-coordinate and differential equivariance. Integral completeness
makes finite evaluations jointly injective, so
`RationalPlaceHodgeTateDlogGalois` carries this identity through the integral
limit and then to C_p. `RationalPlaceHodgeTateRightGalois` proves original
bidual and right-lattice equivariance. `RationalPlaceTateRealizationGalois`
constructs the diagonal action and proves its group and semilinearity laws;
`RationalPlaceHodgeTateEquivariance` proves full right-map equivariance for
both the original local Galois group and its standard Q_p coordinates.

For the left map, `PDivisibleTateEvaluationSurjective` proves unconditional
surjectivity of the original finite Tate evaluations from faithful flatness.
It upgrades finite Cartier separation to separation against actual full
Tate vectors. Separation does not prove perfectness of the scalar-extended
pairing. `RationalPlaceHodgeTateLieTranspose` transposes the actual dlog using
the original Lie-cotangent contraction. Its target is the C_p-dual of the
Cartier Tate realization, not yet the original Tate realization.
`RationalPlaceHodgeTateLieTwist` constructs the original Lie source with its
positive cyclotomic action and proves the group law. It does not assert that
this source embeds into the Tate module.

Remaining HT1 steps are to prove perfect Tate Cartier duality, identify the
positively twisted dual Cartier Tate realization with the original Tate
realization using the actual pairing, and transport the constructed Lie
transpose through that identification. HT2 still needs the kernel, image
and dimension arguments for connected systems and assembly through CE14.
HT3, DR1/P2-P6 and W1-W3 remain open. The original family admission is
unchanged. The W59 constant-system counterexample remains required: an
etale Lie module can vanish while its actual Cartier period is nonzero.

Read-only evidence for W62 is recorded with checked-at times and source
hashes in `W62_VALIDATION.json` and `W62_AXIOM_RESULT.json`, and summarized in
untracked `FAMILY_W62_DONE.md`. Recheck `python3 W62_FINAL_CHECKS.py`;
`python3 W62_VALIDATE.py` builds and lints one new module at a time, and
`python3 W62_RUN_AXIOMS.py` audits every source-named declaration and the
original family boundary. The required root build follows the main merge.

## W63 perfect Tate duality prerequisites

Work in the original system, without comparison hypotheses. Each new complete
module has cap 150 lines. First prove generic exactness from the specified
closed inclusions, faithfully flat reductions, kernel equations and ranks
(`PDivisibleGenericExactness`). Then prove coherent p-power division and the
actual Tate quotient comparison (`PDivisibleTateReduction`). Lift finite-level
generators through the compact inverse limit (`PDivisibleTateFinite`), and
prove torsion-freeness and freeness (`PDivisibleTateFree`). Rank control and
perfect Cartier duality follow these prerequisites; connected Hodge–Tate
exactness, both-component compatibility and filtered de Rham comparison remain
separate gates. No map or nondegeneracy theorem alone closes those gates.

W63 refinement (cap 150 each): `PDivisibleTateRank` identifies tensor reduction
with the original finite points and proves rank equals height.
`TateRootModule` builds the genuine coherent-root target with residue scalar
actions. Integral perfectness must construct all root-valued linear
functionals from actual dual Tate vectors; it cannot follow from equal rank
and integral nondegeneracy alone.

W63 further leaves, each cap 150: `PDivisibleFiniteRootPairing` proves finite
bilinearity, `PDivisibleTateRootPairing` packages the original root-valued
limit map, and `PDivisibleRootFunctionalDescent` descends every root-valued
linear functional to the original finite levels. `PDivisibleTateRootDuality`
proves coherence of its finite Cartier representatives and hence perfect
integral duality. `ConstantRationalTateBasis` proves that the prescribed
constant Tate generator is a basis. `RationalPlaceTateRootRank` identifies
its dual Tate module with the actual roots and proves finite freeness and
rank one (using the existing odd-prime constant-system constructor).
`PDivisibleTateRootGalois` proves original Galois compatibility, and
`RationalPlaceTateRealizationRank` computes the full C_p realization ranks.
These leave the standard positive cyclotomic twist identification and the
actual left Hodge–Tate map as distinct HT1
work. HT2–HT3, filtered period realization and weights are not consequences
of integral duality alone.

W63 final refinement (cap 150): `RationalPlaceTateRootDuality` uses the proved
finite freeness to commute Hom with C_p scalar extension, giving perfect
duality on the original full realizations with the genuine root-line target.
The remaining HT1 identification is with the standard positive cyclotomic
twist, followed by transport of the Lie transpose to the actual left map.

W63 verification is recorded with source hashes and checked-at timestamps in
`W63_VALIDATION.json` and `W63_AXIOM_RESULT.json`; `W63_ROOT_BUILD_RESULT.json`
records the root build after the main merge. Recheck all claims with
`python3 W63_FINAL_CHECKS.py`. The untracked `FAMILY_W63_DONE.md` lists the
individual leaves and exact remaining boundary. The original family admission
and the constant-system sanity check are unchanged.

## W64: prescribed cyclotomic coordinates and the actual left map

Each leaf retains the 150-line cap. The next HT1 leaves are
`RationalCyclotomicRootVector` (primitive finite generators),
`RationalCyclotomicRootBasis` (compact compatible coefficient fibres), and
`RationalCyclotomicRootGalois` (the original positive character action).
`RationalPlaceRootTwist` extends those prescribed coordinates over C_p.
`RationalPlaceTateScalarDuality` orients the original perfect pairing toward
the original Tate realization by vector-space evaluation, and
`RationalPlaceTateRootEquivariance` checks both original Galois factors.
`RationalPlaceHodgeTateLeft`, `RationalPlaceLieTransposeGalois`, and
`RationalPlaceHodgeTateLeftGalois` transport the original Lie transpose and
prove its positive-twist equivariance.

For HT2, split the remaining linear algebra from the connected comparison:
`RationalPlaceLieEvaluationEquiv` identifies the full cotangent dual;
`RationalPlaceHodgeTateLeftImage` describes the actual kernel and image and
reduces left injectivity to surjectivity of the original Cartier differential;
`RationalPlaceHodgeTateLeftRank` expresses the kernel defect in terms of that
same differential rank. `RationalPlaceTwistSeparation` and
`RationalPlaceHodgeTateComplex` use nonzero-twist vanishing to show that the
original right map kills the original left image.

None of these linear-algebra reductions establishes connected differential
surjectivity or equality of the left image and the right kernel. The next
comparison leaf must prove differential surjectivity for the original
connected system without accepting it as data, then establish the exact
kernel and assemble through the connected-etale extension. Full HT3,
DR1/P2-P6, W1-W3 and replacement of the original family admission remain
separate work. The original constant-system period sanity check is retained.

## W66: check the direction before applying Tate comparison

The proposed map `T(G) tensor C -> t_(G^dual)^* tensor C` is a quotient
map in the Hodge–Tate sequence; it is not generally injective. A Tate twist
does not change this dimension obstruction. In the current API,
`rationalPlaceHodgeTateDlogLinear X` has source the realization of
`X.cartierDual`, and target the cotangent realization of `X`.
For the constant height-one system X, its target is zero and its source has
dimension one. Thus the proposed injectivity step, as written, is false.
The transpose has a different source, and its injectivity remains the
comparison theorem, equivalent to surjectivity of this dlog map.

Split before implementation (each new module capped at 150 lines):

| Leaf | Module / obligation | Dependency / status at split |
|---|---|---|
| a0 | `AugmentationUnramifiedCotangent`: zero augmentation cotangent for an unramified algebra | Prove from formal etaleness of the augmentation |
| a1 | `ConstantRationalHodgeTateDlog`: zero dlog, one-dimensional source, failure of injectivity on the actual constant system | a0 and existing Tate rank theorem |
| a2 | Logarithm comparison for the original connected system and its dual | Open analytic input; do not assume injectivity of dlog |
| a3 | Injectivity of the actual transposed Lie-to-Tate map | Requires a2, not dimension counting alone |
| b | Orthogonality of actual left/right maps | Already `rationalPlaceHodgeTate_range_le_ker`; full dual pairing compatibility remains HT3 |
| c | Dimension sum for original Lie modules and dual | Must justify the original cotangent ranks, not merely Tate rank = height |
| d | Image = kernel and right surjectivity for original maps | Requires a3, b, c and the corresponding dual comparison |

Leaves a2–d name mathematical obligations, not new records containing those
obligations as fields. Do not add conditional exactness wrappers in place
of the missing comparison. HT3, DR1/P2–P6 and W1–W3 remain downstream.


## W67: primary-source orientation and Cartier adjunction

Source checked against J. Tate, *p-Divisible Groups*, in *Proceedings of a
Conference on Local Fields* (1967), pp. 158–183, especially pp. 167–169,
177–180. The scan is available at
https://www.math.arizona.edu/~cais/scans/Proceedings_on_a_Conference_in_Local_Fields.pdf .
Proposition 11, not Proposition 4, proves injectivity of
`dα : t_G(C) → Hom_Zp(T(G′), C)`. Proposition 4 concerns connected–etale
points; Theorem 2 concerns nonzero-twist cohomology. Theorem 3 and its
Corollary 2 give the comparison and decomposition. The independent dimension
sum is Proposition 3, p. 166 (Frobenius/Verschiebung).

Here `rationalPlaceHodgeTateLieTranspose X` has the orientation of `dα`;
`rationalPlaceHodgeTateDlogLinear X` is its transpose under Lie evaluation.
Identifying the former with the derivative of Tate's analytic character map
is an unproved comparison, not a consequence of naming the maps.
Tate's `G(S)` is `lim_i colim_n G_n(S/m^i S)`, not just the union of finite
level points. Its logarithm has torsion kernel; over algebraically closed C
it induces `G(O_C)/G(O_C)_tors ≅ t_G(C)`. His proof uses torsion-freeness
of `ker α` after the torsion pairing is proved bijective, never of all G(S).
Fontaine, *Groupes p-divisibles sur les corps locaux* (1977), V §1.1,
pp. 225–226, distinguishes `T(G)`, `U₀(G)=T(G) tensor Qp`, and the larger
universal cover `U(G)`; these must not be substituted for each other.

Split before implementation; all new modules capped at 150 lines:

| Leaf | Original-map obligation | Status at split |
|---|---|---|
| B1 / `PDivisibleCartierBidualTateEquiv` | Prove the specified bidual Tate map bijective using actual finite evaluation | Open algebraic prerequisite |
| B2 / `RationalPlaceHodgeTateRightCotangent` | Extend that bidual equivalence and factor the actual right map through the dual differential | Open algebraic prerequisite |
| B3 / `RationalPlaceHodgeTateCartierAdjunction` | Pair the right map with dual Lie vectors; identify its kernel as a Cartier annihilator; prove orthogonality of the two actual left images in bidual coordinates | Open; no comparison hypothesis |
| A1 | Construct the connected formal group, completed points, analytic logarithm and its torsion quotient from the original system | Open analytic construction |
| A2 | Compare the derivative of the analytic Cartier character with the original completed differential, then prove transpose injectivity | Requires A1 and Tate Proposition 11 argument |
| C | Original Lie dimension sum from Frobenius/Verschiebung and finite-flat ranks | Open; not implied by Tate-module height |
| D | Exactness and connected–etale assembly | Requires A2, its dual, B3 and C |

B1–B3 do not close A1–D. No conditional exactness wrapper replaces the
analytic construction. HT3 beyond the proved pairings, DR1/P2–P6, W1–W3,
and the family admission remain separate obligations.

W67 refinement before B4 implementation: `RationalPlaceHodgeTateOrthogonality`
(cap 150) proves orthogonality directly in X's original Cartier pairing from
the positive character actions on both actual left maps. This avoids needing
to identify the dual-system bidual pairing with the original pairing first.
It remains a zero-component compatibility theorem, not full HT3 or exactness.

W67 proved B1–B4: actual bidual Tate bijectivity; right-map factorization
through the original dual dlog; right-kernel annihilator identification in
bidual Cartier coordinates; and orthogonality in both that pairing and X's
original root-valued Cartier pairing. None assumes differential surjectivity.
The existing p-nilpotent formal smoothness and infinitesimal cotangent
representation (`PDivisibleFormalSmoothness`, `PDivisibleFormalCotangent`)
are inputs for A1, not yet its analytic coordinate/logarithm construction.
The analytic derivative identification, Lie dimension sum and exactness
remain unproved. Recheck the new leaves using `python3 W67_FINAL_CHECKS.py`;
module logs, source hashes and axiom results accompany `FAMILY_W67_DONE.md`.

## W68: original completed points before the analytic logarithm

Refine A1 into the following leaves before implementation (each new module
at most 150 lines). These construct the actual inverse limit of the original
point colimits; no logarithm or comparison property is built into its data.

| Leaf | Module / obligation | Dependencies |
|---|---|---|
| A1a | `PDivisiblePointColimitGroup`: convolution group law on the original point colimit, natural coefficient maps, agreement with original multiplication | Original finite Hopf points |
| A1b | `RationalPlacePointPrecision`: original O_C/p-power reduction composition and surjectivity on colimit points at positive precision | Proved nilpotent formal smoothness |
| A1c | `RationalPlaceCompletedPoints`: compatible original point sequences, abelian group, finite-level integral specialization | A1a–A1b |
| A1d | `RationalPlaceCompletedPointLifting`: surjectivity of each positive-precision projection | A1b–A1c and recursive compatible lifting |

The topology, connected formal coordinates, convergent logarithm, local
isomorphism and torsion kernel require further leaves after these algebraic
constructions. A2, C, D, HT3 and the period/family obligations remain open.
