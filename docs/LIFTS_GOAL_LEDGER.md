# GOAL-L0: lifting for the positive-natural FLT goal

This is a delta to [LF0](LIFT_FAMILY_PLAN.md), especially its restricted lifting
contract and K1, and [CORE](CORE_PLAN.md), L0–L6. It does not replace those plans
or their shared lifting/family budget. Queue IDs below are **GL**, not their L IDs.

## W14 source match and split — checked 2026-10-03

The contracts below precede their proofs. E1c has a formal cochain-comparison
part and an arithmetic part; only the former has the necessary foundations.
Source: GHLS, arXiv:1506.01050v3, Definition 2.1.2 and Example 2.1.4(1),
PDF pp. 7–8 (`Scratch/LiftsW13/ghls.txt`, lines 312–353). The example identifies
the Tate pairing through Kummer and Artin with evaluation, then identifies
unramified annihilators with units. It does not prove those foundations.
For the formal comparison use the homogeneous-to-inhomogeneous substitution
`F(g₀,…,gₙ) = g₀ • f(g₀⁻¹g₁,…,gₙ₋₁⁻¹gₙ)` and evaluate at
`(1,g,gh,…)`. Mathlib's `TopRep.d` uses alternating deletion with initial
positive sign; `groupCohomology.IsCocycle₁/₂` fixes the explicit conventions.
Locally compact G and a jointly continuous coefficient action are explicit
hypotheses (satisfied in the intended profinite/discrete setting).

| Leaf / proposed module under FLT | Contract and source/API | Dependency/status | Cap |
|---|---|---|---|
| E1c1 / Extensions.HomogeneousOne | Construct the coefficient TopRep and homogeneous degree-zero/one maps; prove evaluation, inverse, differential formulas. `ContinuousMap.curry`, `coind₁_apply_apply`, `homogeneousCochains.d_apply`. | READY | 200 |
| E1c2 / Extensions.HomogeneousTwo | Degree-two cochains, reconstruction and degree-one differential; identify the 2-cocycle equation by evaluating the degree-two differential. Same APIs and locally compact uncurrying. | E1c1 | 200 |
| E1c3 / Extensions.ContinuousH1Comparison | Compare continuous cocycles/principals and the splitting quotient with actual `continuousCohomology 1`. `cohomologyIsoQuot`, `bdryKer`, `cokerπ_eq_zero_iff`. | E1c1/c2 | 200 |
| E1c3a / Extensions.ContinuousH1Equiv | Descend E1c3 to the splitting quotient and prove bijectivity; explicit representative formula. | E1c3 | 200 |
| E1c4 / Extensions.ContinuousH2Comparison | Map explicit continuous 2-cocycles to actual H², prove surjectivity and zero iff an actual continuous coboundary exists. `cohomologyIsoQuot`, `cokerπ_surjective`. | E1c2 | 200 |
| E1c5 / Extensions.HomogeneousCup | Compute the actual homogeneous (1,1) cup under evaluation as the explicit cup; descend the computation to H². `cupCochain_coe`, `cupPair_succ_apply`, `cokerDescBilinear_apply`. | E1c3/c4 | 200 |
| E1c5a / Extensions.ContinuousCupComparison | Descend the homogeneous cup formula to actual H² via the constructed quotient models. | E1c5 | 200 |
| E1c6 / Extensions.PeuCohomologyComparison | Express E1b's predicate as vanishing of the actual continuous cohomology cup against inertia-trivial characters. | E1c5 | 200 |
| E1c7 / SerreWeight.LocalTateComparison | Specialize the genuine local invariant and prove compatibility with Kummer and local Artin evaluation, with Frobenius/sign normalization recorded. | BLOCKED: local CFT, invariant and local Tate duality foundations absent | 200 adapter only |
| E1d1 / SerreWeight.ExtensionKummer | Deduce prime-field annihilator = valuation-unit classes from E1c7 and the valuation quotient; prove both inclusions. | BLOCKED E1c7 | 200 adapter only |
| E1d2 / SerreWeight.ExtendedExtensionKummer | Extend the annihilator comparison to the residual field, then transport through actual Hom coordinates using E09c. | BLOCKED E1d1 | 200 adapter only |

API audit (read-only, checkout and pinned Mathlib, 2026-10-03):
`rg -n -i 'reciprocity|tate.{0,15}duality|local.{0,15}duality|invariant map'
FLT .lake/packages/mathlib/Mathlib/NumberTheory
.lake/packages/mathlib/Mathlib/RepresentationTheory` finds quadratic
reciprocity, descriptive references, and `FLT/PoitouTate.lean:67–74`.
The latter supplies `localPairing` and an order-formula assumption as record
fields; it is not a construction or a local-duality theorem. Mathlib's
`ContCohomology/Sha.lean` defines Sha, not Tate duality. The local-field and
Brauer files do not construct `inv_K : H²(K,μ_p) → (1/p)ℤ/ℤ`, a local Artin
map, its inertia/unit compatibility, or the Kummer–cup evaluation theorem.
`ContCohomology.Basic/CupProduct` do supply the formal homogeneous complex,
quotient and cup APIs. These positive results do not make E1c7 ready.
Foundational arithmetic programs need their own source-matched splits;
the 200-line adapter caps are not bounds on those missing programs.
No Serre-weight evaluation or arbitrary-p Raynaud leaf is dispatched.

## W13 acceptance — checked 2026-10-03 01:42 UTC

E09c is proved, and E1 has been split and started with E1a/b. Seventeen new
modules (1,418 lines, all ≤200) passed foreground builds, individual module
lints and axiom audits. All 56 named theorems and all 106 named definitions,
abbreviations and theorems use only propext, Classical.choice and Quot.sound.
The initial E09c split was committed as `50b071f1`; the linear, actual-Hom,
and tensor refinements as `3dd88843`, `2ebb213b`, `40f62395`; E1's source match
and split as `8e7cf1fd`, before implementing E1a/b.

| Item | Module under FLT | Lines/cap | Commit |
|---|---|---|---|
| E09c1 | GroupScheme.PrimeRootCoordinates | 46/200 | `21c9825d` |
| E09c2 | GaloisRepresentation.Extensions.CharacterCoefficients | 94/200 | `1c96403a` |
| E09c3 | GroupScheme.PrimeCyclotomicCoefficients | 62/200 | `1977c49a` |
| E09c4 | GaloisRepresentation.Extensions.ContinuousCocycleCoordinates | 64/200 | `eaa2aaef` |
| E09c5 | GaloisRepresentation.Extensions.ContinuousClassCoordinates | 74/200 | `f11cc5f6` |
| E09c5a | GaloisRepresentation.Extensions.LinearClassCoordinates | 77/200 | `9d5e283c` |
| E09c5b | GaloisRepresentation.Extensions.TensorCharacterClasses | 122/200 | `a6a61738` |
| E09c6 | GaloisRepresentation.Extensions.LinearContinuousClass | 127/200 | `8b81e469` |
| E09c6a | GaloisRepresentation.Extensions.LinearCoefficientMap | 56/200 | `62c11c94` |
| E09c6b | GroupScheme.RootModuleLinear | 49/200 | `9647194f` |
| E09c7a | GroupScheme.LinearKummerClass | 99/200 | `11ccbe9b` |
| E09c7 | GroupScheme.PrimeUnitSubspace | 55/200 | `7202690f` |
| E09c8 | GaloisRepresentation.Extensions.ExtendedUnitSubspace | 101/200 | `be6b240e` |
| E09c9a | GaloisRepresentation.Extensions.OrdinaryHomCoordinates | 86/200 | `d6908c95` |
| E09c9 | GaloisRepresentation.Extensions.OrdinaryTwist | 131/200 | `f4b80045` |
| E1a | GaloisRepresentation.Extensions.ContinuousCup | 99/200 | `950e82a2` |
| E1b | GaloisRepresentation.Extensions.PeuRamifiedClass | 76/200 | `5172c42b` |

`tensorCharacterClassLinearEquiv` proves the canonical k-linear comparison
`k ⊗[F] H¹_cont(G,F(χ)) ≃ H¹_cont(G,k(χ))` for a finite F-basis of k.
Its pure-tensor formula is actual coefficient inclusion followed by scaling;
the map is independent of the auxiliary basis. Both sides use the explicit
continuous quotient, not a claimed derived-functor identification.
`primeCyclotomicCoordinates_equivariant` identifies the root action with the
actual modular cyclotomic character. `linearKummerEquiv` is additive, so
`primeUnitSubspace` is exactly the independent valuation-unit image.
`extendedUnitSubspace` is its k-span after the constructed coefficient map.
Its scalar-invariance theorem works on the original splitting quotient.
`ordinaryHomUnit_twist_iff` and `liftedUnitClass_basis_iff` apply that result to
actual Hom representations and actual lifted-difference cocycles.

E1a proves a continuous (1,1) cup and its continuous splitting coboundary.
E1b defines the independent cup-annihilator of unramified trivial characters,
proves splitting invariance and descends it to the class quotient. E1c/d
remain blocked on the explicit-to-derived degree-two/cup comparison and the
local Tate/Artin evaluation theorem. Neither this arithmetic comparison nor
Serre-weight evaluation, Raynaud classification or global lifting is claimed.

Validation: `python3 Scratch/LiftsW13/check.py` checks caps, source scope,
sorted unique FLT imports, every final per-module build/lint log, all named
declaration audits and the final dependency audit. It checks recorded logs;
for fresh execution run, for each module M individually:
`LEAN_NUM_THREADS=2 lake build M`, then
`LEAN_NUM_THREADS=2 lake exe runLinter M`, then
`LEAN_NUM_THREADS=2 lake env lean Scratch/LiftsW13/<ShortName>Axioms.lean`.
No whole-library build or lint ran. Combined fresh audit:
`LEAN_NUM_THREADS=2 lake env lean Scratch/LiftsW13/FinalAxioms.lean`.
Logs: `Scratch/LiftsW13/<ShortName>-{build,lint,axioms}.log`,
`Final-axioms.log`, `summary.json`. All final logs are warning/error-free.
The final audit still gives sorryAx for lifts and its adapter, and
`[Mazur_statement, propext, sorryAx, Classical.choice, Quot.sound]` for
`PNat.pow_add_pow_ne_pow`. W13 has not removed the lifting admission.

## W13 E1 source match and first leaves — checked 2026-10-03

E09c's coefficient gate is now proved: the prime cyclotomic/root identification,
canonical k-linear tensor comparison (including the pure-tensor formula and
basis independence), prime unit subspace, extended unit span, actual Hom twist
transport, and actual lifted-difference b/a invariance all have implementations.
All root-existence/primitive-root hypotheses remain explicit for a general L/K;
E08g supplies the former in the characteristic-zero algebraic closure, and
`HasEnoughRootsOfUnity.exists_primitiveRoot` supplies the latter. No arithmetic
ramification or finite-flat assertion follows just from these comparisons.

For E1 use Gee–Herzig–Liu–Savitt, *Potentially crystalline lifts of certain
prescribed types*, arXiv:1506.01050v3 (2017), Definition 2.1.2 and Example
2.1.4(1), PDF pp. 7–8. Checked from the downloaded author PDF; local evidence:
`Scratch/LiftsW13/ghls.{pdf,txt}`. The definition is annihilation under local
Tate duality by unramified dual classes. In the ordinary cyclotomic case the
dual is trivial, and the source compares the pairing, through Kummer and Artin,
with evaluation `Kˣ/(Kˣ)^p × Hom(Kˣ,Fp) → Fp`. It then identifies the annihilator
of unramified characters with valuation units. This definition is independent
of Kummer units and finite-flat models, as required.

| E1 leaf / new module | Contract, source/API match | Status | Cap |
|---|---|---|---|
| E1a / Extensions.ContinuousCup | Construct the continuous (1,1) cup with a trivial additive character, prove its 2-cocycle identity, and compute the continuous 2-coboundary from a splitting change. Mathlib LowDegree.IsCocycle₂/IsCoboundary₂ specify signs; continuous scalar multiplication and E03 supply the calculation. | READY | 200 |
| E1b / Extensions.PeuRamifiedClass | Define the explicit continuous cup-annihilator of characters vanishing on inertia, prove splitting invariance, and descend to the existing class quotient. This is the independent ordinary predicate; no unit or finite-flat condition enters its definition. | E1a | 200 |
| E1c / SerreWeight.LocalTateComparison | Identify the explicit degree-one/two cocycles and cups with the continuous cohomology pairing; specialize the genuine local Tate invariant and Artin reciprocity evaluation. The existing ContCohomology.CupProduct is on homogeneous/coinduced complexes, not the required low-degree comparison or local reciprocity theorem. | BLOCKED on new local-duality/reciprocity foundations; split/source-match those before proof | 200 adapter only |
| E1d / SerreWeight.ExtensionKummer | Prove that the E1b annihilator equals E09c's extended unit subspace, using E1c's proved evaluation comparison and the valuation quotient; transport through actual Hom coordinates. | BLOCKED E1c | 200 adapter only |

Only E1a/b are ready. The bounds on E1c/d do not certify the size of their
missing arithmetic foundations. No local Tate theorem is installed as a field
of a record, and no Serre-weight evaluation or Raynaud classification is ready.

## W13 source match and bounded E09c split — 2026-10-03

These contracts are committed before proof. Each new module has a 200-line
cap, including imports. All comparisons concern E06's explicit continuous
quotient. A finite basis may model scalar extension: coordinatewise cocycles
and coordinatewise splitting changes must both be proved, not postulated.

| Leaf / proposed module | Contract and checked source APIs | Dependencies |
|---|---|---|
| E09c1 / GroupScheme.PrimeRootCoordinates | `ZMod p ≃+ RootModule L p` from a primitive root; compute its value on natural integers. Mathlib RootsOfUnity/PrimitiveRoots: zmodEquivZPowers, zpowers_eq; MulEquiv.subgroupCongr. | READY |
| E09c2 / Extensions.CharacterCoefficients | Discrete character coefficient module, prime-to-extension coefficient embedding and basis-coordinate equivariance for a character valued in the prime field. CharacterLines.characterLine; Basis.equivFun, map_smul. | E09c1 |
| E09c3 / GroupScheme.PrimeCyclotomicCoefficients | E09c1 intertwines the natural Galois action with the actual modularCyclotomicCharacter; hence continuous cocycles/classes identify with the prime character line. CyclotomicCharacter.modularCyclotomicCharacter.spec; E09b.coefficientClassEquiv. | E09c1/c2 |
| E09c4 / Extensions.ContinuousCocycleCoordinates | Finite products commute with continuous cocycles and splitting equivalence, including reconstruction of the splitting vector. continuous_pi; E06; coordinate evaluation. | E09c2 |
| E09c5 / Extensions.ContinuousClassCoordinates | Finite-product continuous classes are exactly products of classes; combine with an equivariant finite coefficient basis to compare scalar-extended character classes. Quotient.map/lift, Quotient.choice, E09b. | E09c4 |
| E09c6 / Extensions.LinearContinuousClass | Linear cocycle submodule, principal submodule, and a proved equivalence of its quotient with E06's explicit quotient. Submodule.mkQ; splittingEquivalent_iff_coboundary. | E09c5 |
| E09c7 / GroupScheme.PrimeUnitSubspace | Prove additivity of the Kummer comparison, then the prime-field unit subspace using the independently defined valuation-unit subgroup. rootUnit_add, unitRatio_mul; KummerUnitClass.unitClasses. | E09c3/c6 |
| E09c8 / Extensions.ExtendedUnitSubspace | Define coefficient extension of E09c7 and prove arbitrary nonzero residual-field scalar changes preserve and reflect membership; relate to finite-basis comparison, independent of basis. Submodule.span/map, E09c5/c6/c7. | E09c7 |
| E09c9 / Extensions.OrdinaryTwist | Apply E09c8 to actual Hom-character coordinates and E09e's b/a lift-basis change, with simultaneous twists cancelling. | E09c8 |

Additional linear foundations matched before proof (each cap 200):

| Leaf / module | Contract and source | Dependencies |
|---|---|---|
| E09c6a / Extensions.LinearCoefficientMap | Semilinear equivariant coefficient maps induce semilinear maps of continuous cocycles and classes. Submodule.mapQ; continuous_of_discreteTopology. | E09c6 |
| E09c6b / GroupScheme.RootModuleLinear | Canonical ZMod-p module on root coefficients, commuting with Galois; primitive-root coordinates are linear. AddCommGroup.zmodModule; ZMod.map_smul; rootUnit_pow. | E09c1/c3 |
| E09c7a / GroupScheme.LinearKummerClass | Additive Kummer comparison on linear continuous classes; prove product compatibility from unitRatio_mul and root-choice independence. | E09c6/c6b |

The last adapter also needs a concrete Hom action, not a supplied
conclusion-bearing equivalence. E09c9a / Extensions.OrdinaryHomCoordinates
(cap 200) constructs the discrete Hom coefficient module from
`Representation.linHom`, then proves that evaluation at 1 intertwines a
specified cyclotomic Hom character. E09c9 consumes this constructed map.
E09c5a / Extensions.LinearClassCoordinates (cap 200) upgrades the finite-basis
comparison to an F-linear equivalence using `linearCoefficientClass` and the
already proved quotient bijection. These refinements are source-matched
before their implementation.

E09c5b / Extensions.TensorCharacterClasses (cap 200) now has its
source match: `TensorProduct.equivFinsuppOfBasisLeft`,
`Finsupp.linearEquivFunOnFinite`, and E09c5a construct an F-linear tensor
comparison. Its pure-tensor formula must identify it with the canonical
coefficient inclusion followed by k-scaling; this also proves independence
of the auxiliary coefficient basis. This closes the distinction between a
bare product-of-classes equivalence and the scalar-extension comparison.

The modules listed after c5 are new constructions, not existing APIs. E09c
closes only after the unit-space and actual ordinary-extension adapters are
proved. Root existence and a primitive root must be supplied explicitly or
proved for the algebraic closure. No equality of an arbitrary k-line with
the cyclic root group is asserted. E1's independent ramification predicate
and arithmetic comparison remain a separate gate; no Serre-weight or Raynaud
classification work is ready on the strength of this split.

## W12 acceptance and remaining boundary — checked 2026-10-03 00:56 UTC

E08a–g and E09a/b/d/e are implemented in eleven new modules (1,051 lines).
All modules passed individual foreground builds and individual module lints.
All 64 named theorems and all 87 named definitions/abbreviations/theorems,
plus the named root-action instance, have only propext, Classical.choice
and Quot.sound. The initial split was committed as `f3faa7f1`; additional
bounded specializations were matched in `02b56d0f` and `561a0965` before proof.

| Leaf | Module under FLT | Lines/cap | Proof commit |
|---|---|---|---|
| E08a | GroupScheme.KummerCoefficients | 80/200 | `e981d170` |
| E08b | GroupScheme.KummerCoefficientDescent | 100/200 | `98541874` |
| E08c | GroupScheme.KummerRefinement | 98/200 | `34d498c7` |
| E08d | GroupScheme.ContinuousKummerParameter | 59/200 | `9ed4ee34` |
| E08e | GroupScheme.KummerRootClass | 107/200 | `c8f6a422` |
| E08f | GroupScheme.ContinuousKummerClass | 123/200 | `e6d55b34` |
| E08g | GroupScheme.AlgebraicClosureKummer | 49/200 | `2a6d75ac` |
| E09a | GaloisRepresentation.Extensions.CharacterLines | 92/200 | `ac19c728` |
| E09b | GaloisRepresentation.Extensions.CharacterBasis | 105/200 | `b4b33ec5` |
| E09d | GroupScheme.KummerUnitTransport | 147/200 | `565f428e` |
| E09e | GaloisRepresentation.Extensions.LiftBasisTransport | 91/200 | `ae133e37` |

E08 constructs the actual root-coefficient embedding into the finite Galois
cocycle field, proves equivariance and refinement compatibility, and uses
finite Hilbert 90 to recover a parameter for every continuous root cocycle.
`rootCocycle_equivalent_iff` proves that equality of the independent power
classes is exactly a change of splitting. `continuousKummerEquiv` is the
resulting bijection when L/K is Galois, n is nonzero, and L contains nth
roots of all base units. `algebraicClosureKummerEquiv` supplies those roots
for perfect K, including characteristic zero, with no root-existence input.
The general imperfect-field separable-closure specialization is not proved.
This remains the explicit E06 quotient, not a derived-continuous-H1 comparison.

E09a/b construct the character-line Hom coordinate equivalence, cancellation
of simultaneous twists, inertia invariance for an unramified twist, and
transport of continuous classes through discrete equivariant coefficient
equivalences. E09e connects the transport to E04's actual lift construction;
rescaling the sub-line basis by a and quotient lift by b multiplies the
cocycle by b/a. E09d proves Kummer compatibility with invertible cyclic
coefficient scaling and preservation/reflection of unit membership on
continuous classes. Its unit predicate uses the proved equivalence and the
independently defined valuation-unit subgroup.

**E09c remains a gate.** No arbitrary finite coefficient-field line has been
identified with the cyclic root module. To transport the unit *subspace*
over arbitrary residual k, construct the prime-field cyclotomic coefficient
identification and the scalar-extension comparison for cocycles/classes,
then prove stability of the extended unit subspace. Cyclic powers do not
supply that theorem. E1 also still needs an independent peu-ramification
definition and its comparison. No Serre-weight evaluation, arbitrary-p
Raynaud classification, or lifting assembly is claimed by W12.

Validation evidence (local, untracked): `Scratch/LiftsW12/check.py` verifies
caps, source scope, sorted unique FLT.lean imports, clean logs and axiom sets.
Run `python3 Scratch/LiftsW12/check.py` to recheck the source and recorded logs;
to rebuild a leaf, run `LEAN_NUM_THREADS=2 lake build MODULE`, then
`LEAN_NUM_THREADS=2 lake exe runLinter MODULE` for that module only, and
`lake env lean Scratch/LiftsW12/<ModuleName>Axioms.lean` with the same thread limit.
Logs are `{Coefficients,Descent,Refinement,Parameter,Root,Class,Closure,Lines,
Basis,Transport,LiftBasis}-{build,lint,axioms}.log`. Extra-axioms.log checks the
root action and displays the two comparison signatures. No whole-library
build or lint was run. Existing Lean proof files were not changed.

The final-goal audit (`LEAN_NUM_THREADS=2 lake env lean
Scratch/LiftsW12/GoalAxioms.lean`, existing compiled theorem) still reports
`[propext, sorryAx, Classical.choice, Quot.sound]` for lifts and its adapter,
and `[Mazur_statement, propext, sorryAx, Classical.choice, Quot.sound]` for
`PNat.pow_add_pow_ne_pow`. See Goal-axioms.log. W12 proves foundations;
it does not remove the admitted lifting theorem from the final dependency graph.

## W10 current gate map — checked 2026-10-02 UTC

This section supersedes readiness labels in the historical audit below and in
W4/W5. Audited checkout: `ae2d6682` (contains W9's four commits); this is a
local source check, not a fresh assertion that HEAD equals remote main.
Checks: `git rev-parse HEAD`; `rg -n 'theorem|lemma|def'` on the modules named
below; `rg -n 'sorry' FLT/GaloisRepresentation/HardlyRamified/Lift.lean`.
The exact target remains the displayed `lifts` statement below, including
its universes, all finite fields k and every odd prime p. Its body is still
`sorry`. F1–F6 do not construct a global lift.

### Proved inputs and their precise limits

Paths are relative to FLT. The modules, rather than old READY labels, are
rerunnable evidence. This table records source inspection; W9's build and
axiom evidence is in its untracked result, and W10 audits its own additions.

| Gate | Proved modules | Limit |
|---|---|---|
| Residual oddness, absolute irreducibility | GaloisRepresentation/HardlyRamified/{ResidualOddness,AbsoluteIrreducibility} | Not irreducibility after cyclotomic restriction |
| GL1–GL4 | HardlyRamified/{PrimeResidueMap,ResidualOddness,LiftPrimeAvoidingP,LiftDomainFree} under GaloisRepresentation | Prime extraction assumes p nonnilpotent; no arithmetic source of that premise |
| Prime residual coefficients | HardlyRamified/{PrimeResidualAlgebra,PrimeResidualNaturality,LiftDomainResidue} | Requires a supplied finite local deformation ring with the prime residue algebra; no arbitrary-k construction |
| W4.1–W4.3 | Deformations/RepresentationTheory/{FlatDiscrete,FlatReduction,FlatCofinal} | Cofinality and openness still explicit in the p-power endpoint |
| W5.1–W5.2 | AbsoluteGaloisGroup/RootCharacter; GroupScheme/KummerCocycle | Kummer result is finite Galois algebra, not continuous extension-class classification |
| F1–F3 | AbsoluteGaloisGroup/RootCharacter{Independence,Uniformizer,Topology} | Root choices, compatible degrees, continuity and finite image |
| F4 | AbsoluteGaloisGroup/{RootInertiaTransitivity,FundamentalTame,RootCharacterResidue,FirstRamificationFiltration,FirstRamificationPGroup,WildInertiaProP} | Tame root characters and wild inertia, not classification of two-dimensional representations |
| Finite tower step | AbsoluteGaloisGroup/{FiniteTameQuotient,FirstRamificationRestriction} | Actual finite first-group restriction is surjective; no longer an assumed hypothesis |
| F5–F6 | AbsoluteGaloisGroup/{FundamentalCoefficients,FundamentalCyclotomic} | Finite coefficients, Frobenius conjugacy and omegaOne = local modCyclotomic; representation-level transport remains |
| Unrestricted deformation representability | Deformations/Representable.isCorepresentable_deformationFunctor | Narrow S-lift representability still has a sorry; neither theorem proves dimension or finiteness |

W10 topology validation checked 2026-10-02 23:38 UTC: T1 (44/120 lines),
T2 (61/250), T3 (44/100) each passed its foreground build, individual
module linter, and all four new theorems' axiom audits (standard axioms only).
Rerun the acceptance commands below with modules PadicIdealCofinal,
PadicIdealOpen and FlatPadic under FLT.Deformations.RepresentationTheory.
Logs: `Scratch/LiftsW10/{Cofinal,Open,Flat}-{build,lint,axioms}.log`.
Final-goal audit checked 2026-10-02 23:38 UTC: `lake env lean
Scratch/LiftsW10/GoalAxioms.lean` (existing compiled final theorem; its source
unchanged) prints sorryAx for lifts and its adapter, and
`[Mazur_statement, propext, sorryAx, Classical.choice, Quot.sound]` for
`PNat.pow_add_pow_ne_pow`. Evidence: `Scratch/LiftsW10/Goal-axioms.log`.

### Remaining leaves and dependencies

All new proof-module caps below include headers/imports. A BLOCKED leaf is
an adapter contract, **not** a claim that its missing foundation fits in the
cap. Capitalized names in blocked sketches are proposed independent APIs,
not existing declarations or permission to introduce conclusion-bearing
record fields. Large foundation programs are identified after the table;
they must be split and source-matched before these adapters become ready.
No bounded complete implementation plan for those programs is certified.

Use the exact `lifts` context for ρ, and write v_p for its rational p-adic
place. For local sketches τ is rank two over an algebraic closure of the
residual field. D denotes a constructed local deformation ring with its
universal representation; it must not be an input assuming lift existence.

| Leaf / proposed new module | Lean statement sketch | Dependencies / status | Cap |
|---|---|---|---|
| T1 / Deformations/RepresentationTheory/PadicIdealCofinal | `theorem exists_p_pow_le_of_isOpen (I : Ideal A) (hI : IsOpen (I : Set A)) : ∃ n : ℕ, Ideal.span {(p : A)^n} ≤ I` for any topological Zp-algebra with continuous scalar multiplication | DONE W10 (`3474e339`): norm_p, continuous algebraMap, powers tend to zero. No finite/free/local assumptions needed. | 120 |
| T2 / Deformations/RepresentationTheory/PadicIdealOpen | `theorem isOpen_span_p_pow (n : ℕ) : IsOpen (Ideal.span {(p : A)^n} : Set A)` for finite free A with Zp-module topology | DONE W10 (`ab6e2d50`): finite basis, open scalar ideals, continuous linear equivalence. This is topology only. | 250 |
| T3 / Deformations/RepresentationTheory/FlatPadic | `theorem isFlatAt_iff_powers : ρ.IsFlatAt v ↔ ∀ n : ℕ, (ρ.baseChange (A ⧸ Ideal.span {(p : A)^n})).HasFlatProlongationAt v` | DONE W10 (`8f9a51a8`): T1+T2+FlatCofinal. Coefficients as in lifts. | 100 |
| E1 / GaloisRepresentation/SerreWeight/ExtensionKummer | `theorem ordinary_extension_unit_iff : UnitKummerClass (extensionClass τ) ↔ IsPeuRamifiee τ` | BLOCKED on E08/E09 and an independent ramification comparison. E01–E07b now provide explicit continuous classes and finite Galois descent; the Kummer/ordinary dictionary remains. | 300 |
| S1 / GaloisRepresentation/SerreWeight/Normalization | `serreWeight_ordinary_peu ... : serreWeight p τ = 2`; separate ordinary-tres value p+1 and niveau-two value 2 | BLOCKED on E1+S0+F; independent complete Serre recipe, including exceptional/scalar cases. | 250 |
| R1 / GaloisRepresentation/SerreWeight/FiniteFlatOrdinary | `theorem finiteFlat_ordinary_peu (hf : IsFiniteFlatModel τ) (ho : HasOrdinaryInertia τ) (hd : HasCyclotomicDet τ) : IsPeuRamifiee τ` | BLOCKED on R0 ordinary extension/unit classification and E. Neither hf nor peu may be defined by the other. | 300 |
| R2 / GaloisRepresentation/SerreWeight/FiniteFlatInertia | `theorem finiteFlat_inertia_cases (hf : IsFiniteFlatModel τ) (hd : HasCyclotomicDet τ) : HasOrdinaryInertia τ ∨ HasNiveauTwoInertia p τ` | BLOCKED on R0 with coefficient action, e=1 and F. Rank-two and odd-p hypotheses mandatory. | 300 |
| S2 / GaloisRepresentation/SerreWeight/FiniteFlat | `theorem finiteFlat_serreWeight_two (hf : IsFiniteFlatModel τ) (hd : HasCyclotomicDet τ) : serreWeight p τ = 2` | BLOCKED on S1+R1+R2. | 200 |
| S3 / GaloisRepresentation/HardlyRamified/ResidualSerreWeightTwo | `theorem residual_serreWeight_eq_two (hρ : IsHardlyRamified hpodd hV ρ) : serreWeight p ρ = 2` | BLOCKED on S2 and representation/completion/coefficient transport; use FlatDiscrete, hρ.det and F6. | 250 |
| C1 / GaloisRepresentation/HardlyRamified/CyclotomicRestriction | `theorem cyclotomicRestriction_absIrred (hp17 : 17 ≤ p) (hρirred : ρ.IsIrreducible) (hρ : IsHardlyRamified hpodd hV ρ) : IsAbsolutelyIrreducible (cyclotomicRestriction ρ)` | BLOCKED on S3 and proof of KW I Lemma 6.2(ii), not just numeric exclusion of its weights. | 300 |
| D1 / Deformations/HardlyRamified/LocalConditions | `theorem local_conditions_representable : (hardlyRamifiedLocalFunctor ρ).IsCorepresentable` | BLOCKED on L: determinant-fixed weight-two crystalline problem at p, fixed quadratic semistable type at 2, and unramified conditions elsewhere. Trace 2 alone is insufficient. | 300 |
| D2 / Deformations/HardlyRamified/Dimension | `theorem one_le_global_dimension : 1 ≤ ringKrullDim D` | BLOCKED on D1 and G: arithmetic Selmer presentation/duality in KW II Prop. 4.5. Abstract representability does not imply it. | 300 |
| D3 / Deformations/HardlyRamified/Finiteness | `theorem global_module_finite : Module.Finite ℤ_[p] D` | BLOCKED on C1+D1 and M: residual modular seed, auxiliary totally real fields, comparison and KW II Thm. 10.1. | 300 |
| D4 / Deformations/HardlyRamified/Nonvanishing | `theorem p_not_nilpotent : ¬ IsNilpotent (p : D)` | BLOCKED on D2+D3 plus the Noetherian dimension-zero argument for a finite ring killed by a power of p. Then use GL3, not a new assumed point. | 200 |
| I1 / GaloisRepresentation/HardlyRamified/CrystallineTorsionModels | `theorem crystalline_torsion_model (hc : IsCrystallineWeightTwo (σ.baseChange E)) (n : ℕ) : (σ.baseChange (O ⧸ Ideal.span {(p : O)^n})).HasFlatProlongationAt v_p` | BLOCKED on H: independent period-module theory and integral Barsotti–Tate comparison for every stable lattice. | 300 |
| I2 / GaloisRepresentation/HardlyRamified/CrystallineIntegralFlat | `theorem isFlatAt_of_crystallineWeightTwo (hc : IsCrystallineWeightTwo (σ.baseChange E)) : σ.IsFlatAt v_p` | BLOCKED on I1+T3. This is over O; descent to a nonnormal coefficient order is separate. | 150 |
| I3 / GaloisRepresentation/HardlyRamified/LiftOrderDescent | `theorem order_flat_models (n : ℕ) : (σR.baseChange (R ⧸ Ideal.span {(p : R)^n})).HasFlatProlongationAt v_p` | BLOCKED on I1 and integral model descent from O to the residual-compatible image order R. Flatness does not descend by assertion. | 300 |
| I4 / GaloisRepresentation/HardlyRamified/LiftDyadicQuotient | `theorem integral_dyadic_quotient : ∃ (π : W →ₗ[R] R), Function.Surjective π ∧ ∃ δ : GaloisRep ℚ_[2] R R, DyadicQuotientEquivariant σ π δ ∧ Unramified δ ∧ ∀ g, δ g * δ g = 1` | BLOCKED on D1's fixed-character semistable type and integral quotient descent. Sketch expands to Defs.isTameAtTwo, including its inertia subgroup. | 300 |
| A1 / GaloisRepresentation/HardlyRamified/LiftResidualIdentification | `theorem residual_conjugacy : ∃ r : k ⊗[R] W ≃ₗ[k] V, (σ.baseChange k).conj r = ρ` | BLOCKED on D4 and actual universal lift base change to R=D/P; finite/free/local topology, rank-two and residual algebra data must be constructed, not postulated as a package with this equality. | 300 |
| X1 / GaloisRepresentation/HardlyRamified/LiftFiniteField | `theorem finiteField_coefficient_order : ∃ (R : Type u) ..., Algebra R k ∧ IsScalarTower ℤ_[p] R k` | BLOCKED: arbitrary finite k needs a residue-k coefficient ring (e.g. Witt/unramified coefficients) and residue-preserving D/P; current primeReduction lands only in Fp. Reuse GL4 after constructing D. | 300 |
| X2 / GaloisRepresentation/HardlyRamified/LiftSmallPrimes | `theorem lifts_small (hp : p < 17) :` exact lifts existential | BLOCKED on a separate source-matched treatment of p=3,5,7,11,13 and any exceptional restriction case. C1's hp17 cannot be silently added to lifts. | 300 |
| A2 / GaloisRepresentation/HardlyRamified/LiftAssembly | `theorem lifts_from_constructed_deformation :` exact lifts existential | BLOCKED on D1–D4,I3,I4,A1,X1,X2, universe transport. Assemble all four HR fields and actual tensor conjugacy; no extra arithmetic premise in the endpoint. | 300 |

Large missing theory: E (continuous extension classes), S0 (full independent
Serre weight), R0 (arbitrary-p Raynaud classification), L (local deformation
rings), G (Selmer presentation/dimension), M (modularity/auxiliary fields and
finiteness), H (integral p-adic Hodge comparison). These are **not ready leaf
proofs**. The rows above cap only eventual adapters; dispatching any foundation
requires another split into concrete, independently meaningful statements.
Searches find many Raynaud-named order-three modules and a PoitouTate API;
those names do not establish the arbitrary-p R0 or the required G theorem.

Dependency spine: F + E + S0 + R0 → S3 → C1; C1 + L + G + M → D4;
D4 + H + I3 + I4 + A1 + X1 + X2 → A2. T1–T3 discharge only the topology
premises in I2/I3; they do not manufacture torsion models or remove sorryAx.
For the weaker FLT-only route, retain the original Frey contract (k=Fp,
p≥17), omit X1/X2, and later rewire Assembly; this would bypass, **not prove**,
the full `lifts` declaration. No such rewiring is authorized in W10.

Rerun readiness searches:
```sh
rg -n 'serreWeight|IsPeuRamifiee|IsCrystalline' FLT .lake/packages/mathlib/Mathlib
rg -n 'sorry|isCorepresentable' FLT/Deformations/Representable.lean
rg -n 'theorem|lemma' FLT/AbsoluteGaloisGroup/{FundamentalCoefficients,FundamentalCyclotomic,FirstRamificationRestriction}.lean
rg -n 'theorem|lemma' FLT/Deformations/RepresentationTheory/{FlatDiscrete,FlatReduction,FlatCofinal}.lean
```
The first search has no implemented weight/crystalline predicates. Acceptance
for each W10 proof leaf: foreground `LEAN_NUM_THREADS=2 lake build MODULE`,
`LEAN_NUM_THREADS=2 lake exe runLinter MODULE` individually, and every new
declaration's `#print axioms` restricted to propext, Classical.choice,
Quot.sound. Keep proof modules ≤ their row's cap; add sorted FLT.lean imports.

## W11 split of program E — continuous extension classes

Source/API check at `19d6ccb3`, 2026-10-02 UTC: mathlib
`RepresentationTheory/Homological/ContCohomology/LowDegree` implements H0,
not the H1 dictionary needed here. Its algebraic `GroupCohomology/LowDegree`
provides `IsCocycle₁` and `IsCoboundary₁`. The existing
`FLT/GroupScheme/KummerCocycle` proves finite Galois Hilbert-90 statements.
This split uses explicit continuous cocycles first; it does not identify a
new quotient with derived continuous cohomology by definition.

Each row is a separate new module, with a total file cap of 200 lines.
The E0 prefix distinguishes these foundation leaves from adapter E1 above.
Ready leaves are proved in the displayed dependency order. Mathematical
source: the crossed-homomorphism description of H1 and changes of a lift
in an extension; Kummer theory via Hilbert 90. No Serre-weight or Raynaud
classification is an input or a claimed consequence.

| Leaf / module | Concrete statement and proof route | Dependencies / status | Cap |
|---|---|---|---|
| E01 / GaloisRepresentation/Extensions/CocycleAction | For an additive G-module and `IsCocycle₁ c`, construct the affine permutation homomorphism `g ↦ (x ↦ g • x + c g)`; its kernel fixes the original action and kills c. | DONE W11 (`9aec89da`). Uses groupCohomology.IsCocycle₁, additive action laws. | 200 |
| E02 / GaloisRepresentation/Extensions/FiniteDescent | For finite discrete M, continuous c and continuous orbit maps, construct an open normal N and descended action and cocycle on G/N; prove inflation recovers both and G/N is finite. Use E01's kernel, finite intersections of open fibers, and the first isomorphism theorem. | DONE W11 (`b1b73a90`). Uses E01; no assumed quotient or descent witness. | 200 |
| E03 / GaloisRepresentation/Extensions/ChangeSplitting | Prove `c'(g)=c(g)+g•a-a` is a cocycle, is continuous for continuous orbit maps, and define an equivalence relation by this formula; transitivity adds the splitting parameters. | DONE W11 (`14f9d412`). Uses elementary additive action laws and topology. | 200 |
| E04 / GaloisRepresentation/Extensions/LiftCocycle | Given an injective equivariant additive map i:A→V and a vector v fixed modulo i(A), construct the unique cocycle from `i(c(g))=g•v-v`; replacing v by v+i(a) changes it by the E03 coboundary. | DONE W11 (`662c52cb`). Uses E03; explicit range hypothesis expresses quotient invariance, not existence of a representation/lift. | 200 |
| E05 / GroupScheme/KummerUnitClass | Independently define `Kˣ / (Kˣ)^n` and its subgroup of classes represented by valuation-ring units; prove representative criterion and invariance under multiplying by nth powers. | DONE W11 (`d6408497`). Uses QuotientGroup, powMonoidHom and existing exists_unit_factor_iff. | 200 |
| E06 / GaloisRepresentation/Extensions/ContinuousClass | Form the quotient of continuous cocycles by E03 and prove equality iff change of splitting, plus inflation injectivity for a surjective quotient map with descended action. | DONE W11 (`35d2bb96`). E02/E03 APIs matched; explicit quotient and inflation injectivity proved. No derived-functor comparison asserted. | 200 |
| E07a / AbsoluteGaloisGroup/OpenNormalFixedField | For an open normal N in Gal(L/K), with L/K Galois, construct its finite Galois fixed field, the quotient-group equivalence, and its restriction compatibility. | DONE W11 (`5f818f98`). Uses source match: InfiniteGalois.fixingSubgroup_fixedField, isOpen_iff_finite, normalAutEquivQuotient. | 200 |
| E07b / AbsoluteGaloisGroup/CocycleFiniteGalois | Apply E07a to E02's affine kernel, transport the descended action and cocycle to the actual finite Galois group, and prove inflation recovers the original action and cocycle. | DONE W11 (`3b5d4bac`). Uses E02/E07a; generic additive finite coefficients. Roots-of-unity identification remains in E08. | 200 |
| E08 / GroupScheme/ContinuousKummerClass | For roots-of-unity coefficients, construct a bijection between E06 continuous classes and E05 power classes using E07b and finite Hilbert 90; prove independence of finite extension and root. | BLOCKED on E06/E07b and separate refinement transport lemmas; split again if those exceed a leaf. | 200 |
| E09 / GaloisRepresentation/Extensions/OrdinaryTwist | Transport E04 extension classes through an unramified character twist and changes of bases of sub/quotient lines, proving independence of the E05 unit predicate. | BLOCKED on concrete rank-one character/Hom-coefficient API and E08. | 200 |

At the initial split E06–E09 were contracts. E06 became ready from E02/E03;
E07a/b became ready after the explicit Krull API source match above.
E08/E09 remain contracts, not implemented APIs. In particular E08 requires
surjectivity, injectivity and compatibility with roots of unity in positive
and mixed characteristic under the correct invertibility assumptions;
finite additive descent alone does not supply any of them. E1 remains
blocked until the independent ramification definition and these bridges
are available. All arithmetic hypotheses must remain visible.

Acceptance for each ready leaf: foreground `LEAN_NUM_THREADS=2 lake build
MODULE`, then `LEAN_NUM_THREADS=2 lake exe runLinter MODULE` individually;
`#print axioms` for every new theorem must use only propext,
Classical.choice and Quot.sound. Sorted FLT.lean imports only; no existing
Lean proof module edits. Validation and resulting commits are recorded in
`LIFTS_W11_RESULT.md` outside the tracked proof/document tree.

### W11 acceptance — checked 2026-10-03 00:11 UTC

E01–E06 and E07a/b are implemented: eight new modules, 664 total lines,
58–126 lines per module against each 200-line cap. Each passed a foreground
`LEAN_NUM_THREADS=2 lake build MODULE` and its own `lake exe runLinter MODULE`.
All 37 named theorems and all other new definitions/abbreviations (62 named
declarations total) were axiom-audited; only propext, Classical.choice and
Quot.sound occur. No existing Lean module changed except FLT.lean imports.
Checks/logs: `python3 Scratch/LiftsW11/check.py`; module-specific
`{Action,Descent,Splitting,Lift,Units,Class,Fixed,Galois}-{build,lint,axioms}.log`
and `Abbrev-axioms.log` in that scratch directory. These are local untracked
validation artifacts, not files required by downstream imports.

Finite descent now constructs the open normal subgroup, quotient action,
continuous quotient cocycle, finite Galois fixed field and restriction
identities. The independent unit subgroup lives in Kˣ/(Kˣ)^n. No theorem
identifies these units with finite-flat models or peu-ramified extensions.
E08/E09 remain blocked bridges; their caps describe eventual adapters, not
a certified bounded proof of the missing root-coefficient or twist theory.

Goal audit: `LEAN_NUM_THREADS=2 lake env lean Scratch/LiftsW11/GoalAxioms.lean`
(exited 0, existing compiled final theorem) still prints sorryAx for lifts
and hardlyRamifiedLifting. `PNat.pow_add_pow_ne_pow` still has
`[Mazur_statement, propext, sorryAx, Classical.choice, Quot.sound]`.
Evidence: `Scratch/LiftsW11/Goal-axioms.log`; no final-goal dependency was
removed by these foundation leaves.

## W12 source match and bounded E08/E09 split (initial contracts)

Checked 2026-10-03 against the local Mathlib revision recorded above and
W11's modules. This split is committed before implementation. Each cap
includes headers and imports; status here is readiness, not completion.

The coefficient group is `Additive (rootsOfUnity n L)` with its discrete
topology and natural Galois action. Require `NeZero n` for finite descent
and `IsGalois K L` throughout. A comparison onto **all** power classes
requires every base-field unit to have an nth root in L; in the eventual
separable-closure specialization the standard sufficient hypothesis is n invertible in K. We must
prove that specialization, or retain the explicit root-existence hypothesis;
we must not assert it for a general Galois extension or inseparable roots.

| Leaf / new module | Statement and source match | Dependencies | Cap |
|---|---|---|---|
| E08a / GroupScheme/KummerCoefficients | Natural additive root action, finite discrete coefficients and continuous orbit maps. RootsOfUnity.Basic: restrictRootsOfUnity, coe_injective, finite instance; FLT/Mathlib/FieldTheory/Galois/Infinite: algebraic discrete continuity; ContinuousSMulDiscrete.isOpen_smul_eq. | READY | 200 |
| E08b / GroupScheme/KummerCoefficientDescent | Embed every root coefficient into E07b's actual finite fixed field, prove injectivity and equivariance, and map the descended cocycle into field units. IntermediateField.mem_fixedField_iff, mem_cocycleAction_ker, restrictNormalHom_surjective. | E08a | 200 |
| E08c / GroupScheme/KummerRefinement | Root ratios commute with a field embedding and restriction of automorphisms; compare parameters and root choices by division. Normal.Defs: restrictNormal_commutes; KummerCocycle: exists_kummer_parameter. | E08b | 200 |
| E08d / GroupScheme/ContinuousKummerParameter | Apply finite Hilbert 90 to the embedded cocycle and inflate its nonzero root and parameter to L. KummerCocycle.exists_kummer_parameter; finiteGaloisCocycle_restrict. | E08b/E08c | 200 |
| E08e / GroupScheme/KummerRootClass | Construct a continuous root-ratio cocycle; show changing roots or multiplying a parameter by an nth power preserves its continuous class. Use open evaluation fibers and E03. | E08a/E08c | 200 |
| E08f / GroupScheme/ContinuousKummerClass | Descend to E05 power classes, prove injectivity using fixed elements, and surjectivity using E08d. Explicit E06 quotient, with root existence as a visible arithmetic hypothesis. | E08d/E08e | 200 |
| E09a / GaloisRepresentation/Extensions/CharacterLines | Construct rank-one character actions and their Hom character; simultaneous twists cancel, including unramified twists. Character values are units; inertia triviality is explicit. | READY after E08 | 200 |
| E09b / GaloisRepresentation/Extensions/CharacterBasis | Coefficient equivalences transport cocycles, splitting changes and continuous classes; compute the two-line basis factor. | E09a | 200 |
| E09c / GaloisRepresentation/Extensions/OrdinaryTwist | Relate transport to Kummer unit membership where the coefficient identification is available; distinguish prime-field root coefficients from arbitrary residual-field scalars. | E08f/E09b and concrete coefficient identification | 200 |

Additional bounded specializations are source-matched before proof:

| Leaf / new module | Statement and source match | Dependencies | Cap |
|---|---|---|---|
| E08g / GroupScheme/AlgebraicClosureKummer | Supply root existence in an algebraically closed Galois extension; specialize to AlgebraicClosure K for perfect K (in particular characteristic zero). IsAlgClosed.exists_pow_nat_eq, PerfectField's algebraic separability instance, IsGalois.mk. | E08f | 200 |
| E09d / GroupScheme/KummerUnitTransport | Natural powers of parameters and root cocycles agree; unit membership is preserved and reflected for powers invertible modulo n. Subgroup.pow_mem and the nth-power quotient relation. | E08f | 200 |
| E09e / GaloisRepresentation/Extensions/LiftBasisTransport | Transport E04's actual lift cocycle through a coefficient equivalence, and compute its b/a factor after rescaling both line bases. LiftCocycle_unique/spec and linearity; no ramification classification. | E09b | 200 |

E09d handles cyclic coefficient changes only. It does not provide the
arbitrary-k coefficient-extension comparison needed by E09c.

E09c is an adapter gate: roots of unity are a cyclic group, not an
arbitrary finite-field line. Extending coefficients to k and proving the
unit subspace is stable under k-scalars needs a tensor/cohomology comparison;
it cannot be assumed or replaced with an arbitrary scalar action on roots.
E1's independent peu-ramification comparison remains outside this split.

## Historical baseline and admission (2026-09-30)

At task start, checked 2026-09-30 UTC: HEAD = GitHub `main` =
`c557fcd66261f7de888076c086a7eb28df6539af`; `origin/main` agrees.
The local branch named `main` is older; it is not the audited baseline.
Checks: `git rev-parse HEAD origin/main`; `gh api repos/futarchy-fi/FLT/commits/main --jq .sha`.
Mathlib: `c32e1ec0d1eb5237ba344eee50162f45d5b0fc76`.
All file:line references and readiness claims below refer to this snapshot.
Freshness checked 18:26:35 UTC: main advanced to `d4e575010ee5015026d7afa23ac17eb0ceac4700`;
only `docs/MAZUR_GOAL_LEDGER.md` changed, so the audited Lean sources still match main.
Evidence: `gh api repos/futarchy-fi/FLT/compare/c557fcd66261f7de888076c086a7eb28df6539af...d4e575010ee5015026d7afa23ac17eb0ceac4700 --jq '[.files[].filename]'`.

The exact admitted declaration is `GaloisRepresentation.IsHardlyRamified.lifts`,
`FLT/GaloisRepresentation/HardlyRamified/Lift.lean:37` (body `sorry`, line 48).
Its full context and result, with only whitespace changed, are:

```lean
namespace GaloisRepresentation.IsHardlyRamified
universe u v
variable {k : Type u} [Finite k] [Field k]
    [TopologicalSpace k] [DiscreteTopology k]
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    [Algebra ℤ_[p] k] [IsLocalHom (algebraMap ℤ_[p] k)]
    (V : Type v) [AddCommGroup V] [Module k V]
    [Module.Finite k V] [Module.Free k V] (hV : Module.rank k V = 2)
open TensorProduct
theorem lifts (ρ : GaloisRep ℚ k V) (hρirred : ρ.IsIrreducible)
    (hρ : IsHardlyRamified hpodd hV ρ) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsLocalRing R)
      (_ : TopologicalSpace R) (_ : IsTopologicalRing R)
      (_ : Algebra ℤ_[p] R) (_ : IsLocalHom (algebraMap ℤ_[p] R))
      (_ : Module.Finite ℤ_[p] R) (_ : Module.Free ℤ_[p] R)
      (_ : IsModuleTopology ℤ_[p] R)
      (_ : Algebra R k) (_ : IsScalarTower ℤ_[p] R k) (_ : ContinuousSMul R k)
      (W : Type v) (_ : AddCommGroup W) (_ : Module R W) (_ : Module.Finite R W)
      (_ : Module.Free R W) (hW : Module.rank R W = 2)
      (σ : GaloisRep ℚ R W) (r : k ⊗[R] W ≃ₗ[k] V),
    IsHardlyRamified hpodd hW σ ∧ (σ.baseChange k).conj r = ρ := sorry
end GaloisRepresentation.IsHardlyRamified
```

Consumer: `FLT/Assembly/ExistingInputs.lean:31` proves `hardlyRamifiedLifting`
by applying this admission at line 33. `FermatsLastTheorem.lean:19` supplies
that adapter at line 24 to `PNat.pow_add_pow_ne_pow_of_three_inputs`
(`FLT/Assembly/ThreeInputFinal.lean:24`). The actual call to the lifting input
is `FLT/Assembly/PrimeField.lean:48`, through `FLT/Assembly/Proof.lean:27`.
The generic `HardlyRamified/PrimeField.lean:53` is a separate caller.

Build checked 2026-09-30 18:21:14 UTC: `LEAN_NUM_THREADS=2 lake build FermatsLastTheorem`
(foreground; `Scratch/lifts-goal-build.log`), exit 0, 10,293 targets.
Audit command (foreground, from this baseline):
`LEAN_NUM_THREADS=2 lake env lean Scratch/LiftsGoalAudit.lean > Scratch/lifts-goal-audit.log 2>&1`.
The scratch file imports `FermatsLastTheorem` and `Lean`, prints axioms of the
final theorem, `lifts`, and its adapter, then runs the type-and-body constant
walker from the prior GOAL-AUDIT on the final theorem and adapter. It rejects
missing constants and compares its axiom set with Lean's `collectAxioms`.
Checked 2026-09-30 18:32:32 UTC: exit 0; final root 133,419 declarations,
zero missing, axiom set `[Mazur_statement, propext, sorryAx, Classical.choice, Quot.sound]`.
The lifting adapter visits 43,935 declarations, zero missing; its only library
frontier is `lifts` at line 37. Both `lifts` and its adapter have exactly
`[propext, sorryAx, Classical.choice, Quot.sound]`. The legacy `three_adic`
is not reachable from the final goal. Both walks agree with `collectAxioms`.
Scratch is local evidence, deliberately not committed; a minimal independent
rerun is a scratch file containing `import FermatsLastTheorem` and
`#print axioms PNat.pow_add_pow_ne_pow` / `#print axioms FLT.Assembly.hardlyRamifiedLifting`.
The other arithmetic inputs remain `mem_isCompatible` and `Mazur_statement`;
this ledger does not propose proving them as lifting leaves.

## Smallest retained lifting boundary and source ledger

Use **exactly `FreyLifting` and `HasPrimeFieldLift` from LF0's “Restricted
lifting contract”**, not a new interchangeable existential. Thus: `P : FreyPackage`,
`17 ≤ P.p`, canonical `PadicInt.toZMod`, residual `P.freyCurve.galoisRep P.p P.hppos`,
and its irreducibility imply the existential above specialized to `k = ZMod P.p`
and `Type`, with its *same* residual conjugacy. HR is already proved by
`HardlyRamified/Frey.lean:95`. `Proof.lean:57` needs only these Frey inputs;
`Assembly/Proof.lean:30` currently discards the ≥17 bound and must later be rewired.
This is the weakest retained **lifting interface**, not a logically least
sufficient proposition: LF0's `FreyResidualTraceInput` is the weaker endgame
consequence, but combines lifting, companions and three-adic arithmetic.
No arbitrary finite fields, p=3 case or universes are needed for this goal.

Sources checked directly: Khare–Wintenberger, *Serre's modularity conjecture I*,
Invent. Math. 178 (2009), 485–504 ([author manuscript](https://www.math.ucla.edu/~shekhar/papers/results.pdf), **I**);
and *II*, ibid. 505–586, DOI 10.1007/s00222-009-0206-6
([author manuscript](https://www.math.ucla.edu/~shekhar/papers/proofs.pdf), **II**).
The numbering below is the downloaded author manuscripts (23 and 98 pages),
not an assertion that journal pagination matches. Downloads and extracted text:
`Scratch/kw-{results,proofs}.{pdf,txt}`, checked 2026-09-30.

| Step / source | Exact hypothesis obligation or delta |
|---|---|
| Residual oddness and absolute irreducibility; I §4 (definition of odd), II Theorem 6.1 (S-type input) | Already proved in `HardlyRamified/AbsoluteIrreducibility.lean:68,99`, using `RationalComplexConjugation.lean:75`. Do not redispatch CORE L0. GL2 only exposes the determinant equality. |
| Finite-flat residual input has Serre weight 2; II Proposition 3.6 and §3.2.2 (low-weight crystalline local problem); Serre, *Sur les représentations modulaires de degré 2*, Duke 54 (1987), §2 (weight definition) | For the discrete prime field, specialize `IsFlatAt.cond` to the zero ideal (`Deformations/RepresentationTheory/GaloisRep.lean:396`), transport through the quotient/tensor identity, then identify the resulting finite-flat model with Serre's weight-2 condition. II §3.2.2 explicitly uses finite flatness to select weight 2. A fully matched Lean dictionary, including the reverse integral assertion for the lift, remains a design gate; Proposition 3.6 alone is not that dictionary. |
| Cyclotomic-restriction absolute irreducibility; I Lemma 6.2(ii) | Over the algebraic closure, reducible restriction forces weight `(p+1)/2` or `(p+3)/2`; weight 2 and p≥17 exclude both. First prove the weight dictionary. Never add this restriction as a premise of `FreyLifting`, nor require an unproved “large image” assumption. |
| Fixed determinant and local rings; II Theorem 3.1, Proposition 3.6, §3.3.4 | Choose ψ=1, hence determinant χp; S={2,p,∞}. At p use weight-2 crystalline; at 2 use the fixed-character semistable type of §3.3.4; elsewhere impose unramifiedness. Need integral finite-flatness at **every open coefficient quotient**, not just Hodge–Tate weights. |
| Exact local type at 2; II Theorem 3.1 and §3.3.4 (twist of semistable deformations) | Use the residual quotient δ from `Defs.lean:115`, lift it to a fixed unramified quadratic γ, and impose upper-triangular type `(γχp, γ)` even when the residual representation is unramified at 2. The source imposes γ²χp=φ, hence γ²=1 for φ=χp. Recovering the **surjective integral quotient** over the chosen coefficient order remains a bridge; minimal/unramified deformation or inertia trace 2 alone does not fix Frobenius eigenvalues. |
| Global deformation dimension; II Proposition 4.5 | Prove the arithmetic Selmer presentation and dimension ≥1 for these local rings. Existing `Deformations/Representable.lean:38` is unrestricted; line 114 is admitted and is not an input to reuse as proved. |
| Residual modular seed, comparison and finiteness; II Theorems 6.1, 8.2, 10.1; Proposition 9.2 | Theorem 10.1 gives finite Zp-module global ring after these hypotheses. Construct the totally real auxiliary fields with the local/disjointness properties used in its proof. This is not potential modularity of an already-assumed desired global lift. |
| Characteristic-zero point; II Corollary 4.7, §10.3.1 | Dimension plus finiteness makes p nonnilpotent. Extract a prime avoiding p, then a finite characteristic-zero coefficient domain; GL3 is only the prime-extraction sublemma. Abstract representability or finiteness alone is insufficient. |
| Integral coefficients and residual identification; II Corollary 4.7 and I Theorem 5.1(1) | An O′-valued point may enlarge the residue field. Preserve the original residual Fp model via the finite local image/order of the deformation ring, with residue Fp, or prove coefficient descent. Taking O′ itself does **not** automatically give `Algebra O′ (ZMod p)`. Prove freeness, module topology, continuity, HR and the actual tensor-conjugacy witness over that order. |

Use **II Theorem 10.1 + Corollary 4.7 with §3.3.4 at 2** as the lifting
source. I Theorem 5.1(1) alone is insufficient: a minimal unramified lift at 2
need not have the required quadratic quotient. This sharpens LF0 K1. The unresolved weight/local-integral dictionaries
above are explicit gates; this ledger does not certify a complete matched proof.
Do not obtain an auxiliary-ramified lift and silently call it hardly ramified.
Compatible-family source/hypothesis work stays in LF0; no duplicate queue here.

## Historical dispatch queue (GL1–GL4 now proved)

All paths below are **new proposed modules**, under `FLT/GaloisRepresentation/HardlyRamified/`.
Caps include headers/imports/proofs. GL1–GL3 are independently ready; they prove
small algebraic facts, not existence of lifts. No library edits were made by L0.

**GL1 — `PrimeResidueMap.lean`, cap 180, READY; no queue dependencies.**
Import `Mathlib.NumberTheory.Padics.RingHoms`. Exact statement:
```lean
theorem primeResidueMap_unique (p : ℕ) [Fact p.Prime]
    (f : ℤ_[p] →+* ZMod p) : f = PadicInt.toZMod
```
Use `PadicInt.toZMod_spec` to subtract the canonical integer representative;
the difference lies in `(p)`, killed by f. This fixes the coefficient map in
residual deformation interfaces without assuming continuity or a second algebra.
Anchors: `Padics/RingHoms.lean:318,327,442`,
`Padics/PadicIntegers.lean:513` (`maximalIdeal_eq_span_p`).
For the final cast, change the target to `f x = (x.zmodRepr : ZMod p)`.
Do not reimplement the existing `PadicInt.residueField` equivalence.

**GL2 — `ResidualOddness.lean`, cap 120, READY; no queue dependencies.**
Import `HardlyRamified.AbsoluteIrreducibility`. In its exact variable context
(`AbsoluteIrreducibility.lean:61–65`, also `[Module.Free k V]`), prove:
```lean
theorem det_complexConjugation (hρ : IsHardlyRamified hpodd hV ρ) :
    ρ.det ThreeAdicPlan.rationalComplexConjugation = -1
```
Proof: specialize `hρ.det`, rewrite `rationalComplexConjugation_cyclotomic`,
`map_neg`, `map_one`. Consumer: the oddness field of the source's residual seed.
Reuse `hρ.isAbsolutelyIrreducible` separately; do not prove it again.

**GL3 — `LiftPrimeAvoidingP.lean`, cap 100, READY; no queue dependencies.**
Import `Mathlib.RingTheory.Nilpotent.Lemmas`. Exact statement:
```lean
theorem exists_prime_avoiding_p (D : Type) [CommRing D] (p : ℕ)
    (h : ¬ IsNilpotent (p : D)) :
    ∃ P : Ideal D, P.IsPrime ∧ (p : D) ∉ P
```
Use `nilpotent_iff_mem_prime` (that file:59) and classical negation.
Source: II Corollary 4.7; Atiyah–Macdonald, *Introduction to Commutative Algebra*,
Proposition 1.8. Its nonnilpotence premise remains the arithmetic ring construction's obligation.

**GL4 — `LiftDomainFree.lean`, cap 300, READY after GL3; algebra only.**
Import `HardlyRamified.B5Inputs` for the existing quotient/PID infrastructure.
With `(p : ℕ) [Fact p.Prime] (D : Type) [CommRing D] [Algebra ℤ_[p] D]`
and `[Module.Finite ℤ_[p] D] (P : Ideal D) [P.IsPrime]`, exact sketch:
```lean
theorem quotient_free_of_prime_avoiding_p (hp : (p : D) ∉ P) :
    Module.Free ℤ_[p] (D ⧸ P)
```
Show the coefficient map injective using `PadicInt.ideal_eq_span_pow_p`, then
finite torsion-free over the PID implies free. Source: II Corollary 4.7's proof.
Reuse the argument in `B5Inputs.lean:76–90`; its `exists_domain_quotient` at 52
assumes D already free, so cannot supply this weaker-input lemma. Locality and
residue compatibility are follow-ups, not hidden conclusions of GL4.

After GL1–GL4, dispatch through the existing LF0 D1/D2/P1/K1 queues only
when the dictionary gates above have source-matched contracts. Their arithmetic
nonvanishing must supply GL3's premise; these four ready algebra leaves do not.
Final assembly will prove `freyLifting : FreyLifting` from the constructed ring,
HR specialization and residual witness, then rewire B4 and audit FLT. It must
not use `lifts`, `mem_isCompatible`, or unconditional FLT to construct that ring.

Read-only API evidence (rerun from baseline; `M=.lake/packages/mathlib/Mathlib`):
`rg -n 'toZMod_spec|ker_toZMod|toZMod_eq_residueField_comp_residue' "$M/NumberTheory/Padics/RingHoms.lean"`;
`rg -n 'maximalIdeal_eq_span_p|ideal_eq_span_pow_p' "$M/NumberTheory/Padics/PadicIntegers.lean"`;
`rg -n 'nilpotent_iff_mem_prime' "$M/RingTheory/Nilpotent/Lemmas.lean"`;
`rg -n 'complexConjugation_fixed_finrank|isAbsolutelyIrreducible|exists_domain_quotient' FLT/GaloisRepresentation/HardlyRamified`.
Acceptance per new module: foreground `lake build MODULE`, then
`lake exe runLinter MODULE` **one module at a time**, and scratch `#print axioms`
of its endpoints showing only standard axioms. Never lint the whole library.

Ready-contract check, 2026-09-30 18:34:57 UTC: `LEAN_NUM_THREADS=2 lake env lean Scratch/LiftsReadySketches.lean`
exited 0 (`Scratch/lifts-ready-sketches.log`): GL1–GL3 proofs and GL4's type elaborate;
`#print axioms GaloisRepresentation.IsHardlyRamified.isAbsolutelyIrreducible` has only the three standard axioms.
