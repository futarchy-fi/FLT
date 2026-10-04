# GOAL-L0: lifting for the positive-natural FLT goal

This is a delta to [LF0](LIFT_FAMILY_PLAN.md), especially its restricted lifting
contract and K1, and [CORE](CORE_PLAN.md), L0–L6. It does not replace those plans
or their shared lifting/family budget. Queue IDs below are **GL**, not their L IDs.

## W59 — C1 circularity audit and restored arithmetic priorities

Checked 2026-10-04 against `HardlyRamifiedWittPoint`,
`HardlyRamifiedWittLift`, `HardlyRamifiedWittResidual`, and the exact `lifts`
statement in `HardlyRamified/Lift.lean`. These are distinct assertions:

- **Bare C1** asks for a continuous global characteristic-zero lift of the
  residual representation. It omits HR local conditions and finite free
  p-adic coefficients. It is not literally the `lifts` theorem, and no
  equivalence with that theorem has been proved. An unrestricted lift may
  have extra ramification; it cannot witness an HR quotient point.
- **C1 together with C2–C6** asks for that same lift with determinant,
  away-inertia, the prescribed quotient at two, and every finite-flat open
  reduction. `flatPointOfFramedLift` then constructs a characteristic-zero
  point of the actual HR quotient. Conversely its universal representation
  already has these conditions, and `flatObject_exists_charZero_iff` proves
  point existence equivalent to exclusion of every p-power from the flat
  ideal. This is precisely the unresolved nonvanishing assertion, not an
  independent proof of it.
- **The exact `lifts` endpoint** additionally requires a finite free p-adic
  coefficient order, original residue field and tensor-conjugacy witness,
  in independent universes. These integral and universe obligations prevent
  calling the current proartinian point criterion an exact equivalence with
  `lifts`. C0's Eisenstein targets do not construct a representation or a
  specialization map.

Thus using C1–C6 to prove the HR quotient's characteristic zero is circular
as a proof strategy unless their existence is independently established.
There is no proof that global Selmer/modularity is the only possible route;
it is the source-matched route retained here (KW II Proposition 4.5,
Theorem 10.1 and Corollary 4.7). Deprioritize C1–C6. Work in order on
S0a2/S0a3, effective R1 quotient-twist descent, Lp0 crystalline comparison,
Noetherianity and the finite coefficient order, then the specified global
Selmer contracts. Do not dispatch numerical weight evaluation or arbitrary-p
Raynaud classification as available APIs. No global admission is removed by
this audit.

### W59 local comparison and remaining boundary

Validation is checked by `python3 Scratch/LiftsW59/check.py`, which prints
its checked-at time and verifies source hashes and saved foreground Lean
receipts. It does not rerun Lean; the untracked W59 result lists commits and
build commands. Require that check before treating this inventory as validated.

| Item | New module under `FLT/AbsoluteGaloisGroup/` | Scope |
|---|---|---|
| S0a2 completeness | `CompletionIntegersAdic` | Proves the actual valuation topology is maximal-ideal adic, derives algebraic completeness and Henselianity at every number-field finite place, and constructs primitive tame roots in the base. |
| S0a2 normality | `TameRootGaloisModel` | The exact chosen root field is Galois; constructs its open normal level, actual integral uniformizer and finite/absolute character comparison. |
| S0a2 common level | `TameCommonLevel` | Constructs a finite comparison field containing any specified model and the chosen root; proves the actual ramification-exponent formula. |
| S0a2 transfer | `UniformizerCharacterTransfer`, `FiniteUniformizerTransfer` | Proves the valuation-power relation under an injective local integral map, then constructs the actual nested finite-level maps, their equivariance and commuting residue inclusions. |
| S0a2/S0a3 comparison | `TameSpecifiedModelComparison` | Eliminates the common-level character to obtain chi_model^k = tameCharacter^e in the actual absolute residue field, with both exponents positive and their valuations specified. |

This removes the previous general-number-field normality gap and supplies
transfer of uniformizer characters to the specified finite model. It does
not cancel noninvertible exponents, extract every representation's normalized
inertial type, or prove numerical Serre-weight evaluations. S0a3's niveau-two,
non-peu and symmetric-power composition-factor gates remain first in priority.
R1 effective twisted Hopf descent, Lp0 PD-envelope universality/Frobenius/B_cris,
arithmetic Noetherianity, and the finite order carrying a lift remain open.

[Global Selmer contracts](LIFTS_W59_GLOBAL_CONTRACTS.md) specify G0a–G1c,
the separate modularity/finiteness gate, and exact integral assembly. They
also correct a ring mismatch: KW II Theorem 10.1 concerns the **unframed
image** in a global framed local-condition ring, not the full framed HR
quotient. This source distinction must survive the eventual Lean comparison.
The new modules do not remove `sorryAx` from `lifts` or the FLT endpoint.

## W43 — integral ordinary models, weight specification, and universe transport

The W43 status supersedes the “next bounded gates” statuses in the historical
W42 section below. Validation receipt: `python3 Scratch/LiftsW43/check.py`;
its output supplies the checked-at time and verifies saved logs/source hashes,
not a fresh Lean run. The receipt must pass before these items are considered
validated.

| Item | Constructed result | Still required |
|---|---|---|
| R1a1 | `GroupScheme.OrdinaryFiltrationModels`: schematic submodel and contracted quotient in the specified middle model, canonical integral extension, original injection/projection and coefficient-linear point maps. | Automatic ordinary filtration extraction, integral coefficient endomorphisms, multiplicative/étale model identifications, unramified twist descent. The existing W42 exact filtration is the input. |
| R1b1, partial | `GroupScheme.IntegralQuotientPointFiber`: actual tensor-product fibre over an integral point of the contracted quotient, finite faithfully flat over the base. | Specialize to the point one of an identified constant quotient, construct the multiplicative torsor action, derive an integral unit, and prove normalized generic-class compatibility. No unit witness is supplied. |
| S0a1 | `SerreWeight.NormalizedRecipe`: source-matched finite branch table, scalar and p=3 cases, normalized bounds. | Arithmetic extraction, normalization and full twist invariance. This is branch data, not a Serre-weight evaluation. |
| S0a3 specification | [Numerical convention](LIFTS_NUMERICAL_WEIGHT_CONVENTION.md): least classical weight >=2 via symmetric-power composition factors. | Existence and comparison theorem before implementing `serreWeight`. |
| C1u | `HardlyRamified.ResidualCyclotomicUniverses`: absolute irreducibility on the cyclotomic kernel at the exact independent universes of `lifts`. | No remaining universe gate for this restriction theorem. It does not construct a lift. |
| Lp0 / L20 | [Local conditions](LIFTS_LOCAL_CONDITION_CONTRACTS.md) matches KW II; `SpecifiedTwoQuotient` preserves a fixed quotient under conjugation and coefficient extension. | Integral crystalline comparison, character-lift construction and arithmetic local rings. |
| D1a first leaf | `Deformations.OpenIdealCondition`: quotient by a proper open ideal corepresents its actual kernel condition; factor, uniqueness, continuity and naturality proved. | Arbitrary closed ideals, identification of arithmetic local ideals and effectivity. |

The global lifting admission is unchanged. The restrictions against supplied
isomorphisms, supplied evaluations and conclusion-bearing model fields remain.
All new modules are <=200 lines; existing Lean modules are unchanged except
sorted imports in `FLT.lean`.

## W42 — actual ordinary representations and corrected downstream gates

W42 constructs the actual continuous Hom-valued class of an exact two-line
filtration, proves section independence and the b/a basis-change formula, and
constructs simultaneous twists with unchanged Hom class. `OrdinaryGaloisClass`
discharges orbit continuity from `GaloisRep`. The local representation predicate
uses the independent cup test; `ordinaryRepresentationPeuRamified_iff_unit`
proves its equivalence with the existing unit condition. No comparison
isomorphism, evaluation, extension class or unit witness is an input field.
The whole local Hom character must be cyclotomic; equality only on inertia is
insufficient for this theorem.

Proof inventory: `Extensions.OrdinaryFiltration`, `OrdinaryFiltrationClass`,
`OrdinaryGaloisClass`, `OrdinaryFiltrationBasis`, `OrdinaryFiltrationTwist`,
`OrdinaryFiltrationUnit`, and
`LocalClassFieldTheory.OrdinaryRepresentationUnitCriterion`.
The first six paths are under `FLT/GaloisRepresentation/`.

The [source contract](LIFTS_ORDINARY_SOURCE_MATCH.md) matches the integral
parameter to the **fppf** Kummer sequence (Stacks 040N), and the independent
odd-prime weight-set recipe to BDJ Theorem 3.17, including scalar inertia,
peu/tres, split/nonsplit, p=3 and niveau-two branches. It splits the integral
model/fibre/parameter/generic-compatibility steps. The numerical `serreWeight`
convention still needs its own checked specification. Neither finite-flat
arithmetic nor a weight evaluation is asserted by the new Lean modules.

### Correction to W41: C1 has a proved direct route

The source re-audit finds more than W41's prime-field spectrum:

- `ThreeAdicPlan.coefficient_flat_trace_ne_zero` constructs the nonzero trace
  at a cyclotomic inertia generator over the **original coefficient field**.
- `coefficient_flat_spectrum` gives mapped characteristic-polynomial roots,
  their trace/determinant, and ratio different from −1. It does **not** assert
  the prime-field p±1 ratio classification over arbitrary coefficients.
- `GaloisRep.flat_cyclotomic_restriction_absolute_of_isFlatAt` combines that
  trace with the proved quadratic self-twist/Clifford obstruction and descends
  from algebraically closed coefficient extensions.
- `IsHardlyRamified.residual_cyclotomic_restriction_absolute` applies it to
  every finite residual field with `k V : Type`; the existing mod-three
  reducibility theorem excludes p=3 under residual irreducibility. This route
  does not depend on the missing Serre-weight recipe.

The last theorem quantifies over coefficient extensions in universe u, but its
original k and V are in Type 0. `lifts` has independent arbitrary universes for
k and V. Preserve that distinction: the remaining C1 work is universe/endpoint
transport if the full polymorphic endpoint is retained, not another arithmetic
restriction proof. The p=3 ordinary trace theorem still has zero trace; the
HR theorem excludes that case globally rather than changing the local theorem.

`ExistingAxioms.lean` checks the HR restriction theorem, its flatness frontend,
and `hardlyRamified_exists_universalTraceLift`: all use only propext,
Classical.choice and Quot.sound. The unrestricted universal deformation theorem
is thus a proved input, but not a local-condition or characteristic-zero theorem.

### Next bounded gates after this re-audit

These replace stale dependency claims below, not the exact `lifts` statement.
Every eventual Lean module has cap 200; refine a leaf further if needed.

| Leaf | Concrete next artifact | Status/dependencies |
|---|---|---|
| C1u | Transport the proved Type-0 HR restriction to the exact residual universes, constructing the finite field/module replacements and all HR/restriction comparisons. | Arithmetic C1 is proved; inspect existing universe transports before coding. Never supply an equivalence as a new endpoint premise. |
| Lp0 | Exact local functor specification for weight-2 crystalline deformations and the integral finite-flat models at every open ideal, matched to KW II §3.2.2/Prop. 3.6. | Specification first. R1 and integral crystalline comparison remain missing. |
| L20 | Compare the actual condition at 2 with KW II §3.3.4: fix the unramified quadratic quotient character, not merely inertia trace 2. | A source/API mismatch checklist is bounded and ready; no local ring is asserted. |
| D1a | Construct quotient/closed-condition functors on the existing unrestricted universal ring and prove their universal property for the specified local conditions. | Needs Lp0/L20 and proofs of closure. `isCorepresentable_narrowSLiftFunctor` still has `sorry`. |
| G0 | Specify actual global/local adjoint cohomology, localization and dual local conditions; identify a source for their finiteness/exactness. | Ready as source/interface audit. `PoitouTateData.orderFormula` assumes the formula, so its projection theorem is not arithmetic duality evidence. |
| G1 | Construct the Selmer tangent/obstruction presentation, then prove the KW II Prop. 4.5 dimension bound. | Blocked on G0 arithmetic duality and D1a. Do not turn the order formula into an assumed record field. |
| M0 | Hypothesis-by-hypothesis KW II Thms. 6.1/8.2/10.1 and Prop. 9.2 map: residual seed, auxiliary totally real fields, disjointness, local conditions, comparison. | Source/interface work; no implemented modularity lifting theorem was located. Coordinate compatible-family work rather than duplicate it. |
| D3/D4 | Prove global p-adic finiteness and p-nonnilpotence, then use the existing prime-avoiding-p/domain-free lemmas. | Depends on local rings, G1 and M0 arithmetic, not unrestricted representability alone. |
| I0 | Recover a coefficient order with the original residue field, a free rank-two module, continuity and the exact residual conjugacy. | Integral descent remains required; the normalization may enlarge the residue field. |

Checked at 2026-10-04T03:25:27Z. Source-contract recheck:
`python3 Scratch/LiftsW42/audit-next.py`. All seven modules (565 lines,
maximum 129/200) passed individual builds, linters and audits of 30 named
declarations, with only propext, Classical.choice and Quot.sound. Saved Lean
validation and the final source hashes are checked by
`python3 Scratch/LiftsW42/check.py`; it does not rerun Lean. Final check time and
integration commits are recorded in the untracked W42 result. The global lifting
admission and `Mazur_statement` at the positive-natural FLT endpoint remain.

## W41 proved scope — character evaluation and the independent unit annihilator

W41 proves arbitrary finite-character carry evaluation, the root-ratio-first
Kummer–Artin minus sign, and both directions of the independent prime and
residual-field unit annihilator. The result uses the existing predicates
`IsPeuRamifiedClass`, `primeUnitSubspace`, `IsExtendedUnitClass`, and
`OrdinaryUnitClass`; none was defined to make the comparison automatic.

`characterFixedField` constructs the finite cyclic kernel field and proves
faithfulness of the descended character. `characterArtinValue_carry` evaluates
the carry on its actual positive finite Artin map, with canonical integers.
`characterCarry_artin_tower_evaluation` transports the result to arbitrary
finite Galois overfields, without cyclicity of the larger field.
`finiteStage_character_evaluation` starts with a character on a caller-selected
finite Galois stage, proves containment of the kernel field, and evaluates
that stage's existing Artin map. No evaluation or comparison isomorphism is
an input.

`rootCoefficientH2_injective` proves that inclusion into field-unit
coefficients reflects zero on actual continuous H²: Hilbert 90 and a root
correct the bounding cochain into root coefficients. `rootLocalInvariant`
then constructs an injective invariant on root-coefficient H².
`rootLocalInvariant_kummer` gives the negative positive-Artin value.
`continuousKummerCup_zero_iff_artin` connects zero detection to the existing
homogeneous continuous-cohomology cup.

For E1d1, the unramified Frobenius degree character detects integer order
modulo the root prime. Dividing by a power of a uniformizer proves precisely
the independent unit-representative criterion. Continuous character descent
identifies the unramified-quotient tests with the original inertia-annihilator
predicate. For E1d2, finite coefficient coordinates transport every unramified
dual character and actual continuous boundary in both directions. Thus the
extended annihilator is the span of the prime annihilator, identified with
`extendedUnitSubspace`. This is pairing compatibility, beyond a vector-space
comparison alone.

`localPeuRamified_iff_primeUnitSubspace` and
`localPeuRamified_iff_extendedUnitClass` use the existing valuation inertia at
number-field completions with complete integers. The rational-place theorems
discharge completeness internally. `localOrdinaryPeuRamified_iff_unit` uses
the constructed actual Hom coordinates and concludes the existing
`OrdinaryUnitClass` criterion. This closes the ordinary class-level E1
arithmetic contract, including E1d1/d2; it does not construct a global lift.
A standalone inverse-limit reciprocity API is not asserted by these theorems.

Checked at 2026-10-04T02:55:26Z, integrated proof head `d6d49047` after
merging `origin/main` at `cceaae2a`. All 39 modules (3,021 lines,
maximum 128/200) and all 132 named declarations passed foreground module builds,
individual module linters, and axiom audits. Only `propext`, `Classical.choice`,
and `Quot.sound` occur. Proof commits: `cb016c1b`, `6cbfd5df`.

Read-only evidence check: `python3 Scratch/LiftsW41/check.py` checks source
hashes, saved successful build/lint/axiom results, declaration coverage,
permitted proof edits, sorted imports, line caps, the post-merge build-input
snapshot and downstream-audit source hashes. It checks saved Lean results;
it does not rerun Lean. The required post-merge `LEAN_NUM_THREADS=2 lake build FLT`
ran once and passed without name clashes. The endpoint build and final audit
passed. The lifting endpoints still depend on `sorryAx`, and
`PNat.pow_add_pow_ne_pow` additionally retains `Mazur_statement`.

### Subsequent lifting gates: checked source contracts, no dispatch

The historical tables below retain their original snapshots. This section
supersedes their claims that the E1 arithmetic comparison is absent.
The exact global endpoint remains `GaloisRepresentation.IsHardlyRamified.lifts`,
with arbitrary finite residual field and every odd prime, and is unchanged.

The re-audit finds a proved positive input beyond the old order-three audit:
`ThreeAdicPlan.FF.primeInertia_tame_spectrum` works at rational places for
p > 3, prime-field rank two, and the actual cyclotomic determinant. It proves
a characteristic-polynomial factorization at one inertia element, eigenvalue
ratio order p−1 or p+1, and nonzero trace. It does not identify the ordinary
extension class as a unit class or implement a Serre-weight recipe. The
order-three `model_presentation` remains a distinct theorem over ℤ₃.
Searches find no `serreWeight`, `IsPeuRamifiee`, or
`ordinary_extension_unit_iff` declaration. The continuous class-level names
above are the implemented E1 API; the old representation-level names are
still sketches. Broad finite-flat/unit searches only find the pre-existing
order-three Kummer example and the zero model, not R1's theorem.

The next work is split into the following reviewable contracts. These are
proposed work, not implemented declarations or ready arithmetic adapters.
Proof modules remain capped at 200 lines and must split further if needed.

| Leaf | Concrete artifact or theorem contract | Existing input and remaining condition |
|---|---|---|
| E1r1 / ordinary representation extraction | Construct the continuous Hom-valued class from an actual two-line filtration; prove its class is unchanged by changing the splitting. | Reuse `liftCocycle`, `continuous_liftCocycle`, `ContinuousClass`, `ordinaryHomCoordinates`; construct the injection and quotient-line normalization from the filtration. No supplied extension-class comparison. |
| E1r2 / representation unit criterion | Apply `localOrdinaryPeuRamified_iff_unit` to E1r1's class, with basis/twist independence from `OrdinaryTwist`. | E1r1; retain the actual cyclotomic Hom-character equality. Define the representation predicate via the independent cup test, never via units or finite flatness. |
| S0a / full recipe specification | Source-matched branch table for the independent two-dimensional Serre recipe, including scalar/exceptional, ordinary peu/tres and niveau-two cases; identify each needed representation invariant. | E1 supplies only the ordinary cup test. No Serre-weight definition exists; specification/review must precede S0 implementation and S1 evaluation. Not dispatched. |
| R1a / integral ordinary extension extraction | From an actual finite-flat ordinary model, construct the rank-one submodel and quotient with their actual generic-point characters and coefficient actions. | Existing finite-flat subobject/quotient and character-factor APIs; the required multiplicative/étale identifications and arbitrary-residual-field transport still need proof. |
| R1b / integral extension parameter | Prove that the Kummer class of R1a's actual generic extension has an integral-unit representative, using an independently constructed integral extension parameter. | Missing arithmetic theorem; E1 is only the final unit-to-peu adapter. No unit witness may be added as a model field or a premise. Foundation requires its own source match and split. |
| R2a / full inertia classification audit | Separate existing prime-field rank-two characteristic-polynomial statements from full representation isomorphisms, all finite residual fields, and p=3. Record precise missing transport and classification statements. | `FF.primeInertia_tame_spectrum`, `original_reducible_charpoly`, fundamental-character APIs. No arbitrary-prime Raynaud classification dispatch or completeness claim. |
| C1a / cyclotomic restriction route check | Determine whether the available nonzero-trace inertia element and Clifford theory can supply the needed restriction irreducibility in the exact endpoint context; otherwise retain the source-matched KW route. | Residual absolute irreducibility and the prime-field spectrum are narrower than arbitrary-k `lifts`. This is a research contract, not an assumed C1 theorem. |

S1/S2/S3, R1/R2, C1 and deformation gates remain blocked on their stated
missing inputs. In particular unrestricted representability does not prove
local conditions, global dimension, finiteness, or integral crystalline
models. `isCorepresentable_narrowSLiftFunctor` still contains an admission.
No Serre-weight evaluation, arbitrary-prime Raynaud classification, global
lifting theorem, or endpoint rewiring was implemented or dispatched.

Downstream source audit checked at 2026-10-04T02:49:31.164024+00:00, at `d6d49047`:
`python3 Scratch/LiftsW41/audit-next.py` reruns the recorded read-only searches
and saves their exact commands, results and source hashes in
`Scratch/LiftsW41/next-gates-audit.json`. These are source-contract findings,
not a fresh axiom audit of the older Raynaud/deformation declarations.

## W40 proved scope — finite normalization and the Kummer boundary sign

W40 identifies the actual finite uniformizer carry with
`relativeFundamentalOrdinaryClass`. The proof compares continuous and ordinary
representatives, transports the finite field through its actual inclusion into
the unramified union, and uses injective absolute inflation with positive
invariant `1/n`. No comparison isomorphism or evaluation is assumed.

The existing `finiteArtin` sends a uniformizer to **negative** arithmetic
Frobenius. `positiveFiniteArtin` explicitly negates that map, retains its
surjectivity and algebraic norm kernel, and commutes with every finite tower.
Its uniformizer theorem covers every positive degree, including degree one.
The Frobenius used in the original subfield of the closure is transported from
the existing arithmetic Frobenius through the canonical field equivalence.

The Kummer calculation proves a further, separate statement: the existing
root-ratio-first continuous cup, included into field-unit coefficients, has
H² class equal to the **negative** positive parameter-carry class. The bounding
cochain is the chosen root raised to integer representatives of the character;
algebraic closedness supplies the root. This does not yet evaluate the
parameter carry's invariant at the Artin image for an arbitrary character.

Validation: ten modules, 954 lines, maximum 123/200; all 52 named declarations
passed individual foreground builds, one-module linters, and axiom audits.
Only `propext`, `Classical.choice`, and `Quot.sound` occur in the new declarations.
Proof commits: `d6121062`, `e7e871fd`. Integration merged `origin/main` at
`2363004c` in `7dcb31c6`. Checked at 2026-10-04T00:58:30Z;
`python3 Scratch/LiftsW40/check.py` checks source hashes, saved successful
build/lint/axiom logs, declaration coverage, line caps, permitted proof edits,
sorted root imports, and the post-merge build-input snapshot. It checks saved
root/endpoint results rather than rerunning Lean. The lifting endpoints still
have `sorryAx`; `PNat.pow_add_pow_ne_pow` also retains `Mazur_statement`.

### Remaining work, in order

1. Prove character evaluation for the positive parameter carry: for a finite
   character factoring through an actual finite Galois extension, its absolute
   invariant must equal the rational-circle image of that character evaluated
   on `positiveFiniteArtin` of the parameter. The uniformizer computation in
   an unramified stage does not prove this for arbitrary characters. The new
   `kummerCarryCup_class` supplies the required cup-order minus sign once this
   evaluation is proved. Construct any needed finite-character descent and
   coefficient/cohomology comparisons, without evaluation premises.
2. Finish the Kummer H² coefficient-inclusion/vanishing comparison and the
   continuous reciprocity assembly needed by E1c7, then derive E1d's independent
   unit-class annihilator statement and its scalar extension.
3. Only after E1 closes, re-audit and split the later lifting gates. The
   Serre-weight evaluation and arbitrary-prime Raynaud classification APIs
   remain unavailable; no dispatch or ready-API claim is made for them here.

## W39 proved scope — invariant composite and unrestricted Artin towers

W39 computes the negative connecting composite of the actual invariant
sequences, identifies its ordinary two-class with the independently
constructed smaller-field fundamental class, and proves compatibility of
the actual finite Artin maps in every finite tower. Shared-prime relative
degrees are included; no degree cancellation or assumed comparison is used.

The explicit positive carry with uniformizer coefficients has negative Tate
value at arithmetic Frobenius for degree > 1. This is a cocycle evaluation,
not yet an
evaluation of `finiteArtin`: the finite-stage carry still needs identification
with the independently constructed fundamental class. Positive reciprocity
normalization must retain this sign. E1c7/E1d and removal of `sorryAx` remain
open. Kummer–Artin evaluation and later lifting gates have not advanced.

Checked 2026-10-04T00:08:56Z at integrated proof head `5ab1664a`, after merging
`origin/main` at `bd950c51`. Read-only evidence check:
`python3 Scratch/LiftsW39/check.py` verifies source hashes, saved successful
module build/lint/axiom logs, declaration audit coverage, permitted proof-commit
edits, sorted imports, line caps and the post-merge Lean/build-input snapshot.
It checks saved root/endpoint results; it does not rerun Lean. All 17 new
modules (1,493 lines; maximum 109/200) and all 56 named declarations passed;
the only axioms used by those declarations are `propext`, `Classical.choice`,
`Quot.sound`. Foreground root and endpoint builds passed; no whole-library
lint ran. The final endpoint audit still lists `sorryAx` for the lifting
statements and additionally `Mazur_statement` for `PNat.pow_add_pow_ne_pow`.

- `invariantNegativeComposite_eq_negativeCupQuotient` computes the two actual
  negative connecting maps using subgroup norm lifts; the quotient norm then
  composes with the subgroup norm to give the ambient norm.
- `twoExtension_boundary_negative_cup` identifies that composite with cup by
  the ordinary connecting class. `relativeFundamentalInvariantTwoClass_negativeCup_deflation`
  gives the unscaled arithmetic square.
- `quotientInflationH2_injective` proves ordinary inflation injectivity from
  subgroup H¹ vanishing by correcting and descending a bounding cochain.
  Arithmetic subgroup Tate vanishing supplies that hypothesis.
- `finiteTowerQuotientGroup` and `finiteTowerQuotientCoefficients` identify the
  quotient group and its fixed coefficients with the smaller-field data.
  Their inflation, scalar, cup and deflation squares use the actual maps.
- `relativeFundamentalOrdinaryClass_quotient` identifies the two independently
  constructed classes using injective inflation and their normalizations.
  `relativeFundamentalTateCup_tower` and `finiteArtin_tower` compare the actual
  cups and their inverses without a coprimality restriction.
- `unramifiedStageCarry_positive_frobenius` evaluates the explicit positive
  uniformizer carry (degree > 1) to the **negative** uniformizer Tate class.
  Its negated Frobenius input gives the positive class. Neither statement replaces the
  missing arithmetic fundamental-class identification.

### Remaining work after W39

1. Identify the finite-stage uniformizer carry with the independently defined
   relative fundamental class through actual inflation and the absolute
   invariant. Establish positive-Frobenius reciprocity with an explicit sign
   convention: the current inverse-cup `finiteArtin` has no built-in negation.
2. Prove Kummer–Artin evaluation with the cup-order sign, then E1d's
   annihilator statement.
3. Re-audit and split later lifting gates only after E1 closes. No Serre-weight
   evaluation or arbitrary-p Raynaud classification API is assumed.

The W38 sections below record the earlier state; the first tower gate listed
there is superseded by W39.

## W38 proved scope — quotient descent and invariant-class normalization

**W38 proves unscaled descent of the upper-field negative cup to a quotient
and constructs a quotient two-class with the required inflation normalization.
The comparison with the independently constructed smaller-field cup remains
open, including shared-prime towers. E1c7/E1d and removal of `sorryAx` remain
open; the ordered Frobenius and Kummer evaluations have not advanced.**

Checked 2026-10-03T22:39:46Z at integrated proof head `040b6a6f`, after merging
`origin/main` at `588bfe04`. Read-only evidence check:
`python3 Scratch/LiftsW38/check.py` verifies source hashes, saved successful
build/lint/axiom logs, declaration audit coverage, permitted proof-commit edits,
sorted imports and line caps. It also checks that Lean/build inputs match the
post-merge integration snapshot; it does not rerun Lean. The 12 new modules
contain 1,006 lines and 46 named declarations, each audited with only
`propext`, `Classical.choice`, `Quot.sound`. Each module has at most 113 lines
(cap 200). The sequential foreground root and endpoint builds passed.

- `tateZeroDeflation_eq_zero_iff` identifies the kernel of actual Tate H⁰
  deflation with subgroup corestriction; `tateScalarMap_quotient_eq_zero_iff`
  identifies the scalar quotient kernel with the subgroup image.
- `negativeCupQuotient` descends the deflated negative cup along the actual
  scalar quotient map. Its unscaled square holds for every ordinary two-class;
  no coprimality or cancellation in a torsion group is used.
- `relativeFundamentalQuotientCupEquiv` proves that this descended map is an
  equivalence for the local fundamental class. `finiteQuotientArtin_descendedCup`
  computes the **existing projected** Artin map by its inverse. This does not
  identify it with the smaller field's independent Artin map.
- The two invariant coefficient sequences are proved short exact. The second
  divides its scalar projection by `|N|` in **ℤ**, using proved subgroup Tate
  vanishing for divisibility and norm lifts for surjectivity. These sequences
  define `relativeFundamentalInvariantTwoClass` without an assumed evaluation.
- `relativeFundamentalInvariantTwoClass_inflation` proves
  `infl(u_quotient) = |N| • u_original` by actual maps of the exact sequences.
  This constructs and normalizes a candidate quotient class; it does not yet
  identify its negative cup with `negativeCupQuotient`.

### Remaining work after W38

1. Compute the negative connecting composite of the two invariant sequences
   as `negativeCupQuotient`, then identify that composite with cup by their H²
   class. Transport the inflation normalization through the actual group and
   coefficient maps and use inflation injectivity to identify the class with
   the smaller-field fundamental class. Compare the independent cups and
   invert to prove unrestricted Artin tower compatibility. Degree cancellation
   is still invalid in the shared-prime case.
2. Prove unramified uniformizer evaluation with positive Frobenius, retaining
   W35's negative carry-cup sign. Then prove Kummer–Artin evaluation with the
   cup-order sign and E1d's annihilator statement, in that order.
3. Re-audit and split later lifting gates only after E1 closes. No Serre-weight
   evaluation or arbitrary-p Raynaud classification API is assumed.

The final audit still lists `sorryAx` for `IsHardlyRamified.lifts` and
`FLT.Assembly.hardlyRamifiedLifting`; `PNat.pow_add_pow_ne_pow` additionally
retains `Mazur_statement`. Evidence: `Scratch/LiftsW38/FinalAxioms.{lean,log,exit}`.
No approval decision is needed. This is a partial advance in the first gate.

## W37 proved scope — partial tower comparison

**W37 proves the degree-weighted negative fundamental-cup tower comparison,
annihilates its defect by the gcd of the two tower degrees, and identifies
the independently constructed Artin maps for coprime towers. The unrestricted
tower identity, positive-Frobenius evaluation, Kummer–Artin evaluation and
E1d remain open. The lifting goal still retains `sorryAx`.**

Checked 2026-10-03T21:33:16Z at integrated proof head `39f3bdba`.
Read-only evidence check: `python3 Scratch/LiftsW37/check.py` checks saved
exit-zero logs, source hashes, allowed edits, sorted imports and line caps;
it does not rerun Lean. All 27 named declarations in nine new modules
(706 lines, each <=200) use only `propext`, `Classical.choice`, `Quot.sound`.
The required post-merge foreground `LEAN_NUM_THREADS=2 lake build FLT`
passed (11,386 jobs), including the root import and FLT endpoint.

Let `m = [F:E]`, `n = [E:K]`, and let `D(x)` denote the difference between
`finiteTateNormTower K E F (cupF x)` and
`cupE (tateScalarMap (AlgEquiv.restrictNormalHom E) x)`.

- `relativeFundamentalOrdinaryClass_inflation` transports the proved arithmetic
  inflation identity to the ordinary two-classes used by the cup construction.
- `finiteTateNormTower_inflated_class` computes the negative cup of an inflated
  class with its actual relative-degree factor, using cocycle sums.
- `relativeFundamentalTateCup_tower_nsmul` proves `m • D(x) = 0`.
  `relativeFundamentalTateCup_tower_gcd` strengthens this to
  `gcd(m,n) • D(x) = 0` by proving group-order annihilation on actual Tate H⁰.
- `relativeFundamentalTateCup_tower_of_coprime` proves the unweighted square
  when `m.Coprime n`. Inverting the existing fundamental-cup equivalences gives
  `finiteArtin_tower_of_coprime`, comparing the actual field-wise Artin maps
  through the abelianized restriction of automorphisms.
- `tateTwoClassMap_deflation_inflation` proves the quotient-level formula
  `defl(cup(inf(a),x)) = |N| • cup(a,scalarMap(quotient,x))` on actual Tate
  groups. Its class is explicitly inflated; it does **not** prove unscaled
  deflation of the local fundamental class.

No cup isomorphism, comparison square or evaluation is assumed. Coprimality
is an explicit arithmetic restriction of the new unweighted theorem, not
an assertion that arbitrary towers satisfy it. The new declarations do not
change W36's Artin normalization or any existing Lean proof module.

### Remaining work after W37

1. Remove the shared-prime tower defect. W37's gcd annihilation supplies no
   cancellation when `gcd([F:E],[E:K]) > 1`; this includes nontrivial prime-power
   towers. Prove the unscaled fundamental-cup quotient/tower comparison, then
   invert it to obtain the unrestricted Artin tower identity. Equal norm
   kernels and surjectivity still do not identify the two maps.
2. Prove unramified uniformizer evaluation with positive Frobenius. Preserve
   the sign obligation from `cyclicCarry_negative_cup_sign`: the constructed
   negative Tate cup sends the positive carry to the negative scalar class.
3. Prove Kummer–Artin evaluation with the cup-order sign, then E1d's
   annihilator statement. E1c7/E1d remain open. The later lifting gates have
   not been reclassified or split; that re-audit remains conditional on E1
   closing. No Serre-weight evaluation or arbitrary-p Raynaud API is assumed.

The final audit at this head gives `[propext, sorryAx, Classical.choice,
Quot.sound]` for `IsHardlyRamified.lifts` and its assembly adapter;
`PNat.pow_add_pow_ne_pow` additionally retains `Mazur_statement`.
Evidence: `Scratch/LiftsW37/FinalAxioms.{lean,log,exit}`.
No approval decision is needed; this is a partial advance in the first gate.

## W36 proved scope

**W36 identifies the subgroup Artin map with the independently constructed
field-wise Artin map over the canonical fixed-field DVR, proves the norm
diagram for arbitrary (including nonnormal) fixed fields, and proves the
surjectivity and exact fixed-field norm kernel of the actual quotient Artin
map. The quotient/tower identity between independently constructed Artin maps,
positive-Frobenius evaluation, Kummer–Artin evaluation, E1d and the overall
lifting goal remain open.**

Checked 2026-10-03T20:59:44.653485+00:00; integrated proof head `ed0850ab`.
Read-only evidence check: `python3 Scratch/LiftsW36/check.py` checks saved
exit-zero logs, source hashes, allowed edits, sorted imports and line caps;
it does not rerun Lean. All 77 named declarations in 14 new modules
(1445 lines; each <=200) use only `propext`, `Classical.choice`, `Quot.sound`.

- `finiteSubgroupArtin_fixedUnitEquiv` transports every subgroup-invariant unit
  through the actual fixed-unit equivalence and `subgroupFixedFieldEquiv`.
  Its field-wise map is `finiteFixedFieldArtin`, which constructs the canonical
  integer DVR and its residue/completeness structures internally and calls
  the existing `finiteArtin`. No cup isomorphism or evaluation is assumed.
- `finiteArtin_fixedField_fieldwise_norm` compares the two actual Artin maps
  and the algebraic fixed-field norm, without normality. The forgetful Galois
  map is `H.subtype.comp (subgroupFixedFieldEquiv F H).symm.toMonoidHom`;
  `subgroupFixedFieldEquiv_restrictScalars` identifies this with forgetting
  the intermediate scalars. The coset product is proved by enumerating all
  fixed-field embeddings, rather than assuming the fixed field is Galois.
- `finiteQuotientArtin` is the actual composite of `finiteArtin` with
  `Abelianization.map (QuotientGroup.mk' H)`, for normal H. Its surjectivity
  and norm kernel are proved in `finiteQuotientArtin_surjective` and
  `finiteQuotientArtin_eq_zero_iff`. Identifying it with the independently
  constructed Artin map of the lower extension is still unproved.
- `tateZeroDeflation` and `finiteTateNormTower` construct the actual
  degree-zero norm-quotient projections and prove their surjectivity and
  invariant-class formulas. They do not assert a fundamental-cup diagram.

### Remaining work after W36

1. Prove the negative fundamental-cup quotient/tower comparison. For a finite
   local tower K ⊆ E ⊆ F, with E/K and F/K Galois, the missing identity is
   schematically
   `finiteTateNormTower K E F (cupF x) =
   cupE (tateScalarMap (AlgEquiv.restrictNormalHom E) x)`, where `cupF` and
   `cupE` are the already constructed `relativeFundamentalTateCupNegTwoEquiv`
   for their respective integer DVRs and field presentations. This requires
   a proof of the local fundamental class's deflation comparison, not a new
   comparison premise. Inverting those proved cups will then give the actual
   Artin tower identity. The existing inflation formula multiplies by [F:E];
   arbitrary cancellation in Tate degree zero is invalid. Equal norm kernels
   and surjectivity also do not identify two maps: they permit a target
   automorphism. W36's quotient-kernel theorem does not close this gap.
2. Prove unramified uniformizer evaluation with positive Frobenius. W35's
   `cyclicCarry_negative_cup_sign` remains relevant: the current negative
   Tate cup sends the positive carry to the negative scalar class. A positive
   normalization of the Artin map must be justified, not silently inferred
   from the degree-zero normalization.
3. Prove Kummer–Artin evaluation with its cup-order sign, then E1d's
   annihilator statement. E1c7/E1d remain open. Only after E1 closes should
   the next lifting gates be re-audited and split; no Serre-weight evaluation
   or arbitrary-p Raynaud classification API was assumed or dispatched.

The rebuilt endpoint audit still gives `sorryAx` for
`GaloisRepresentation.IsHardlyRamified.lifts` and
`FLT.Assembly.hardlyRamifiedLifting`; `PNat.pow_add_pow_ne_pow` retains
`Mazur_statement`, `sorryAx` and the three standard axioms. W36 is a proved
advance in the local class field theory program, not completion of the full
brief or the lifting goal. No approval decision is needed.

## W35 historical scope

**W35 proves the subgroup corestriction diagram for the actual degree-minus-two
fundamental cup, constructs the subgroup Artin map without an invertibility premise,
and proves the algebraic norm diagram for normal fixed fields. The full two-field
tower comparison, positive-Frobenius normalization, Kummer–Artin evaluation, E1d,
and the overall lifting goal remain open.**

The scalar comparison preserves the bar generator at `g`; the constructed cup
sends it to the invariant class of `∑ h, c(h,g⁻¹)`. For the positive cyclic carry,
`cyclicCarry_negative_cup_sign` proves that this is the **negative** scalar class.
Thus positive normalization cannot be inferred from W34's degree-zero unit
normalization; the negative-degree convention must be handled explicitly.

Checked 2026-10-03T20:04:29.451293+00:00; integrated proof head `951458d6`.
Read-only evidence check: `python3 Scratch/LiftsW35/check.py` verifies saved
exit-zero logs, source hashes, allowed edits, sorted imports and line caps;
it does not rerun Lean. All 63 named declarations in 17 new modules
(1289 lines, each <=200) use only `propext`, `Classical.choice`, `Quot.sound`.

The Artin norm theorem is specifically `finiteArtin_fixedField_norm`: its left
side is W34's existing `finiteArtin` applied to the algebraic norm from the
normal fixed field. Its right side is the actual abelianized subgroup inclusion
applied to `finiteSubgroupArtin` on fixed units. The latter is constructed from
the inverse cup of the restricted original fundamental class; its invertibility,
surjectivity and norm kernel are proved. Identification with a separately
constructed `finiteArtin` over that fixed field has **not** yet been transported
through the fixed-field Galois equivalence.

### Next proofs after W35

1. Transport `finiteSubgroupArtin` through `subgroupFixedFieldEquiv` and the
   fixed-unit equivalence to the separately constructed field-wise `finiteArtin`.
   Extend the algebraic norm identification to nonnormal fixed fields. The
   subgroup corestriction/cup square itself is proved in
   `tateTwoClassMap_corestriction`; no all-degree transfer API is needed for it.
2. Prove the quotient/tower diagram on the actual Artin maps. The existing
   inflation identity for fundamental classes multiplies by the relative degree;
   canceling that scalar in Tate degree zero is not justified. The needed
   deflation/inflation comparison remains to be constructed.
3. Prove the unramified uniformizer evaluation with **positive Frobenius**,
   accounting for `cyclicCarry_negative_cup_sign`; then prove Kummer–Artin
   evaluation and its cup-order sign. No positive-Frobenius theorem for the
   current inverse-cup `finiteArtin` is claimed.
4. Prove E1d's annihilator statement, then continue `docs/LIFTS_GOAL_LEDGER.md`.
   No Serre-weight evaluation or arbitrary-p Raynaud classification API was assumed.

The rebuilt endpoint audit still gives `sorryAx` for
`GaloisRepresentation.IsHardlyRamified.lifts` and
`FLT.Assembly.hardlyRamifiedLifting`; `PNat.pow_add_pow_ne_pow` retains
`Mazur_statement`, `sorryAx` and the three standard axioms. The remaining work
is mathematical, not waiting for approval.

## W34 historical scope

**W34 proves the adjacent-vanishing criterion for arbitrary finite groups,
all-degree acyclicity of the local fundamental extension on every subgroup,
and the actual fundamental cup isomorphism in every integer degree, including -2.
It also constructs the finite Artin map and proves surjectivity and the exact
field-norm kernel. Tower compatibility, Kummer–Artin evaluation, E1d and the
full lifting goal remain open.**

The finite-group proof uses normal norm-splice ascent/descent, induction through
a cyclic quotient for solvable groups, two concrete coefficient sequences, and
Sylow detection. It does not assume Hochschild–Serre, any cup isomorphism, or
any evaluation. The first connecting map is proved invertible using the actual
middle term's acyclicity and composed with the established coinduced shift.

Checked 2026-10-03T19:14:13.835793+00:00; proof commits `b05ea241`, `58cdd300`;
merged head `ac51bb34`. Read-only check: `python3 Scratch/LiftsW34/check.py`.
It checks saved exit-zero logs, source hashes, allowed edits and line caps;
it does not rerun Lean. Every new declaration was independently printed by
`#print axioms` and uses only `propext`, `Classical.choice`, `Quot.sound`.

19 new modules, 1413 lines, 76 named declarations; each module <=200 lines.
Per-module foreground validation used `LEAN_NUM_THREADS=2` and, sequentially,
`lake build MODULE`, `lake exe runLinter MODULE`, and `lake env lean AXIOM_FILE`.
No library-wide lint was run. Logs and exit codes are in
`Scratch/LiftsW34/MODULE-{build,lint,axioms}.{log,exit}`.
Rerun with `python3 Scratch/LiftsW34/validate.py MODULE ...` (short module names).

Fetched `origin/main` over HTTPS after SSH public-key authentication failed,
merged it locally, and ran the required foreground `LEAN_NUM_THREADS=2 lake build FLT`.
The root build, endpoint build, and rebuilt endpoint axiom audit passed:
`Scratch/LiftsW34/{RootBuild,EndpointBuild,FinalAxioms}.{log,exit}`.
No duplicate declaration required renaming.

### Next proofs after W34

1. Prove the finite Artin norm and tower diagrams on the actual constructed maps.
   `finiteArtin_norm` proves that a norm from the defining extension is killed;
   it does **not** prove compatibility between distinct extensions or base fields.
   The next work is the needed restriction/corestriction and inflation comparison
   through the Tate norm splice and the two-extension cup, then transport through
   the inverse cup and scalar abelianization comparison.
2. Prove positive-Frobenius normalization and Kummer–Artin evaluation, including
   the cup-order sign. The map constructed here is the inverse-cup map; its
   evaluation on a uniformizer has not been proved in this wave.
3. Prove E1d's annihilator statement and continue the remaining lifting program.
   No Serre-weight evaluation or arbitrary-p Raynaud classification API was assumed.

The original overall goal remains unmet. The rebuilt audit still gives
`sorryAx` for `GaloisRepresentation.IsHardlyRamified.lifts` and
`FLT.Assembly.hardlyRamifiedLifting`; `PNat.pow_add_pow_ne_pow` still uses
`Mazur_statement`, `sorryAx`, and the three standard axioms. These are remaining
mathematical proofs, not an approval request or a claim that the full brief is done.

## W33 historical scope

Checked 2026-10-03T18:19:05.194888+00:00; base `b91dbdc1`; proof head `49be88b8`.
Read-only evidence check: `python3 Scratch/LiftsW33/check.py` checks saved
build/lint/axiom logs, source hashes, allowed edits, sorted imports and line caps.
It does not rerun Lean. The full lifting goal remains unmet.

**The original fundamental extension has Tate H⁰ = H¹ = 0 on every subgroup
of its finite Galois group. Its Tate groups vanish in every integer degree on
cyclic subgroups. The adjacent-vanishing criterion for arbitrary finite groups
and the degree −2 cup equivalence remain unproved.**

Seven new modules contain 705 lines and 37 named declarations. Every module
has at most 158 lines. All declarations use only `propext`, `Classical.choice`
and `Quot.sound`.

- `SubgroupFixedFieldTower` constructs the fixed field inside the original
  ambient field and its actual Galois equivalence with the given subgroup.
  Restriction of scalars through this equivalence equals subgroup inclusion.
- `TateGroupEquivalence` reindexes cochains and chains in opposite directions,
  proves the norm square, and derives an isomorphism in every Tate degree.
- `FiniteSubfieldDvr` constructs the canonical integer inclusion and proves
  locality, DVR structure, completeness, finiteness and residue properties.
  `RelativeFundamentalSubgroup` instantiates these constructions and transports
  W32's field-wise theorem to the original module restricted to any subgroup.
  No intermediate DVR, cohomological vanishing or cup equivalence is supplied
  by the caller.
- `TateNormVanishing` proves both directions of the norm-surjectivity criterion
  in degree zero and the augmentation-exactness criterion in degree minus one.
- `CyclicTateVanishing` proves the cyclic case of the adjacent-vanishing criterion
  using periodic resolutions and the explicit norm splice.
  `RelativeFundamentalCyclicSubgroup` applies it to the original local extension
  on every cyclic subgroup, with no vanishing premise.

### Next proofs after W33

1. Prove the adjacent-vanishing criterion for arbitrary finite groups from
   degrees zero and one on all subgroups. The cyclic case is now available;
   the passage to noncyclic groups is still missing. A finite-solvable version
   suffices here using the existing `localGalois_solvable` theorem. A
   normal-subgroup descent or another proof must be constructed. The pinned Mathlib
   `GroupCohomology/Basic.lean` still lists Hochschild–Serre as a TODO; its
   cyclic resolutions alone do not provide that passage.
2. Apply the general criterion to `relativeFundamentalExtension_subgroup_isZero`.
   Prove the first boundary invertible and compose it with the existing
   coinduced shift to obtain the actual input-degree −2 cup equivalence.
3. Construct finite Artin maps with norm and tower compatibility, then prove
   Kummer–Artin evaluation with positive Frobenius and the cup-order sign,
   and derive E1d's annihilator statement. These remain unproved.

Validation evidence: `Scratch/LiftsW33/*-{build,lint,axioms}.{log,exit}`
and `Scratch/LiftsW33/{EndpointBuild,Integration,FinalAxioms}.{log,exit}`.
Rerun individual modules with `python3 Scratch/LiftsW33/validate.py MODULE ...`;
rerun endpoint/integration checks with `python3 Scratch/LiftsW33/final_checks.py`.
Builds run in the foreground and lint runs one module at a time, with
`LEAN_NUM_THREADS=2`. The endpoint audit still records `sorryAx` for the
lifting theorem and both `sorryAx` and `Mazur_statement` for the FLT endpoint.

## W32 proved scope (historical)

The following is the W32 snapshot; its checks refer to its reported W32 head.

Checked 2026-10-03T17:42:41.194685+00:00; base `25750cda`; proof head `98a7908a`.
Read-only evidence check: `python3 Scratch/LiftsW32/check.py` checks the saved
build/lint/axiom logs, validated source hashes, sorted imports, allowed edits
and 200-line caps. It does not rerun Lean. The full lifting goal remains unmet.

**Finite-relative fundamental classes now have proved restriction and inflation
tower formulas. The actual local twisted extension has Tate H⁰ = H¹ = 0 after
restriction to Gal(F/E), for a supplied finite local tower K ⊆ E ⊆ F ⊆ C.
The degree −2 cup and the cohomological-triviality criterion remain unproved.**

Twelve new modules contain 1,163 lines and 73 named declarations, including
local tower instances. Every module is at most 132 lines. Every named
declaration uses only `propext`, `Classical.choice` and `Quot.sound`.

- `RelativeRestrictionTower` constructs the actual cochain restriction and
  its square with inflation to the common closure. `RelativeFundamentalRestriction`
  proves res(u_F/K) = u_F/E. The intermediate extension E/K need not be Galois.
- `RelativeInflationTower` constructs finite inflation, proves its composition
  law and H² injectivity. `RelativeFundamentalInflation` proves
  inf(u_E/K) = [F:E] · u_F/K, with the positive normalization.
- `FiniteRestrictionComparison` proves naturality of the finite continuous
  comparison. `RelativeFundamentalOrdinaryRestriction` transports the arithmetic
  identity to ordinary H², where the two-extension representatives live.
- `CoinducedInjectiveRestriction` gives coset coordinates and all-degree
  acyclicity for arbitrary injective finite group maps.
  `CoinducedRestrictionComparison` constructs the quotient comparison and
  proves that its actual Tate maps are isomorphisms in every degree.
- `TwoExtensionRestriction` compares the concrete twisted short exact sequences
  and their boundaries. `TwoExtensionRepresentativeIso` constructs inverse
  translations for cohomologous representatives. `TwoExtensionSubgroupVanishing`
  transports vanishing to the original restricted extension by exactness.
- `RelativeFundamentalExtensionRestriction` applies these comparisons to the
  chosen local representatives and proves the two adjacent vanishing groups
  after restriction to Gal(F/E). Its local theorem assumes neither vanishing,
  an isomorphism, nor an evaluation formula.

The quotient comparison is a proved Tate isomorphism, not an asserted
isomorphism of the two differently constructed coefficient representations.
The final local theorem still takes the DVRs and compatible algebra towers
as inputs. It does not yet package an arbitrary subgroup of Gal(F/K) through
its fixed field and canonical intermediate DVR.

### Next proofs after W32

1. Specialize the field-wise vanishing theorem to every subgroup, constructing
   its fixed-field/DVR instances and transporting along the actual Galois-group
   identification. Then prove the cohomological-triviality criterion from
   adjacent Tate vanishing on all subgroups.
2. Apply that criterion to the twisted extension and compose its first boundary
   with the proved coinduced shift. This must establish the degree −2 cup
   equivalence without adding an invertibility premise.
3. Construct finite Artin maps, prove norm and tower compatibility, prove
   Kummer–Artin evaluation with positive Frobenius and the cup-order sign,
   then derive E1d's annihilator statement. These remain unproved.

All twelve per-module build, lint and axiom checks passed, as did the foreground
`lake build FermatsLastTheorem`, combined import check and final goal audit.
The rebuilt lifting theorem still depends on `sorryAx`; the FLT endpoint also
retains `Mazur_statement`. Endpoint evidence:
`Scratch/LiftsW32/{EndpointBuild,Integration,FinalAxioms}.{log,exit}`.
Module evidence: `Scratch/LiftsW32/*-{build,lint,axioms}.{log,exit}`.
Rerun each module with `python3 Scratch/LiftsW32/validate.py MODULE ...`;
this runs foreground builds and one-module lint with `LEAN_NUM_THREADS=2`.


## W31 proved scope (historical)

The following is the W31 snapshot; its checker refers to its reported W31 head.

Checked 2026-10-03T16:05:18.866549+00:00; base `114f96be`; proof head `c316c543`.
Read-only evidence check: `python3 Scratch/LiftsW31/check.py` verifies saved
per-module build/lint/axiom logs, source hashes, sorted imports and the 200-line
cap. It does not rerun Lean. The full lifting goal remains unmet.

**The concrete coinduced module is Tate acyclic in every integer degree,
including after restriction to every finite subgroup. Its connecting maps are
proved isomorphisms. The relative twisted extension has vanishing Tate H⁰ and
H¹ for the ambient Galois group. The degree −2 cup remains unproved.**

Nine new modules contain 641 lines and 33 named declarations. Each module is
below 200 lines, and every declaration uses only `propext`, `Classical.choice`
and `Quot.sound`.

- `CoinducedShapiro` identifies the orbit-function module with coinduction
  from the trivial subgroup, then uses Shapiro for positive cohomology and
  homology. No projectivity of the coefficient module is assumed.
- `CoinducedNormExact` proves the two splice calculations using point masses:
  the norm is the constant sum, and the augmentation boundary of the explicit
  chain is the function minus its sum supported at the identity.
- `CoinducedTateAcyclic` combines those calculations with Shapiro to prove
  actual Tate vanishing in every integer degree. `CoinducedTateShift` makes
  the concrete boundary an isomorphism and cancels this second boundary in
  the two-extension cup's injectivity and surjectivity conditions.
- `CoinducedSubgroup` supplies an equivariant coset-coordinate isomorphism
  and proves acyclicity on every finite subgroup, without normality.
  `CoinducedSubgroupShift` proves the actual restricted-sequence boundary
  invertible; its source is the restriction of the original quotient.
- `TateScalarVanishing` proves integral scalar Tate H⁻¹ and H¹ vanish.
  `TateExactSequence` supplies the coefficient-map segment of the Tate long
  exact sequence. `RelativeFundamentalExtension` uses Hilbert 90 and W30's
  proved degree-zero cup to prove Tate H⁰ and H¹ of the actual local twisted
  extension vanish. It also proves the actual input-degree −1 cup bijective
  between zero groups. No class-formation conclusion is a hypothesis.

The coinduced module and the twisted extension are different modules. Only
the former is proved acyclic in every degree on every subgroup. The latter's
vanishing in degrees zero and one is presently for the ambient Galois group.
Neither statement supplies the missing degree −2 reciprocity isomorphism.

### Next proofs after W31

1. Prove finite-relative fundamental-class restriction/tower compatibility
   and compare the restricted concrete two-extension with the one constructed
   for each subgroup. This must transport the generator normalization and
   the twisted extension's two adjacent vanishing groups to every subgroup.
2. Prove the cohomological-triviality criterion from that subgroup vanishing,
   and apply it to the twisted extension. Its first Tate boundary, followed
   by the now-proved coinduced shift, must yield all cup isomorphisms,
   especially input degree −2. No invertible boundary may be assumed.
3. Construct finite Artin maps and prove norm/tower compatibility; prove
   Kummer–Artin evaluation with positive Frobenius and the cup-order sign;
   then derive E1d's annihilator statement. These remain unproved.

Combined imports and the final axiom audit passed (`Scratch/LiftsW31/Integration.log`
and `FinalAxioms.log`, both exit 0). `IsHardlyRamified.lifts` and
`hardlyRamifiedLifting` still use `sorryAx`; `PNat.pow_add_pow_ne_pow` still
uses `sorryAx` and `Mazur_statement`. No W31 declaration uses either.

Module evidence: `Scratch/LiftsW31/*-{build,lint,axioms}.{log,exit}`.
Rerun with `python3 Scratch/LiftsW31/validate.py MODULE ...`; it runs each
module's build, lint and axiom check sequentially with `LEAN_NUM_THREADS=2`.
Serre-weight evaluation and arbitrary-p Raynaud classification were not used.

## W30 historical proved scope

Checked 2026-10-03T15:32:51.559692+00:00; base `5cfcd5c0`; proof head `40439142`.
Read-only evidence check: `python3 Scratch/LiftsW30/check.py` verifies saved
logs, source hashes, import order, line caps and axiom coverage; it does not
rerun Lean. The full lifting goal remains unfinished.

**The relative fundamental Tate cup is constructed in every integer degree.
Its ordinary cochain formula is proved in every nonnegative input degree,
and the actual degree-zero cup is proved to be an isomorphism.**
The 18 new modules contain 1,376 lines and 81 named declarations; every module
is below 200 lines and every declaration uses only `propext`, `Classical.choice`,
and `Quot.sound`.

- The orbit inclusion M → (G → M), its quotient Q, and the primitive
  `F(g)(x) = c(x,g)` construct a concrete two-extension for every two-cocycle.
  Its two actual Tate connecting maps define `tateTwoExtensionMap` in every
  integer degree. `TateTwoClassOperation` proves representative independence;
  `TateTwoClassZero` proves that zero classes act by zero.
- `ScalarCochainCup`, `OneCocycleScalarBoundary`, `TwoExtensionCochainCup`,
  `TatePositiveCocycleClass` and `TateCupComparison` prove the ordinary formula
  `z(g₂,…) • c(g₀,g₁)` for every nonnegative input degree and compare it through
  the actual positive Tate isomorphism. The fundamental class is the left
  factor and the trivial scalar class is the right factor.
- `TateCupUnit` and `RelativeFundamentalTateCup` prove that the scalar Tate unit
  maps to W29's normalized relative Tate generator. The all-degree operation
  is named `relativeFundamentalTateCup`.
- `TateClassArithmetic` and `TateScalarDegreeZero` prove generation and norm
  annihilation in actual scalar Tate H⁰. `RelativeTateCupDegreeZero` uses the
  proved local H² generator to establish bijectivity of the actual degree-zero
  cup. `relativeFundamentalTateCupZeroEquiv` has this cup as its forward map.

Every module passed a foreground build, module-only lint and declaration
axiom audit with `LEAN_NUM_THREADS=2`. Combined imports and final endpoint
axiom checks passed. Evidence is in `Scratch/LiftsW30/`; the lifting theorem
still uses `sorryAx`, and `PNat.pow_add_pow_ne_pow` still uses both `sorryAx`
and `Mazur_statement`. No new declaration uses either.

### Next proofs after W30 (historical)

| Gate | Required proof |
|---|---|
| Tate–Nakayama beyond input degree zero | Prove cohomological triviality and dimension shifting for the concrete two-extension using local H¹ vanishing, H² generators and actual finite-relative subgroup/tower compatibility. The crucial input degree −2 isomorphism remains open. |
| Finite Artin maps | Construct reciprocity from that degree −2 isomorphism and establish norm and tower compatibility. |
| Kummer–Artin evaluation | Prove actual cocycle evaluation with positive Frobenius convention and the cup-order sign; compare the Kummer pairing. |
| E1d | Deduce the annihilator statement from the evaluation theorem. |

The general cup construction is a Yoneda cup through explicit short exact
sequences on the actual Tate complexes. Its existence does not prove
bijectivity in other degrees. Local arithmetic retains the complete-DVR,
finite-residue and compatible finite Galois tower scope; the degree-zero
isomorphism uses the characteristic-zero H² saturation theorem.
Serre-weight evaluation and arbitrary-p Raynaud classification remain separate.


## W29 historical proved scope

Checked 2026-10-03T14:36:50.156663+00:00; base `13b878bb`; proof head `4fd72473`.
Read-only evidence check: `python3 Scratch/LiftsW29/check.py` (saved logs and
source hashes; does not rerun Lean). Full lifting remains unfinished.

**I03c and the normalized fundamental-class comparisons are proved.**
The 17 new modules contain 1,292 lines and 76 named declarations, all below
200 lines per module and using only `propext`, `Classical.choice`, `Quot.sound`.

- `TransferCoset`, `TransferCochain`, `TransferRestrictionHomotopy`, and
  `ContinuousTransfer` construct the finite coset sums in degrees one and two,
  prove cocycle and boundary preservation, and exhibit the continuous homotopy
  for transfer after restriction. `IntegralTwoClassAdditive`,
  `ContinuousCorestrictionH2`, and `CorestrictionRestrictionH2` descend these
  formulas to actual categorical H².
- `CocycleRectangle`, `TransferRepresentativeChange`, and
  `TransferChoiceIndependence` prove independence of arbitrary coset sections
  using another explicit continuous one-cochain boundary.
- `FixingSubgroupTopology` and `AbsoluteCorestriction` identify the extension's
  Galois group with its open fixing subgroup and prove
  `cor(res x) = [E:K] • x`. `CorestrictionInvariant` proves
  `inv_K(cor y) = inv_E(y)` for this constructed transfer, using W28 restriction
  surjectivity. Absolute E/K need not be Galois.
- `AbsoluteFundamentalClass`, `FundamentalClasses`, and
  `FundamentalClassBaseChange` construct the relative generator of exact
  degree order, compare its inflation with positive invariant `1/[E:K]`, and
  prove actual restriction/corestriction formulas for the absolute classes.
  Restriction sends `u_K([E:K]*n)` to `u_E(n)`; corestriction preserves n.
- `RelativeTateClasses` identifies actual relative Tate H² with Z/[E:K],
  carrying 1 to the proved fundamental generator, and proves Tate H¹ = 0.
  This comparison does not yet construct the Tate cup-product isomorphisms.

Arithmetic scope remains characteristic-zero complete DVR fraction fields
with finite residue fields and the stated compatible finite DVR towers.
Relative classes use finite Galois extensions. Transfer is constructed on H²;
an all-degree continuous chain map is not claimed.

Every module passed its own foreground build, module-only lint, and declaration
axiom audit with `LEAN_NUM_THREADS=2`; no whole-library lint was run.
Evidence: `Scratch/LiftsW29/M-{build,lint,axioms}.log` and their `.exit` files.
The combined-import and final-axiom checks also passed. The full FLT theorem
still uses `sorryAx` and `Mazur_statement`; the lifting theorem still uses
`sorryAx`. No new declaration uses either.

### Historical next proofs after W29

| Gate | Required construction |
|---|---|
| Class formation / Tate cup | Construct cup with the relative fundamental class on the actual Tate complex, including nonpositive degrees; compare with the positive-degree cochain formula. |
| Class formation / Tate–Nakayama | Prove the degree-shift cup maps are isomorphisms by dimension shifting and cohomological triviality. Prove the needed finite-relative subgroup/tower comparisons on the actual maps; normalized absolute formulas alone do not supply them. |
| Finite Artin and Kummer–Artin | Construct the finite reciprocity maps, prove cocycle evaluation with the recorded sign/Frobenius normalization, then compare the Kummer pairing. |
| E1d | Deduce the annihilator statement from that evaluation theorem. |

API checks: `Scratch/LiftsW29/TateApi.log` and `CupApi.log`. The checked
homological sources provide the Tate complex, its exact sequences and
positive/negative comparisons, but no all-degree Tate cup or class-formation
isomorphism theorem. Those proofs remain work, never assumed hypotheses.
Serre-weight evaluation and arbitrary-p Raynaud classification remain separate.

## W28 historical validation

Checked 2026-10-03T13:55:03.657454+00:00; branch task/goal-lifts-w28; base eb101554; proof head c084ba11.
Read-only evidence check: `python3 Scratch/LiftsW28/check.py` (saved logs and source hashes).

**R04e, R05a–R05c, R06a–R06b, and I03a–I03b are proved. The full lifting goal remains unmet.**
The 22 new modules contain **1,675 lines and 73 named declarations**, all within the 200-line cap.
Every new declaration uses only `propext`, `Classical.choice`, and `Quot.sound`.
I03c has its restriction-surjectivity prerequisite, but corestriction remains unconstructed.

1. The ramified normalized valuation sequence, trivial-integer cyclic cohomology,
   and W27's integral-unit calculation give h(Lˣ) = [L:K].
   Hilbert 90 then gives the exact cyclic relative H² order and finiteness.
2. Wild inertia is a p-group, its tame quotient is cyclic, and the residue
   automorphism group is cyclic. These actual maps prove local Galois solvability.
3. A proper normal subgroup gives two smaller extensions. Constructed intermediate
   DVRs and W25 inflation-restriction exactness support strong degree induction,
   proving finite relative H² and its degree upper bound. W26's lower subgroup
   proves equality and exhausts the relative group with unramified classes.
4. A continuous absolute cocycle descends pointwise to a finite Galois fixed field.
   The spectral norm proves locality of its integral closure; that closure is a
   complete DVR with finite residue field. Finite relative saturation then proves
   surjectivity of actual unramified inflation, hence bijectivity.
5. Inverting this inflation and composing with the normalized unramified
   invariant gives an additive equivalence H²(K, Ksepˣ) ≃ Q/Z.
6. The actual cochain restriction square proves that finite base extension
   multiplies the invariant by [E:K]. E need not be Galois for this formula.
   Divisibility of Q/Z proves restriction surjective; its kernel is exactly
   the classes with degree-torsion invariant.

The arithmetic scope is characteristic-zero fraction fields of complete DVRs
with finite residue fields of prime characteristic p. Finite relative groups
use Galois extensions; the absolute restriction results allow arbitrary finite
intermediate extensions with the stated compatible finite DVR towers.
Positive-characteristic local invariants are not established here.

| Item | Module under FLT.LocalClassFieldTheory | Lines/cap | Commit |
|---|---|---|---|
| R04e | RamifiedOrderSequence | 94/200 | `6cceac89` |
| R04e | CyclicIntegerCohomology | 112/200 | `6cceac89` |
| R04e | RamifiedFieldHerbrand | 86/200 | `6cceac89` |
| R05a | CyclicRelativeOrder | 75/200 | `6cceac89` |
| R05b | LocalGaloisSolvable | 90/200 | `b83cbb87` |
| R05c | FiniteDvrComplete | 58/200 | `f4c88eea` |
| R05c | IntermediateDvrAlgebra | 71/200 | `f4c88eea` |
| R05c | IntermediateDvr | 99/200 | `f4c88eea` |
| R05c | FiniteRelativeSequence | 83/200 | `f4c88eea` |
| R05c | SolvableNormalStep | 42/200 | `f4c88eea` |
| R05c | SolvableFieldStep | 42/200 | `f4c88eea` |
| R05c | RelativeOrderInduction | 109/200 | `f4c88eea` |
| R06a | FiniteRelativeSaturation | 101/200 | `f4c88eea` |
| R06b | FiniteExtensionLocalRing | 70/200 | `c084ba11` |
| R06b | FiniteExtensionDvr | 44/200 | `c084ba11` |
| R06b | FiniteRelativeCocycleDescent | 60/200 | `c084ba11` |
| R06b | UnramifiedInflationSurjective | 83/200 | `c084ba11` |
| I03a | AbsoluteInvariant | 67/200 | `c084ba11` |
| I03b | AbsoluteRestriction | 49/200 | `c084ba11` |
| I03b | UnramifiedAbsoluteSquare | 93/200 | `c084ba11` |
| I03b | InvariantRestriction | 63/200 | `c084ba11` |
| I03c prerequisite | RestrictionSurjective | 84/200 | `c084ba11` |

Each module M passed sequentially in the foreground with LEAN_NUM_THREADS=2:
`lake build FLT.LocalClassFieldTheory.M`,
`lake exe runLinter FLT.LocalClassFieldTheory.M`, and
`lake env lean Scratch/LiftsW28/MAxioms.lean`.
All 73 named declarations, including definitions and instances, were axiom-audited.
No whole-library lint was run. Evidence: Scratch/LiftsW28/M-{build,lint,axioms}.log.

Combined imports passed in Scratch/LiftsW28/Integration.lean.
Scratch/LiftsW28/FinalAxioms.lean confirms that the new endpoints are axiom-clean,
while `GaloisRepresentation.IsHardlyRamified.lifts` and
`FLT.Assembly.hardlyRamifiedLifting` still use `sorryAx`;
`PNat.pow_add_pow_ne_pow` retains both `sorryAx` and `Mazur_statement`.
Both checks have .log and zero .exit files.

`python3 Scratch/LiftsW28/check.py` checks saved logs, source hashes, caps,
audit coverage, allowed axioms, sorted imports, allowed paths, new-file-only
Lean changes, and clean tracked state. It does not rerun Lean.
The source snapshots were recorded after verifying that every build, lint,
and axiom log postdated its source. Fresh module validation is
`python3 Scratch/LiftsW28/validate.py M ...`.

The next proof is **I03c: continuous corestriction**. Restriction surjectivity
and its kernel calculation are available in RestrictionSurjective.
The source search in Scratch/LiftsW28/CorestrictionApiSearch.log found ordinary
Shapiro (`groupCohomology.coindIso`), but no group-cohomology corestriction.
Mathlib's group-homology corestriction is a different construction.

| Gate / next leaf | Required proof and dependency |
|---|---|
| I03c / transfer construction | Construct finite-index transfer on continuous cochains, or prove continuous Shapiro and a coefficient trace; prove preservation of cocycles and boundaries and independence of coset choices. |
| I03c / restriction-degree identity | For that constructed map prove cor(res x) = [E:K] • x. A cochain homotopy or a proved Shapiro comparison is still needed. |
| I03c / CorestrictionInvariant | Use the proved restriction surjectivity and degree formula to deduce inv_K(cor y) = inv_E(y). Transporting the identity through the invariants alone would leave the transfer comparison unproved. |
| I03d / FundamentalClasses | Compare the inverse image of positive 1/[E:K] with relative H² and prove its restriction, inflation, and corestriction formulas. |
| Class formation | Assemble the proved relative order and Hilbert 90 with compatible fundamental classes; prove the Tate cup-product isomorphisms. |
| Kummer–Artin evaluation | Construct the finite Artin maps and prove the cocycle evaluation formula, then the Kummer comparison and E1d annihilator statement. |

Each new module keeps the 200-line cap; the transfer rows are proof obligations,
not existing APIs or certified size estimates. Serre-weight evaluation and
arbitrary-p Raynaud classification remain independent unproved work.

## W27 historical acceptance

Checked 2026-10-03T12:49:39.162743+00:00; branch `task/goal-lifts-w27`; base `e8a80ed9`; proof head `f704730c`.
Read-only evidence check: `python3 Scratch/LiftsW27/check.py` (saved logs and source hashes).

**R03c–R03g and R04b–R04d are proved. The full lifting goal remains unmet.**
The 36 new modules contain **2,755 lines and 168 named declarations**, all within the 200-line cap.
Every new declaration uses only `propext`, `Classical.choice`, and `Quot.sound`.

1. The induced topology on the integer ring is proved adic. Algebraic
   `IsAdicComplete` gives a complete neighborhood of zero in the fraction field,
   hence field completeness and exponential summability without an extra premise.
2. The actual logarithm series converges on `v(x) < v(p)`, uniformly on every
   smaller closed ball. Integral scaled formal series, evaluated in a complete
   topological copy of the DVR, give both analytic exp/log composition identities.
   A proved nonarchimedean Cauchy product gives exponential multiplicativity.
3. The exponential gives a group equivalence and homeomorphism between the
   additive ball `v(x) < v(p)` and the principal units `v(u-1) < v(p)`.
   Preservation of integrality proves continuity of the actual Galois action,
   allowing it through the sums and proving equivariance.
4. Multiplication by the base scalar p² puts the constructed normal lattice
   inside that convergence ball. Its exponential image is an actual open,
   Galois-stable subgroup of field units. The transported integral action is
   proved equal to the natural action, and all positive cohomology vanishes.
5. A complex indexed by Boolean parity has differential generator-minus-one
   in even degree and norm in odd degree. Its two homologies are identified
   with the existing cyclic quotients and every positive even/odd cohomology
   group. The snake lemma gives both connecting maps and all six exactness
   assertions; the return from odd to even is part of the complex itself.
   Connecting-map naturality is proved for morphisms of coefficient sequences.
6. Counting adjacent images gives the six-term alternating cardinal identity
   and Herbrand multiplicativity for finite periodic cohomology. The periodic
   quotient agrees with the usual H²/H¹ quotient for cyclic coefficients.
7. Complete DVRs with finite residue field are compact in the constructed
   topology. Pulling the open exponential subgroup back to integral units
   therefore gives a finite quotient. Its natural Galois short exact sequence
   and the proved subgroup acyclicity identify every positive integral-unit
   cohomology group with that of this finite quotient. The finite cyclic
   coefficient calculation yields `integralUnit_herbrand_eq_one`.

The analytic and unit results use characteristic-zero local fields with prime
residue characteristic p, algebraically complete DVRs, and finite DVR extensions;
the finite quotient step additionally uses finite residue field. They do not
claim the corresponding positive-characteristic analytic statements.

| Item | Module under FLT.LocalClassFieldTheory | Lines/cap | Commit |
|---|---|---|---|
| R03c | AdicFractionFieldComplete | 79/200 | `dd6abf85` |
| R03c | AdicIntegerTopology | 87/200 | `dd6abf85` |
| R03d | LocalLogConvergence | 82/200 | `052822ad` |
| R03d | LocalLogUniformConvergence | 69/200 | `052822ad` |
| R03d | ValuationUniformSeries | 68/200 | `052822ad` |
| R03e | AdicIntegerSpace | 80/200 | `3afe221e` |
| R03e | AdicSeriesEvaluation | 91/200 | `3afe221e` |
| R03e | AdicSeriesField | 78/200 | `3afe221e` |
| R03e | LocalExpEquivalence | 83/200 | `3afe221e` |
| R03e | LocalExpLogInverse | 86/200 | `3afe221e` |
| R03e | LocalExpMultiplicative | 65/200 | `3afe221e` |
| R03e | LocalIntegralInverse | 45/200 | `3afe221e` |
| R03e | LocalIntegralSeries | 102/200 | `3afe221e` |
| R03e | LocalScaledCoefficients | 83/200 | `3afe221e` |
| R03e | LocalScaledSeries | 73/200 | `3afe221e` |
| R03e | LocalSeriesComparison | 91/200 | `3afe221e` |
| R03f | AdicGaloisContinuity | 80/200 | `ee500370` |
| R03f | LocalExpEquivariance | 81/200 | `ee500370` |
| R03f | LocalExpHomeomorph | 75/200 | `ee500370` |
| R03f | LocalExpIsometry | 68/200 | `ee500370` |
| R03g | AcyclicOpenUnits | 85/200 | `6b8a59b7` |
| R03g | LocalExpOpen | 48/200 | `6b8a59b7` |
| R03g | NormalLatticeExpDomain | 92/200 | `6b8a59b7` |
| R03g | NormalLatticeExpOpen | 60/200 | `6b8a59b7` |
| R03g | NormalLatticeExpUnits | 78/200 | `6b8a59b7` |
| R04b | CyclicPeriodicComplex | 73/200 | `c245a55f` |
| R04b | CyclicPeriodicExact | 53/200 | `c245a55f` |
| R04b | CyclicPeriodicHomology | 51/200 | `c245a55f` |
| R04b | CyclicSixTermSequence | 81/200 | `c245a55f` |
| R04c | HerbrandExact | 74/200 | `c2dcf673` |
| R04c | SixTermCard | 58/200 | `c2dcf673` |
| R04d | AdicIntegerCompact | 78/200 | `f704730c` |
| R04d | IntegralExpQuotient | 60/200 | `f704730c` |
| R04d | IntegralExpSequence | 103/200 | `f704730c` |
| R04d | IntegralExpSubrepresentation | 94/200 | `f704730c` |
| R04d | UnitHerbrand | 101/200 | `f704730c` |

Each module M passed sequentially in the foreground with `LEAN_NUM_THREADS=2`:
`lake build FLT.LocalClassFieldTheory.M`,
`lake exe runLinter FLT.LocalClassFieldTheory.M`, and
`lake env lean Scratch/LiftsW27/MAxioms.lean`.
All 168 named declarations, including definitions and instances, were axiom-audited.
No whole-library lint was run. Evidence: `Scratch/LiftsW27/M-{build,lint,axioms}.log`.

Combined new-module imports passed in `Scratch/LiftsW27/Integration.lean`.
`Scratch/LiftsW27/FinalAxioms.lean` confirms the new endpoints are axiom-clean,
while `GaloisRepresentation.IsHardlyRamified.lifts` and
`FLT.Assembly.hardlyRamifiedLifting` still use `sorryAx`;
`PNat.pow_add_pow_ne_pow` retains both `sorryAx` and `Mazur_statement`.
Both checks have `.log` and zero `.exit` files.

`python3 Scratch/LiftsW27/check.py` checks saved logs, source hashes, caps,
audit coverage, allowed axioms, sorted imports, allowed paths, new-file-only
Lean changes, and clean tracked state. It does not rerun Lean.
The source snapshots were recorded only after checking that each build, lint,
and axiom log postdated its source. Fresh module validation is
`python3 Scratch/LiftsW27/validate.py M ...`.

W27 stopped before R04e; the W28 checkpoint above supersedes that remaining-work list.

## W26 historical acceptance

Checked 2026-10-03T11:22:50.341193+00:00; branch `task/goal-lifts-w26`; base `f34a19ea`; proof head `c58387ad`.
Read-only evidence check: `python3 Scratch/LiftsW26/check.py` (saved logs and source hashes).

At the W26 checkpoint, I02c, I02d, R02a, R02b, and R03b were proved; R03c was partial.
W27 above completes R03c–R04d.
The 22 new modules contain **1,505 lines and 58 named declarations**, all within the 200-line cap.
Every new declaration uses only `propext`, `Classical.choice`, and `Quot.sound`.

1. Frobenius restriction is proved for the constructed finite-stage embeddings and
   actual unramified-union restriction, with exponent the residue degree. Naturality
   of the integral connecting map gives the same factor on integral H2 coordinates.
2. The ramification order square is proved on cochains and cohomology. The actual
   local degree identity combines its factor with residue degree to give
   `unramifiedMultiplicativeInvariant_baseChange`, multiplication by `[L:K]` on Q/Z.
3. The multiplication-by-n kernel is the subgroup generated by positive `1/n`,
   with an additive equivalence from `ZMod n` and cardinality n.
4. The base-change/inflation square commutes with restriction to the actual
   Galois kernel. W25 exactness supplies relative preimages of degree-torsion
   unramified classes; the proved inflation injections make them additive and
   distinct. `relativeLowerBound` embeds `ZMod [E:K]` into
   `continuousCohomology ℤ Gal(E/K) (Additive Eˣ) 2` and its range has `[E:K]`
   elements. No finiteness or order of the whole relative H2 is assumed.
5. Clearing the finite coordinate matrix puts a nonzero base scalar times the
   entire ring of integers in the constructed normal lattice. This proves
   maximal-ideal-power containment and openness for `dvrAdicValued`, the topology
   of the actual maximal-ideal valuation on the fraction field.
6. The exact formula `v(n!) = v(p)^padicValNat p n!` and its geometric lower bound
   are proved for residue characteristic p. In characteristic zero the exponential
   terms tend to zero on the explicit positive domain `v(x) < v(p)`.
   `localExp_summable` proves summability when that same adic field topology is
   complete. At W26 the transfer from `IsAdicComplete` to `CompleteSpace` was missing;
   W27 proves that transfer.

| Item | Module under FLT.LocalClassFieldTheory | Lines/cap | Commit |
|---|---|---|---|
| I02c | FrobeniusPowers | 51/200 | `18e22390` |
| I02c | IntegralFrobeniusBaseChange | 56/200 | `18e22390` |
| I02c | UnramifiedFrobeniusEmbedding | 102/200 | `18e22390` |
| I02c | UnramifiedFiniteStageBaseChange | 73/200 | `18e22390` |
| I02c | FrobeniusRestrictionScale | 83/200 | `18e22390` |
| I02c | UnramifiedIntegralH2Restriction | 66/200 | `18e22390` |
| I02d | LocalDegreeFormula | 45/200 | `18e22390` |
| I02d | UnramifiedBaseChangeOrderCohomology | 76/200 | `18e22390` |
| I02d | UnramifiedInvariantRestriction | 78/200 | `18e22390` |
| R02a | RelativeRestrictionKernel | 74/200 | `e6e97be1` |
| R02b | GaloisKernelContinuousEquiv | 35/200 | `e6e97be1` |
| R02b | UnramifiedKernelInflation | 73/200 | `e6e97be1` |
| R02b | UnramifiedBaseChangeInflationSquare | 98/200 | `e6e97be1` |
| R02b | RelativeDegreeTorsionClass | 101/200 | `e6e97be1` |
| R02b | RelativeLowerBound | 102/200 | `e6e97be1` |
| R03b | NormalLatticeDenominators | 64/200 | `791899ba` |
| R03b | NormalLatticePower | 51/200 | `791899ba` |
| R03b | DvrAdicTopology | 53/200 | `791899ba` |
| R03b | NormalLatticeOpen | 55/200 | `791899ba` |
| R03c, partial | DvrFactorialValuation | 64/200 | `c58387ad` |
| R03c, partial | ValuationSeriesComparison | 35/200 | `c58387ad` |
| R03c, partial | LocalExpRadius | 70/200 | `c58387ad` |

Each module M passed sequentially in the foreground with `LEAN_NUM_THREADS=2`:
`lake build FLT.LocalClassFieldTheory.M`,
`lake exe runLinter FLT.LocalClassFieldTheory.M`, and
`lake env lean Scratch/LiftsW26/MAxioms.lean`.
All 58 declarations, including definitions and local instances, were axiom-audited.
No whole-library lint was run. Evidence: `Scratch/LiftsW26/M-{build,lint,axioms}.log`.

Combined new-module imports passed in `Scratch/LiftsW26/Integration.lean`.
`Scratch/LiftsW26/FinalAxioms.lean` confirms that the new endpoints are axiom-clean,
while `IsHardlyRamified.lifts` and `FLT.Assembly.hardlyRamifiedLifting` still use
`sorryAx`; `PNat.pow_add_pow_ne_pow` also retains `Mazur_statement`.
Both checks have `.log` and zero `.exit` files.

`python3 Scratch/LiftsW26/check.py` checks saved logs, source hashes, caps,
audit coverage, allowed axioms, sorted imports, allowed paths, new-file-only
Lean changes, and clean tracked state. It does not rerun Lean.
Fresh module validation: `python3 Scratch/LiftsW26/validate.py M ...`.

W26 remaining contracts were superseded by the W27 scope and remaining table
in `LOCAL_CFT_FOUNDATIONS.md`.

## W25 historical acceptance

Checked 2026-10-03T10:36:06.210425+00:00; branch `task/goal-lifts-w25`; base `cbd0c5ee`; proof head `89849ffd`.
Read-only evidence check: `python3 Scratch/LiftsW25/check.py` (saved validation logs and source hashes).

**R01b–R01e and I02a–I02b are proved. The full lifting goal remains unmet.**
The new work proves continuous H2 image-kernel exactness, unramified base-change
inclusion and restriction, and multiplication of union order by ramification.
It does not prove the Frobenius/residue-degree factor or the degree formula on Q/Z.
E1c7/E1d and the final lifting admission remain.

28 new modules contain **1,979 Lean lines and 82 named declarations**.
Every module is at most 200 lines. Commits are local; nothing pushed.

## Proved scope

1. R01b: extend the restricted bounding cochain and subtract its differential.
   The mixed terms give an explicitly proved crossed homomorphism on the kernel.
   Actual finite Galois Hilbert 90 supplies its principal witnesses, and a
   normalized quotient section constructs a correction killing both mixed terms.
2. R01c: the corrected cocycle is constant on quotient fibers and invariant-valued.
   Descend its values to actual intermediate-field units. The theorem
   `finiteInflationRestrictionExact` proves `Function.Exact` for
   `galoisMultiplicativeInflation ... 2` and `galoisKernelRestriction ... 2`.
   The unique preimage theorem proves independence of section and correction choices.
3. R01d: a subgroup identity neighborhood contains an ambient open-normal trace.
   Refine cochain fibers and coefficient supports simultaneously. The constructed
   fixed field is finite Galois; both the ambient cocycle and the restricted bounding
   cochain descend to it, the latter on the image of the original kernel.
   `galoisTowerCochainDescent` proves the boundary equation at this same finite stage.
4. R01e: use the Galois correspondence to apply the finite correction to that
   normal image subgroup, then inflate its continuous correcting cochain.
   Quotient topology proves continuity of the descended cocycle; no continuous
   section of a profinite quotient is assumed. `continuousInflationRestrictionExact`
   proves exactness on the actual continuous H2 modules for an arbitrary Galois tower.
   Restriction here has the actual restriction kernel as its group; W24's
   `galoisRestrictionKernelEquiv` identifies this group with Gal(L/E).
5. I02a: residue-degree divisibility and Hensel lifting embed a degree-n unramified
   stage into the degree-n stage of the new base. Normality gives literal containment
   in the common separable overfield. This constructs `maximalUnramifiedBaseChange`
   and `unramifiedBaseChangeRestriction`, including the commuting action equation
   and Krull continuity.
6. I02b: the adic valuation extension formula proves `discreteOrder_ramified_scale`
   with the actual ideal ramification index. The base-change map preserves integral
   units; its value on a base uniformizer determines the full union-order homomorphism.
   `unramifiedUnionOrder_baseChange` proves multiplication by
   `(maximalIdeal R).ramificationIdx' (maximalIdeal S)`.
   `unramifiedBaseChangeCohomology` defines the actual continuous cohomology map,
   and `unramifiedBaseChangeCoefficients_order` proves its coefficient order square.

| Item | Module under FLT.LocalClassFieldTheory | Lines/cap | Commit |
|---|---|---|---|
| R01b | KernelCocycleNormalization | 74/200 | `3dcbf174` |
| R01b | KernelMixedCocycle | 69/200 | `3dcbf174` |
| R01b | KernelSectionCorrection | 127/200 | `3dcbf174` |
| R01b | FiniteKernelCocycleCorrection | 77/200 | `3dcbf174` |
| R01c | KernelCocycleDescent | 96/200 | `facf4fa2` |
| R01c | IntegralTwoClassEquality | 64/200 | `facf4fa2` |
| R01c | FiniteInflationCocycleDescent | 51/200 | `facf4fa2` |
| R01c | GaloisKernelRestriction | 71/200 | `facf4fa2` |
| R01c | FiniteInflationRestrictionExact | 100/200 | `facf4fa2` |
| R01d | ContinuousTowerRefinement | 65/200 | `74cf5bd5` |
| R01d | RestrictedCochainDescent | 91/200 | `74cf5bd5` |
| R01d | TowerRefinementFibers | 53/200 | `74cf5bd5` |
| R01d | GaloisTowerCochainDescent | 82/200 | `74cf5bd5` |
| R01e | FiniteSubgroupCocycleCorrection | 53/200 | `74cf5bd5` |
| R01e | ContinuousKernelCocycleCorrection | 81/200 | `74cf5bd5` |
| R01e | ContinuousCocycleQuotient | 48/200 | `74cf5bd5` |
| R01e | ContinuousInflationCocycleDescent | 63/200 | `74cf5bd5` |
| R01e | ContinuousInflationRestrictionExact | 76/200 | `74cf5bd5` |
| I02a | UnramifiedBaseChangeEmbedding | 64/200 | `11d99762` |
| I02a | UnramifiedBaseChange | 78/200 | `11d99762` |
| I02a | GaloisHomContinuity | 58/200 | `11d99762` |
| I02a | UnramifiedBaseChangeRestriction | 71/200 | `11d99762` |
| I02b | RamifiedOrderScale | 47/200 | `89849ffd` |
| I02b | OrderHomScale | 39/200 | `89849ffd` |
| I02b | UnramifiedUnionBaseOrder | 49/200 | `89849ffd` |
| I02b | UnramifiedBaseChangeIntegral | 72/200 | `89849ffd` |
| I02b | UnramifiedBaseChangeOrder | 76/200 | `89849ffd` |
| I02b | UnramifiedBaseChangeCohomology | 84/200 | `89849ffd` |

## Validation

Every module M passed separately in the foreground with `LEAN_NUM_THREADS=2`:
`lake build FLT.LocalClassFieldTheory.M`,
`lake exe runLinter FLT.LocalClassFieldTheory.M`, and
`lake env lean Scratch/LiftsW25/MAxioms.lean`.
All 82 named declarations were audited, including definitions and local instances;
every axiom set is contained in `{propext, Classical.choice, Quot.sound}`.
Evidence: `Scratch/LiftsW25/M-{build,lint,axioms}.log`.
No whole-library lint was run. Acceptance validation was sequential.

Combined imports and endpoint checks passed:
`LEAN_NUM_THREADS=2 lake env lean Scratch/LiftsW25/Integration.lean` and
`LEAN_NUM_THREADS=2 lake env lean Scratch/LiftsW25/FinalAxioms.lean`.
The `.log` and `.exit` files record their output and exit codes.
The final audit still gives `[propext, sorryAx, Classical.choice, Quot.sound]`
for `GaloisRepresentation.IsHardlyRamified.lifts` and
`FLT.Assembly.hardlyRamifiedLifting`; `PNat.pow_add_pow_ne_pow` additionally
uses `Mazur_statement`. New exactness and ramified-order endpoints are axiom-clean.

`python3 Scratch/LiftsW25/check.py` checks saved evidence, source hashes, caps,
audit coverage, allowed axioms, sorted imports, new-file-only Lean changes,
allowed paths, and clean tracked state. It does not rerun Lean.
Fresh per-module validation: `python3 Scratch/LiftsW25/validate.py M ...`.

At the W25 checkpoint, remaining work started at I02c; see the current table in
`LOCAL_CFT_FOUNDATIONS.md`. W25 does not remove the final lifting admission.

## W24 historical acceptance — 2026-10-03T09:27:54.417110+00:00

Checked 2026-10-03T09:27:54.417110+00:00; branch `task/goal-lifts-w24`; base `f3b2fd00`.
Read-only evidence check: `python3 Scratch/LiftsW24/check.py` (PASS).

**Partial completion: inflation is now proved injective, not bijective.**
R01's image-kernel exactness, the ramified relative-order theorem, change-of-base
restriction, corestriction, and fundamental-class comparisons remain unproved.
E1c7/E1d and the final lifting admission have not been removed.

Twenty new modules contain **1,423 Lean lines and 77 named declarations**.
Every module is at most 200 lines. All proof commits are local; nothing pushed.

## Proved scope

1. Closed normal invariant field units are identified equivariantly with the
   units of the fixed field. Every open normal invariant stage has zero H1 by
   finite Hilbert 90; the existing cohomology colimit proves continuous Hilbert
   90 for arbitrary Galois extensions, with an actual unit coboundary witness.
2. Normalization and Hilbert 90 correct an inflated bounding cochain so it
   vanishes on the restriction kernel. It is then constant on quotient fibers
   and invariant-valued, and descends continuously. This proves injectivity of
   the actual categorical H2 map, rather than merely cochain injectivity.
   Krull-topology continuity and the concrete invariant-coefficient and kernel
   comparisons discharge every premise in the Galois specialization.
3. `unramifiedMultiplicativeInflationH2_injective` applies directly to the W23
   morphism. Its composition with inverse unramified coordinates embeds Q/Z
   into absolute multiplicative H2. The actual inflated uniformizer carry has
   exact annihilator nZ. This is not the relative lower bound of Milne III.2.2
   and does not assert that the absolute embedding is surjective.
4. Clearing a base-field denominator gives an integral-valued normal K-basis.
   Its R-span is a finite free Galois-stable submodule of the integral closure.
   Inverse-indexed coordinates identify its actual action with coinduction
   from the trivial subgroup. Shapiro proves positive additive cohomology
   vanishing over both R and Z. This is a constructed lattice, not a claim
   that the entire integral closure has a normal integral basis. Openness and
   a corresponding multiplicative unit subgroup remain unproved.
5. Kernel-image counting proves equal even/odd homology orders for a finite
   periodic module. The actual cyclic comparison gives the finite-module
   Herbrand quotient one, including a proof of finiteness. A separate generic
   exact-sequence theorem proves finiteness and the product cardinal bound
   needed for relative-order induction; no arithmetic exact sequence is assumed
   to exist or instantiated without proof.

| Item | Module under FLT.LocalClassFieldTheory | Lines/cap | Commit |
|---|---|---|---|
| R01a — fixed-field unit comparison | FieldUnitInvariants | 100/200 | `0b076f6e` |
| R01a — continuous Hilbert 90 | ContinuousHilbert90 | 80/200 | `0b076f6e` |
| R01a — normalized two-cocycles | NormalizedTwoCocycles | 66/200 | `0b076f6e` |
| R01a — continuous boundary descent | InflationBoundaryDescent | 94/200 | `0b076f6e` |
| R01a — kernel correction | InflationKernelCorrection | 72/200 | `0b076f6e` |
| R01a — Galois kernel topology | GaloisKernelTopology | 94/200 | `70b327bf` |
| R01a — arbitrary boundary descent | ContinuousInflationBoundary | 53/200 | `70b327bf` |
| R01a — actual H2 injectivity | ContinuousInflationH2 | 76/200 | `70b327bf` |
| R01a — arithmetic coefficient inclusion | GaloisInflationCoefficients | 69/200 | `70b327bf` |
| R01a — Galois inflation injectivity | GaloisInflationH2 | 51/200 | `70b327bf` |
| R06 injection — W23 specialization | UnramifiedInflationInjective | 39/200 | `70b327bf` |
| R04a — finite periodic homology counting | FiniteHomologyCard | 90/200 | `27fc8a93` |
| R04a — finite-module Herbrand quotient | FiniteCyclicHerbrand | 69/200 | `27fc8a93` |
| R05 helper — exact-sequence cardinal bound | ExactSequenceCardBound | 45/200 | `27fc8a93` |
| R02 prerequisite — absolute carries | UnramifiedInflatedCarries | 71/200 | `27fc8a93` |
| R03a — denominator-cleared normal basis | IntegralNormalBasis | 68/200 | `7c0a8f48` |
| R03a — integral normal lattice | IntegralNormalLattice | 66/200 | `7c0a8f48` |
| R03a — equivariant coinduced comparison | IntegralNormalLatticeAction | 114/200 | `7c0a8f48` |
| R03a — additive acyclicity over R | IntegralNormalLatticeCohomology | 47/200 | `7c0a8f48` |
| R03a — additive acyclicity over Z | IntegralNormalLatticeIntCohomology | 59/200 | `7c0a8f48` |

## Validation

Every new module M passed separately in the foreground with `LEAN_NUM_THREADS=2`:
`lake build FLT.LocalClassFieldTheory.M`,
`lake exe runLinter FLT.LocalClassFieldTheory.M`, and
`lake env lean Scratch/LiftsW24/MAxioms.lean`.
All 77 named declarations were audited; their axiom sets are subsets of
`{propext, Classical.choice, Quot.sound}`. No whole-library lint was run.
Evidence: `Scratch/LiftsW24/M-{build,lint,axioms}.log`.

`LEAN_NUM_THREADS=2 lake env lean Scratch/LiftsW24/Integration.lean` checks all
20 new modules together. The final endpoint audit is
`LEAN_NUM_THREADS=2 lake env lean Scratch/LiftsW24/FinalAxioms.lean`.
Evidence: `Scratch/LiftsW24/Integration.log` and `Final-axioms.log`.

`python3 Scratch/LiftsW24/check.py` verifies saved validation evidence, source
caps, declaration audit coverage, allowed axiom sets, sorted imports, allowed
paths, new-file-only Lean changes, clean tracked state, and final FLT axioms.
It reads saved logs; it does not rerun Lean. Fresh validation can be repeated
with `python3 Scratch/LiftsW24/validate.py M ...`, sequentially.

Both combined Lean checks exited 0. The fresh final audit reports:

- `GaloisRepresentation.IsHardlyRamified.lifts` and `FLT.Assembly.hardlyRamifiedLifting`:
  `[propext, sorryAx, Classical.choice, Quot.sound]`.
- `PNat.pow_add_pow_ne_pow`:
  `[Mazur_statement, propext, sorryAx, Classical.choice, Quot.sound]`.
- All audited new endpoints use only the three standard axioms.

Remaining R01–R06/I02–I03 contracts and their dependencies are in the W24
split in `LOCAL_CFT_FOUNDATIONS.md`; the complete handoff is
`LIFTS_W24_RESULT.md` (untracked). No whole gate R01–R06 is marked complete.

## W23 acceptance — 2026-10-03T08:37:58.585982+00:00

Checked 2026-10-03T08:37:58.585982+00:00; branch `task/goal-lifts-w23`; base `3b918b73`.
**E1c7/E1d remain blocked; the final FLT theorem still depends on sorryAx.**

19 new modules; **1421 Lean lines, 90 named declarations**. Every module is at most
200 lines. All changes are local commits; nothing pushed.

| Item | Module under FLT.LocalClassFieldTheory | Lines/cap | Commit |
|---|---|---|---|
| 1a — discrete integral-unit action | DiscreteIntegralUnits | 72/200 | `7b8868fa` |
| 1b — integral-unit descent | IntegralUnitDescent | 92/200 | `7b8868fa` |
| 1c — equivariant invariant coefficients | IntegralUnitInvariants | 87/200 | `7b8868fa` |
| 1d — invariant cohomology comparison | IntegralUnitInvariantCohomology | 46/200 | `7b8868fa` |
| 1e — cofinal open stages | UnramifiedOpenStages | 54/200 | `7b8868fa` |
| 1f — continuous unit acyclicity | UnramifiedContinuousUnits | 81/200 | `7b8868fa` |
| 2a — canonical tower-order compatibility | UnramifiedStageOrderMaps | 62/200 | `7cf81581` |
| 2b — finite representatives of field units | UnramifiedUnionUnits | 60/200 | `7cf81581` |
| 2c — union order homomorphism | UnramifiedUnionOrder | 84/200 | `7cf81581` |
| 2d — discrete field-unit action | DiscreteFieldUnits | 65/200 | `06f226b9` |
| 2e — actual integral-unit kernel | UnramifiedUnionOrderExact | 68/200 | `06f226b9` |
| 2f — equivariant order coefficients | UnramifiedUnionOrderMap | 75/200 | `06f226b9` |
| 2g — short exact continuous sequence | UnramifiedContinuousOrderSequence | 80/200 | `06f226b9` |
| 2h — positive continuous order isomorphism | UnramifiedContinuousOrderH2 | 71/200 | `06f226b9` |
| 2i — uniformizer-power section | UnramifiedOrderSection | 96/200 | `ed103f10` |
| 2j — multiplicative Q/Z invariant and carry | UnramifiedMultiplicativeInvariant | 91/200 | `ed103f10` |
| 2k — finite-stage inflation square | UnramifiedOrderInflation | 92/200 | `ed103f10` |
| 2l — ordinary subgroup restriction square | UnramifiedOrderRestriction | 68/200 | `fb5e079a` |
| 3a — separable-closure inflation map | UnramifiedMultiplicativeInflation | 77/200 | `ed103f10` |

1. The actual canonical integral units have a discrete continuous Galois action.
   Inclusion identifies units of an intermediate field with invariants under its
   fixing subgroup, including the quotient action. The induced cohomology
   isomorphism connects W22's canonical stages to `invariantStageCohomologyDiagram`.
   Constructed open stages are cofinal. W22's unit vanishing and
   `continuousCohomologyColimitIso` prove all positive continuous unit cohomology zero.
2. `discreteOrder_unramified_tower` gives compatibility on canonical stage inclusions.
   Every field unit of the union has a finite representative; compatible orders
   define an actual surjective, Galois-invariant order homomorphism. Its kernel
   is exactly the integral units. The short exact continuous cochain sequence and
   proved acyclicity make order an isomorphism on every positive cohomology group.
3. The continuous H2 order isomorphism composes with W21's additive Frobenius
   coordinates to give `unramifiedMultiplicativeInvariant : H²(G, Uˣ) ≃+ Q/Z`.
   Integer powers of a base uniformizer are an equivariant section, and the
   coefficient image of the actual integral carry has coordinate **+1/n**.
   The cochain evaluation theorem explicitly gives the uniformizer raised to
   each integer cochain value; this is not a normalization assumed of an abstract class.
4. The actual finite-stage inflation maps commute with order on cochains and
   cohomology. Ordinary subgroup restriction also commutes with order, with the
   same coefficient normalization. The continuous order map commutes with the
   invariant-stage colimit comparison.
5. `unramifiedMultiplicativeInflation` constructs the actual cohomology map from
   the unramified union to the separable closure using continuous Galois
   restriction and coefficient inclusion. Its invariant-stage colimit square is
   proved. Its bijectivity is not claimed.

Each new module M passed separately, with `LEAN_NUM_THREADS=2`, in the foreground:
`lake build FLT.LocalClassFieldTheory.M`,
`lake exe runLinter FLT.LocalClassFieldTheory.M`, and
`lake env lean Scratch/LiftsW23/MAxioms.lean`.
No whole-library lint was run. All named declarations, including instances and
proof abbreviations, use only `propext`, `Classical.choice`, `Quot.sound`, or no axioms.
Logs: `Scratch/LiftsW23/M-{build,lint,axioms}.log`.

`LEAN_NUM_THREADS=2 lake env lean Scratch/LiftsW23/Integration.lean` checks all
19 new modules imported together; evidence: `Scratch/LiftsW23/Integration.log`.
The final audit command is `LEAN_NUM_THREADS=2 lake env lean Scratch/LiftsW23/FinalAxioms.lean`;
evidence: `Scratch/LiftsW23/Final-axioms.log`. Both exited 0.

- `GaloisRepresentation.IsHardlyRamified.lifts` and `FLT.Assembly.hardlyRamifiedLifting`:
  `[propext, sorryAx, Classical.choice, Quot.sound]`.
- `PNat.pow_add_pow_ne_pow`:
  `[Mazur_statement, propext, sorryAx, Classical.choice, Quot.sound]`.
- The new continuous acyclicity, order-H2 isomorphism, multiplicative invariant,
  carry normalization and separable-closure inflation map use only standard axioms.

`python3 Scratch/LiftsW23/check.py` rechecks saved evidence: caps, audit coverage,
allowed axiom sets, fresh accepted logs, new-file-only Lean changes, sorted imports,
allowed paths, clean tracked state and the final FLT axiom set. It does not rerun Lean.
Fresh Lean validation can be repeated with `python3 Scratch/LiftsW23/validate.py M ...`.

### W23 remaining work

1. Prove the separable-closure inflation map bijective. The map now exists,
   but the continuous H2 inflation-restriction/Hilbert-90 bridge and ramified
   finite relative-order argument (Milne III.2; R01–R06) remain unproved.
   A cochain injection is not an injection on H2. Do not promote the constructed
   inflation morphism to an isomorphism by adding a hypothesis or record field.
2. Prove the arithmetic change-of-base-field restriction formula multiplying
   Q/Z coordinates by the extension degree, and the corestriction/fundamental-class
   comparisons. The subgroup restriction square proved here keeps the same
   coefficient order; it does not establish the change-of-base normalization formula.
3. Class formation and Kummer–Artin evaluation remain unproved. W14's cup-order
   minus sign is unchanged. Serre-weight evaluation and arbitrary-p Raynaud
   classification remain independently blocked; neither was dispatched.

API evidence: `Scratch/LiftsW23/remaining-api-check.log`; source boundaries:
R01–R06 and I02/I03 in `docs/LOCAL_CFT_FOUNDATIONS.md`. The new modules concern
ordinary continuous positive-degree cohomology, not arbitrary principal-unit
subgroup acyclicity or a full local reciprocity theorem.

## W22 historical acceptance — 2026-10-03T07:40:35.747894+00:00

Checked 2026-10-03T07:40:35.747894+00:00, branch `task/goal-lifts-w22`, base `c2adcddb`.
**E1c7/E1d remain blocked. Finite-stage arithmetic and the order-H2 comparison
are proved; the continuous unramified-union comparison remains open.**

23 new modules, 1,539 Lean lines, 80 named declarations. Each module passed
foreground `LEAN_NUM_THREADS=2 lake build MODULE`, individual
`lake exe runLinter MODULE`, and an axiom audit of every named declaration.
All new declarations use only propext, Classical.choice, Quot.sound, or no axioms.
Recheck saved evidence with `python3 Scratch/LiftsW22/check.py`; logs and the
machine-readable module table are in `Scratch/LiftsW22/`. No whole-library lint.

| Item | Module under FLT.LocalClassFieldTheory | Lines/cap | Commit |
|---|---|---|---|
| 1a — filtration and divided coefficients | PrincipalUnitFiltration | 79/200 | `f7321978` |
| 1b — graded quotient / residue equivalence | PrincipalUnitResidue | 99/200 | `f7321978` |
| 2a — determinant expansion of norm | NormFirstOrder | 55/200 | `d141432d` |
| 2b — norm preserves levels and residue trace | PrincipalUnitNorm | 79/200 | `d141432d` |
| 2c — base uniformizer upstairs | UnramifiedUniformizer | 50/200 | `d141432d` |
| 2d — one-step correction | PrincipalNormCorrection | 64/200 | `d141432d` |
| 2e — actual quotient norm / trace square | PrincipalNormGraded | 68/200 | `d141432d` |
| 3a — initial and improved approximations | UnitNormApproximation | 70/200 | `1f82a29a` |
| 3b — constructed compatible recursion | UnitNormSequence | 55/200 | `1f82a29a` |
| 3c — convergence and separatedness | PrincipalAdicLimit | 56/200 | `1f82a29a` |
| 3d — norm preserves all congruences | NormCongruence | 54/200 | `1f82a29a` |
| 3e — exact unit norm surjectivity | UnitNormSurjectivity | 71/200 | `1f82a29a` |
| 4a — integral unit Hilbert 90 | UnramifiedUnitHilbert90 | 66/200 | `30745e79` |
| 4b — action, invariants, norm comparison | IntegralUnitRepresentation | 78/200 | `30745e79` |
| 4c — both cyclic complexes exact | UnramifiedUnitCyclicExact | 80/200 | `30745e79` |
| 4d — all positive finite-stage cohomology | UnramifiedUnitAcyclic | 52/200 | `30745e79` |
| 5a — normalized integer order | DiscreteOrder | 59/200 | `6a169336` |
| 5b — order kernel and surjectivity | DiscreteOrderExact | 64/200 | `6a169336` |
| 5c — equivariant coefficient maps | UnramifiedOrderMap | 76/200 | `6a169336` |
| 5d — actual short exact order sequence | UnramifiedOrderSequence | 75/200 | `6a169336` |
| 5e — order-induced finite-stage H2 isomorphism | UnramifiedOrderCohomology | 62/200 | `6a169336` |
| 5f — canonical constructed-stage endpoints | UnramifiedStageOrderH2 | 57/200 | `6a169336` |
| 6 — order compatibility in towers | UnramifiedOrderTower | 70/200 | `bd3acf3d` |

The quotient Uⁿ/Uⁿ⁺¹ is identified with the additive residue field. The induced
norm is residue trace. Constructed successive corrections converge and prove
unit norm surjectivity. Integral unit Hilbert 90 and that surjectivity make both
cyclic complexes exact, proving positive cohomology vanishing for finite
unramified integral units. The actual order sequence then induces the H2
isomorphism. `unramifiedStageOrderH2Iso` instantiates it on the existing canonical
stages; all necessary integral-model instances are derived. Order also commutes
with unramified tower embeddings at the coefficient level.

Next: identify the unramified-union unit representation's invariant coefficients
with these finite-stage representations, prove the compatible cohomology maps,
and apply the existing continuous colimit comparison. Only then compose the
continuous order map with W21's integral Frobenius/Q/Z coordinates. Details and
API boundaries are in the W22 section of `LOCAL_CFT_FOUNDATIONS.md`.
Serre-weight evaluation and arbitrary-p Raynaud classification remain blocked.

Final audit: `LEAN_NUM_THREADS=2 lake env lean Scratch/LiftsW22/FinalAxioms.lean`,
exit 0; evidence `Scratch/LiftsW22/Final-axioms.log`:

- `GaloisRepresentation.IsHardlyRamified.lifts` and `FLT.Assembly.hardlyRamifiedLifting`:
  `[propext, sorryAx, Classical.choice, Quot.sound]`.
- `PNat.pow_add_pow_ne_pow`:
  `[Mazur_statement, propext, sorryAx, Classical.choice, Quot.sound]`.
- The new graded quotient, graded trace, unit norm, unit acyclicity, and
  canonical-stage multiplicative H2 comparison use only the three standard axioms.


## W21 acceptance — 2026-10-03T06:41:20.511369+00:00

Checked 2026-10-03T06:41:20.511369+00:00; branch `task/goal-lifts-w21`; base `3ee6889c`.
**E1c7/E1d remain blocked; the final FLT theorem retains sorryAx.**

17 new modules; 1,401 Lean lines; 76 named declarations.

| Item | Module under FLT.LocalClassFieldTheory | Lines/cap | Commit |
|---|---|---|---|
| 1a — trivial H1 | TrivialH1Characters | 93/200 | `88a00887` |
| 1b — integral H2 | IntegralH2Characters | 52/200 | `ebd8910f` |
| 2a — coefficient naturality | ConnectingCoefficientNaturality | 87/200 | `940e9d9e` |
| 2b — group restriction | ConnectingRestrictionNaturality | 93/200 | `003eabcb` |
| 3a — cochain cup | IntegralCochainCup | 93/200 | `3d38f8c3` |
| 3b — integral cup comparison | IntegralCupComparison | 95/200 | `258a8382` |
| 3c — connecting cup formula | ConnectingCupCompatibility | 108/200 | `28c07e12` |
| 4a — Frobenius generation | UnramifiedFrobeniusGenerator | 85/200 | `720ece2e` |
| 4b — character bijection | UnramifiedFrobeniusCharacters | 84/200 | `3f5a6419` |
| 4c — integral H2 coordinates | UnramifiedIntegralH2 | 65/200 | `48644bfc` |
| 5 — H2 restriction | TrivialRestrictionNaturality | 88/200 | `e8b2269e` |
| 6 — character additivity | IntegralCharacterAdditivity | 74/200 | `64fa02de` |
| 7 — additive H2 coordinates | UnramifiedIntegralH2Additive | 64/200 | `1b30242a` |
| 8 — positive carry normalization | UnramifiedCarryNormalization | 78/200 | `141f1b08` |
| 9 — integral coefficient maps | IntegralCoefficientRestriction | 84/200 | `28b54668` |
| 10 — integral cup boundary | IntegralConnectingCup | 88/200 | `81d94081` |
| 11 — finite-stage generation | UnramifiedCarryTorsion | 70/200 | `659c115a` |

Every new module M passed separately, in the foreground, with `LEAN_NUM_THREADS=2`:
`lake build M`, `lake exe runLinter M`, and
`lake env lean Scratch/LiftsW21/<Module>Axioms.lean`.
No concurrent or whole-library builds/lints were run; no OOM occurred.
Logs: `Scratch/LiftsW21/<Module>-{build,lint,axioms}.log`.
All 76 named declarations (including the scalar-character abbreviation and
three helper instances) use only `{propext, Classical.choice, Quot.sound}` or no axioms.

`python3 Scratch/LiftsW21/check.py` checks source caps, absence of admissions,
audit coverage and permitted axiom sets, log freshness, new-file-only Lean
changes, sorted unique FLT.lean imports, allowed paths, whitespace, clean tracked
state and the final FLT axiom set. It rejects untracked files under FLT/ and docs/.
It reads accepted evidence; it does not rerun Lean. Machine-readable evidence:
`Scratch/LiftsW21/summary.json`; check output: `Scratch/LiftsW21/check.log`.

Final audit command: `LEAN_NUM_THREADS=2 lake env lean Scratch/LiftsW21/FinalAxioms.lean`,
exit 0; evidence `Scratch/LiftsW21/Final-axioms.log`:

- `GaloisRepresentation.IsHardlyRamified.lifts` and `FLT.Assembly.hardlyRamifiedLifting`:
  `[propext, sorryAx, Classical.choice, Quot.sound]`.
- `PNat.pow_add_pow_ne_pow`: `[Mazur_statement, propext, sorryAx, Classical.choice, Quot.sound]`.
- The new additive H2 equivalence, constructed integral connecting-cup representatives,
  and finite-stage generation endpoint use only the three standard axioms.

1. **Characters:** trivial-action principal cocycles are zero. The actual H1
   quotient is continuous characters; composing its inverse with the proved
   positive Q/Z-to-Z boundary gives the integral H2 character equivalence.
2. **Naturality:** commuting coefficient maps construct short-complex morphisms.
   The homology-sequence theorem proves both coefficient and group-restriction
   connecting squares. The concrete integral H2 character equivalence commutes
   with continuous character pullback.
3. **Cups:** the degree-one and degree-two right cups by trivial scalar characters
   are actual continuous cochains. Their differential identity has positive sign.
   The old explicit cup descends to actual integral H1 and agrees with its integral
   H2 representative. Its vanishing is exactly a continuous coboundary witness.
   `integralScalarConnectingMap_cup_exists` constructs the continuous lift and
   both cycle representatives in the Z-linear complex; the scalar ring can be
   a different commutative ring. It proves the two categorical boundary formulas,
   not an assumed connecting/cup bridge. Scope is low-degree scalar-character
   cups, not a general higher-degree cup-product or arithmetic pairing API.
4. **Unramified quotient:** an open subgroup containing arithmetic Frobenius is
   the whole constructed unramified Galois group, by finite-stage cofinality and
   cyclicity. This proves character uniqueness. The denominator stage realizes
   every rational-circle value, giving the Frobenius evaluation bijection.
5. **Further leaves:** Frobenius coordinates give an additive isomorphism from
   integral H2 of the constructed quotient to Q/Z. The inflated degree-n carry
   has coordinate **+1/n**, and its j-multiple has coordinate j/n. Its exact
   annihilator is nZ. Every integral H2 class is an integer multiple of one such
   finite-stage carry, hence torsion.

The proved H2 has **constant integral coefficients**. This is the character/
Frobenius portion of Milne III.1.7, not the multiplicative local invariant.

- The order-induced isomorphism from multiplicative H2 still needs unramified
  unit/principal-unit acyclicity. Higher principal-unit graded quotients,
  norm-as-trace, successive corrections and convergence remain arithmetic work.
- Inflation to the full separable closure, class formation and Kummer–Artin
  evaluation remain unproved. W14's cup-order minus sign remains unchanged;
  the positive integral carry result does not erase it.
- Serre-weight evaluation and arbitrary-p Raynaud classification remain
  independently blocked; neither was dispatched or treated as available.

Next contracts require refinement against actual APIs (cap 200 per module):
construct the principal-unit quotient/residue-additive identification; prove the
norm's graded trace formula; then build compatible corrections and use
completeness before claiming norm surjectivity or unit acyclicity. Do not turn
any of these missing arithmetic conclusions into parameters or record fields.

## W20 acceptance — checked 2026-10-03T06:04:11.614329+00:00

Checked 2026-10-03T06:04:11.614329+00:00; branch `task/goal-lifts-w20`; starting base `d34fe0c6`.
**E1c7/E1d remain blocked; the final FLT theorem still has sorryAx.**

Fourteen new modules implement the four W19 follow-on contracts, split into
bounded leaves, and extend them through restriction naturality, the full
explicit H1 quotient comparison, and the positive Q/Z-to-Z connecting isomorphism.
All commits are local; nothing pushed.

| Item | Module under FLT.LocalClassFieldTheory | Lines/cap | Commit |
|---|---|---|---|
| C05f | ContinuousCoefficientMaps | 111/200 | `64ffd56a` |
| C05g | ContinuousColimitNaturality | 91/200 | `354d63a9` |
| C01i | IntegralLowDegreeComparison | 126/200 | `bfb8fa1f` |
| C01j | IntegralDegreeTwoComparison | 125/200 | `11d0889b` |
| C07a | ContinuousExactCoefficients | 105/200 | `c450c96a` |
| C07b | ContinuousConnectingMap | 111/200 | `e9adad08` |
| C07c | RationalCoefficientSequence | 109/200 | `46c399ea` |
| C07d | CyclicCarryConnecting | 92/200 | `7b11a7cc` |
| C06c | IntegralRationalVanishing | 84/200 | `ad53d35a` |
| C07e | RationalIntegralConnectingIso | 53/200 | `44f5fc93` |
| C05h | ContinuousRestriction | 97/200 | `7ba2cb29` |
| C05i | ContinuousRestrictionColimit | 78/200 | `c05b725a` |
| C01k | IntegralH1Equivalence | 98/200 | `a5eecf6a` |
| C05j | ContinuousRestrictionCohomology | 70/200 | `bc79f67a` |

Total: **1350 Lean lines; 91 named declarations**, including
nine coefficient/topology helper instances. Every module is below 200 lines.

## Validation

Each module M passed separately, in the foreground, with `LEAN_NUM_THREADS=2`:
`lake build M`, `lake exe runLinter M`, and
`lake env lean Scratch/LiftsW20/<Module>Axioms.lean`.
Accepted logs are in `Scratch/LiftsW20/<Module>-{build,lint,axioms}.log`.
Every named declaration, including the named local instances, has axioms
contained in `{propext, Classical.choice, Quot.sound}`; two use no axioms.
No whole-library build or lint was run. No concurrent builds or OOM occurred.

`python3 Scratch/LiftsW20/check.py` checks source caps, absence of admissions,
audit coverage and permitted axiom sets, log freshness, new-file-only Lean
changes, sorted unique FLT.lean imports, allowed paths, whitespace and clean
tracked state. It also rejects untracked files under FLT/ and docs/.
It reads validation evidence; it does not rerun Lean.
The machine-readable result is `Scratch/LiftsW20/summary.json`.

Fresh final audit: `LEAN_NUM_THREADS=2 lake env lean Scratch/LiftsW20/FinalAxioms.lean`,
exit 0, evidence `Scratch/LiftsW20/Final-axioms.log`:

* `IsHardlyRamified.lifts` and `FLT.Assembly.hardlyRamifiedLifting` retain
  `[propext, sorryAx, Classical.choice, Quot.sound]`.
* `PNat.pow_add_pow_ne_pow` retains
  `[Mazur_statement, propext, sorryAx, Classical.choice, Quot.sound]`.

## Proved scope

Coefficient maps restrict Mathlib's actual maps to continuous cochains;
identity, composition and stage-inflation compatibility are proved. The
complex and cohomology colimit comparisons are natural in these maps.

The low-degree coordinate formulas match the actual integral differential.
Every H1/H2 class has an explicit continuous cocycle representative; vanishing
is equivalent to a principal cocycle in degree one and a continuous one-cochain
boundary in degree two. `integralH1Equiv` identifies the existing splitting
quotient with the actual complex's H1 over any commutative ring, including Z.
The existing homogeneous TopRep comparison is field-based; this work uses the
explicit low-degree presentation rather than claiming that API covers Z.

Discrete coefficient sections prove degreewise surjectivity and exactness.
The continuous short exact sequence is constructed from coefficient exactness,
and its categorical connecting map is identified with the positive differential
of a continuous lift. The concrete sequence Z to Q to Q/Z discharges all
coefficient exactness premises. `rationalIntegralConnectingIso G n` is the
actual isomorphism from H^(n+1)(G,Q/Z) to H^(n+2)(G,Z). The scalar-change lemma
proves that rational vanishing applies to the integral complex as required.
`rationalIntegralConnectingMap_cyclicCarry` proves that the degree-one character
i/n maps to the positive integral carry class, fixing the sign.

Restriction pulls an open normal subgroup N back to f^(-1)(N), proves the
invariant-coefficient quotient map there, and proves compatibility with
inflation. The index functor and stage natural transformation are constructed;
both complex and cohomology colimit naturality follow. No pullback-stage,
colimit, boundary or quotient-action bridge is supplied as a hypothesis.

## Remaining work and next bounded contracts

E1c7/E1d remain blocked. Local invariant/class formation, Kummer-Artin evaluation,
higher principal-unit graded quotients, norm-as-trace, successive corrections
and convergence are not supplied by these cohomology constructions.
The Serre-weight and arbitrary-p Raynaud gates remain independently blocked.
No task for either missing API was dispatched.

Next leaves, each with a 200-line cap and a separate build/lint/audit:

1. Identify trivial-action H1 with continuous characters, using `integralH1Equiv`
   and proving that every principal cocycle is zero. Compose with the proved
   connecting isomorphism to express integral H2 by Q/Z characters.
2. Prove connecting-map naturality under coefficient-sequence morphisms and
   continuous group restriction, using the constructed short complexes and
   Mathlib's homology-sequence naturality. Prove the commutative squares.
3. Compare the explicit low-degree cup with a continuous integral cochain cup;
   prove its compatibility with the connecting map before using a local invariant.
4. Apply the character description to the constructed unramified procyclic
   quotient and prove Frobenius evaluation/bijection from that quotient's tower.
   The multiplicative order-H2 isomorphism still needs principal-unit acyclicity.


## W19 acceptance — checked 2026-10-03 05:17 UTC

Thirteen new modules prove common-stage boundaries, the continuous
inhomogeneous complex and its filtered colimit, the cohomology colimit,
finite discrete comparison, and positive characteristic-zero vanishing.
All commits are local; nothing pushed. Base: `fc41abcf`.

| Item | Module under FLT.LocalClassFieldTheory | Lines/cap | Commit |
|---|---|---|---|
| C04f | FixedCoefficientBoundary | 59/200 | `f6a77d5a` |
| C04g | InvariantStageTransition | 81/200 | `68e7594a` |
| C05a | ContinuousCochainComplex | 89/200 | `a33bc6c8` |
| C05b | ContinuousStageDiagram | 94/200 | `f0598852` |
| C05c | ContinuousCochainColimit | 60/200 | `cbaaabb3` |
| C05d1 | CochainHomologyClass | 88/200 | `f6c450c1` |
| C05d2 | FilteredComplexDescent | 66/200 | `7e8616d7` |
| C05d3 | FilteredHomologyDescent | 66/200 | `0fd42145` |
| C04h | ContinuousStageBoundary | 60/200 | `ec91e35a` |
| C05e | ContinuousCohomologyColimit | 65/200 | `35c934ba` |
| C02a | FiniteContinuousComparison | 60/200 | `3aea178c` |
| C06a | FiniteCharacteristicZeroCohomology | 46/200 | `b22c73fe` |
| C06b | ContinuousCharacteristicZeroCohomology | 57/200 | `9bf2fe8e` |

Total: **891 Lean lines; 49 named declarations, including one helper
instance**. Every new module is below its 200-line cap.

Validation: each module M passed separately, in the foreground:
`LEAN_NUM_THREADS=2 lake build M`, `LEAN_NUM_THREADS=2 lake exe runLinter M`,
and `LEAN_NUM_THREADS=2 lake env lean Scratch/LiftsW19/<Module>Axioms.lean`.
All accepted logs are clean; every new declaration has axioms contained in
`{propext, Classical.choice, Quot.sound}`. Evidence is recorded in
`Scratch/LiftsW19/<Module>-{build,lint,axioms}.log`.
`python3 Scratch/LiftsW19/check.py` verifies caps, audit coverage, log freshness,
allowed paths, sorted imports and clean tracked state; it reads evidence,
not rerunning Lean. `validate.py` also commits a validated module.

The complex uses the submodule of continuous functions and Mathlib's actual
inhomogeneous differential. The stage maps are quotient pullbacks with inclusion
of invariant coefficients. Reverse inclusion of open normal subgroups is filtered;
finite descent and injective inflation prove the complex colimit universal property.
The boundary theorem works for an independently supplied stage: descend the bounding
cochain and refine both stages, then prove the finite differential equation.

The cohomology colimit is proved in every degree, including zero. Generic filtered
union lemmas take component injectivity and joint surjectivity; their application
here discharges both from the constructed inflation and finite descent. No common
stage, boundary detection, quotient action, differential or colimit bridge is assumed.
The finite discrete comparison is identity on cochains and works over any commutative
ring, including Z. Characteristic-zero vanishing applies to arbitrary discrete modules
with continuous action over a characteristic-zero field, including rational modules.
It uses proved Maschke/projectivity and the Ext presentation, not an assumed homotopy.

**E1c7/E1d remain BLOCKED.** Fresh final axiom audit:
`LEAN_NUM_THREADS=2 lake env lean Scratch/LiftsW19/FinalAxioms.lean`, evidence
`Scratch/LiftsW19/Final-axioms.log`.
`IsHardlyRamified.lifts` and `FLT.Assembly.hardlyRamifiedLifting` retain
`[propext, sorryAx, Classical.choice, Quot.sound]`;
`PNat.pow_add_pow_ne_pow` retains
`[Mazur_statement, propext, sorryAx, Classical.choice, Quot.sound]`.

Remaining work: compare with the explicit integral low-degree/homogeneous
presentation; prove restriction/coefficient naturality and connecting-map/cup
compatibility; construct the continuous exact-sequence boundary for Q/Z and Z.
The norm route still needs higher principal-unit graded quotients, norm-as-trace,
successive corrections and convergence. Local invariant/class formation and
Kummer–Artin evaluation remain. General analytic completeness transport beyond
the rational specialization remains where callers need it. Serre-weight evaluation
and arbitrary-p Raynaud classification remain independent blocked gates.

## W18 acceptance — checked 2026-10-03 04:46 UTC

Thirteen new modules add degree-indexed profinite reindexing, compatible
arithmetic Frobenius, canonical integral models, the existing valuation-inertia
kernel comparison, normalized continuous unramified characters, and two
finite-cochain follow-ons. All commits are local; nothing pushed.

| Item | Module under FLT.LocalClassFieldTheory | Lines/cap | Commit |
|---|---|---|---|
| U04d1 | UnramifiedDiagram | 96/200 | `02e1fc80` |
| U04d2 | UnramifiedDegreeLimit | 73/200 | `6af82866` |
| U04e1 | UnramifiedIntegralModel | 70/200 | `def84e8a` |
| U04d3 | UnramifiedStageFrobenius | 119/200 | `b67a3d24` |
| U04e2 | UnramifiedLocalInertia | 66/200 | `53f79781` |
| U04e3 | UnramifiedInertiaConverse | 76/200 | `ac1bdb3d` |
| U04e4 | UnramifiedInertiaKernel | 83/200 | `cd6b68dd` |
| U05a | UnramifiedCyclicStages | 86/200 | `9a3a6a94` |
| U05b | UnramifiedCharacterDescent | 66/200 | `c17388d8` |
| U05c | UnramifiedCharacters | 71/200 | `a81313b6` |
| U05d | RationalUnramifiedCharacters | 66/200 | `47e15235` |
| C04d | FixedCoefficientCochain | 50/200 | `49001fb8` |
| C04e | FixedCoefficientDifferential | 95/200 | `41b9366c` |

Total: **1017 Lean lines; 50 named definitions/theorems** plus ten
audited helper instances. Every module is below its 200-line cap.

Validation for each new module M, separately in the foreground:
`LEAN_NUM_THREADS=2 lake build M`, `LEAN_NUM_THREADS=2 lake exe runLinter M`,
and `LEAN_NUM_THREADS=2 lake env lean Scratch/LiftsW18/<Module>Axioms.lean`.
All accepted logs are clean. New declarations and helper instances use only
`propext`, `Classical.choice`, and `Quot.sound`. Evidence:
`Scratch/LiftsW18/<Module>-{build,lint,axioms}.log` and `Instances-axioms.log`.
`python3 Scratch/LiftsW18/check.py` checks these logs, source caps, audit
coverage, import sorting, allowed changed paths and clean tracked state;
it does not rerun Lean. `validate.py` also commits a validated module.

The generic unramified tower still starts from W17's complete DVR with finite
residue field. In number-field completions, the canonical integral closure is
proved to agree with the constructed unramified model; both directions of
finite inertia comparison are proved, and closedness identifies the full
restriction kernel. No residue or inertia bridge is assumed. At rational
p-adic places the existing completeness transport discharges the base
completeness hypothesis, so the character and descent theorems require only
primality of p. The characters exist for every positive degree, including
prime degree, and send every arithmetic Frobenius lift to one in Z/n.

The cochain follow-ons use Mathlib's existing quotient representation on
invariants and its actual inhomogeneous cochain map. Inflation is injective,
commutes with the differential, and reflects cocycles. Thus every continuous
inhomogeneous cocycle descends to a cocycle on a finite quotient with invariant
coefficients. Common-stage boundaries and the cohomology colimit are not
proved by this result.

**E1c7/E1d remain BLOCKED.** Fresh final audit:
`LEAN_NUM_THREADS=2 lake env lean Scratch/LiftsW18/FinalAxioms.lean`, evidence
`Final-axioms.log`. `IsHardlyRamified.lifts` and
`FLT.Assembly.hardlyRamifiedLifting` retain
`[propext, sorryAx, Classical.choice, Quot.sound]`;
`PNat.pow_add_pow_ne_pow` retains
`[Mazur_statement, propext, sorryAx, Classical.choice, Quot.sound]`.
Higher principal-unit norm lifting/completeness, the continuous-cohomology
comparison, local invariant/class formation and Kummer–Artin evaluation remain.
Serre-weight evaluation and arbitrary-p Raynaud classification remain separate
blocked gates. No whole-library build/lint or background build ran.

## W17 acceptance — checked 2026-10-03 04:02 UTC

Thirteen new modules complete the algebraic U03b realization chain and the
ready U04 union/profinite leaves. Refinements preceded the corresponding
proofs (`f120d39d`, `6971e08e`, `0e509e1c`, `9b7cc145`).

| Item | Module under FLT.LocalClassFieldTheory | Lines/cap | Commit |
|---|---|---|---|
| U03b1a | UnramifiedDegree | 104/200 | `f8b84872` |
| U03b1b | UnramifiedExistence | 55/200 | `9dcbc0d9` |
| U03b2a | HenselianRoots | 80/200 | `de7becef` |
| U03b2b | UnramifiedPolynomial | 84/200 | `baf81b55` |
| U03b3a | UnramifiedNormal | 81/200 | `e76df0e0` |
| U03b3b | UnramifiedGaloisExistence | 85/200 | `f2109305` |
| U03b4a | UnramifiedEmbeddings | 82/200 | `303e12db` |
| U03b4b | UnramifiedStages | 81/200 | `badb7c8f` |
| U03b4c | UnramifiedUniqueness | 73/200 | `2c3e5957` |
| U03b4d | UnramifiedStageTower | 93/200 | `a51a4c51` |
| U04a | UnramifiedUnion | 63/200 | `c08d4541` |
| U04b | UnramifiedCofinality | 44/200 | `f5374e47` |
| U04c | UnramifiedGaloisLimit | 74/200 | `7c231c49` |

Total: 999 Lean lines, 42 named declarations (37 theorems and 5 definitions).
Every module is below 200 lines. Each passed foreground
`LEAN_NUM_THREADS=2 lake build M`, individual
`LEAN_NUM_THREADS=2 lake exe runLinter M`, and `#print axioms` for every
named declaration. New axiom sets are subsets of
`{propext, Classical.choice, Quot.sound}`. Evidence:
`Scratch/LiftsW17/<Module>-{build,lint,axioms}.log` and `<Module>Axioms.lean`.
`python3 Scratch/LiftsW17/check.py` checks those recorded logs, caps,
declaration coverage, admission-free sources, sorted imports, allowed changed
paths and clean tracked state. It does not rerun Lean.

Constructed results: complete unramified integral DVR realizations, unique
simple-root lifting, splitting, normality, Galois stages of every positive
degree inside the chosen separable closure, uniqueness, divisibility
containment, lcm composita, the directed Galois union, finite-stage cofinality,
a topological inverse-limit equivalence and continuous surjective restriction.
Normality and stage uniqueness are proved, not assumed by a record field.
The inverse limit uses all finite Galois intermediate fields of the union;
explicit reindexing by positive degrees is still unassembled.

**E1c7/E1d remain BLOCKED.** The valued-local-field frontend and identification
of the restriction kernel with existing valuation inertia remain, followed
by U05 and the other local class-field/cohomological gates. The exact remaining
contracts and reused existing APIs are at the end of LOCAL_CFT_FOUNDATIONS.md.

Fresh final check: `LEAN_NUM_THREADS=2 lake env lean
Scratch/LiftsW17/FinalAxioms.lean`, exit 0 (`Final-axioms.log`).
`IsHardlyRamified.lifts` and `FLT.Assembly.hardlyRamifiedLifting` retain
`[propext, sorryAx, Classical.choice, Quot.sound]`;
`PNat.pow_add_pow_ne_pow` retains
`[Mazur_statement, propext, sorryAx, Classical.choice, Quot.sound]`.
No whole-library build/lint, background build, push, or fleet request ran.

## W16 acceptance — checked 2026-10-03 03:19 UTC

The residue comparison audit and its refinements were committed before their
proofs (`41beb0d6`, `9b2d70fc`, `e7085e14`). Eleven new modules are proved:

| Item | Module under FLT.LocalClassFieldTheory | Lines/cap | Commit |
|---|---|---|---|
| U01a | ResidueAction | 63/200 | `c0854240` |
| U01b | ResidueActionSurjective | 39/200 | `716f387d` |
| U01c | ResidueActionFaithful | 45/200 | `a35029e7` |
| U01d | ResidueGaloisEquiv | 76/200 | `8e8820ad` |
| U02a | Frobenius | 90/200 | `b123c2a3` |
| U03a | FrobeniusTower | 67/200 | `a5404d88` |
| N02a | ResidueNorm | 62/200 | `7cf056fb` |
| N03a | ResidueNormLift | 51/200 | `dc6fec36` |
| C04a | CochainFiniteImage | 55/200 | `ebc81063` |
| C04b | CochainOpenNormal | 62/200 | `ad2cb560` |
| C04c | DescendedCochain | 59/200 | `f1089488` |

Total: 669 Lean lines; 32 named declarations, including 27 theorems.
Each module passed its foreground `LEAN_NUM_THREADS=2 lake build M`, its
individual `LEAN_NUM_THREADS=2 lake exe runLinter M`, and a `#print axioms`
audit of every named declaration. All new axiom sets are subsets of
`{propext, Classical.choice, Quot.sound}`. No whole-library build or lint ran.
Evidence: `Scratch/LiftsW16/<Module>-{build,lint,axioms}.log` and
`<Module>Axioms.lean`; `python3 Scratch/LiftsW16/check.py` checks the recorded
logs, declarations, caps, admission-free sources, sorted root imports,
changed-path scope and clean tracked state. These log checks are separate
from the Lean commands that rerun the proofs.

The integral U01 comparison is complete for a finite Galois fraction-field
extension whose integral closure is a DVR and formally unramified. Reduction,
its ideal-inertia kernel, surjectivity, injectivity and the equivalence are
constructed. Galois invariance, finite/free integral structure and the power
basis are derived; no residue equivalence or inertia-triviality premise is
supplied. Arithmetic Frobenius is then constructed, with its residue q-power
rule, uniqueness, order, generation and tower restriction.

The norm leaves prove norm/trace reduction and a first unit-norm
approximation modulo the maximal ideal. They do not prove full unit-norm
surjectivity. The cochain leaves prove actual finite quotient descent on
arbitrary finite powers of a profinite group, including one constructed
open normal kernel fixing all coefficient values. They do not yet identify
cocycles or boundaries with the finite-stage cohomology complexes.

**E1c7/E1d remain BLOCKED.** The general valued-local-field frontend, existence
and uniqueness of Galois unramified stages in the chosen separable closure,
U04/U05, higher principal-unit norm lifting/completeness, continuous-complex
descent, local invariant, class formation and Kummer–Artin evaluation remain.
Use the finer remaining contracts in LOCAL_CFT_FOUNDATIONS.md; do not
redispatch the already proved integral U01 or residue-unit quotient.

Fresh final audit: `LEAN_NUM_THREADS=2 lake env lean
Scratch/LiftsW16/FinalAxioms.lean`, exit 0 (`Final-axioms.log`).
`IsHardlyRamified.lifts` and `FLT.Assembly.hardlyRamifiedLifting` still use
`[propext, sorryAx, Classical.choice, Quot.sound]`; `PNat.pow_add_pow_ne_pow`
still uses `[Mazur_statement, propext, sorryAx, Classical.choice, Quot.sound]`.
The support leaves do not remove the lifting admission. No Serre-weight or
arbitrary-p Raynaud classification was dispatched. All commits are local.

## W15 acceptance — checked 2026-10-03

The local Artin/invariant source match and dependency program are in
[LOCAL_CFT_FOUNDATIONS.md](LOCAL_CFT_FOUNDATIONS.md). The initial split was
committed as `bae964f8`, the normalized-order refinement as `82c3726c`, and
the large blocked prerequisite expansions as `9496cc75`. Missing arithmetic
theory is explicitly blocked; a proposed 200-line cap is not evidence that
a foundational theorem already exists or fits an adapter.

Five ready leaves were proved, each within 200 lines:

| Item | Module under FLT | Lines/cap | Commit |
|---|---|---|---|
| S01 | LocalClassFieldTheory.RationalTorsion | 77/200 | `ffe9f225` |
| S02 | LocalClassFieldTheory.CyclicCarry | 75/200 | `c5a30d42` |
| S03 | GaloisRepresentation.Extensions.ContinuousCupSwap | 93/200 | `db5931a6` |
| V01 | LocalClassFieldTheory.NormalizedOrder | 98/200 | `f9a5c5c6` |
| V02 | LocalClassFieldTheory.PowerClassOrder | 103/200 | `f5eaca0f` |

S01 constructs the positive map `ZMod n → ℚ/ℤ`, proves injectivity and
image exactly n-torsion. S02 proves the positive cyclic carry/coboundary
formula and the cocycle equation. S03 constructs the opposite continuous
cup and proves `d(diagonal cochain) = -(cup + opposite cup)`, together with
equivalence of their coboundary zero tests. With arithmetic Frobenius and
Milne's positive invariant, W14's Kummer-first order therefore needs the
negative of the character-first evaluation; this arithmetic evaluation is
still a future theorem, not supplied by S03.

V01 constructs the classical normalized order on an actual nonarchimedean
local field, proves surjectivity and identifies its kernel with actual
valuation-ring units. V02 descends order modulo n to the existing Kummer
power quotient and proves its kernel is exactly the independent unit-class
subgroup (for all n, including zero). No Artin map, invariant or annihilator
conclusion is an input to these theorems.

All five foreground builds and individual-module lints passed. All 40 named
declarations (32 theorems) were axiom-audited: only propext, Classical.choice,
Quot.sound. Logs: `Scratch/LiftsW15/<Module>-{build,lint,axioms}.log`.
Rerun each separately with `LEAN_NUM_THREADS=2 lake build M`,
`LEAN_NUM_THREADS=2 lake exe runLinter M`, and
`LEAN_NUM_THREADS=2 lake env lean Scratch/LiftsW15/<Module>Axioms.lean`.
The combined fresh audit is `Scratch/LiftsW15/FinalAxioms.lean` with output
`Final-axioms.log`; `check.py` checks log coverage, standard axiom sets,
line caps, sorted imports, allowed paths and clean tracked state.

**E1c7, E1d1 and E1d2 remain BLOCKED.** The source specifies arithmetic
Frobenius, positive fundamental-class invariant, units mapping to the
abelian image of inertia, and the required cup-order sign. The checkout
has finite cyclic cohomology, Hilbert 90 and the Tate complex, but lacks the
local reciprocity/class-formation theorem, unramified/invariant comparison
and actual H² Kummer–Artin evaluation. BrauerGroup is only a quotient
definition, not a local invariant API; the selected cohomological route
avoids that separate CSA program. E1d1 still needs the actual unramified
character and the local evaluation/injectivity gate. E1d2 additionally
needs the scalar comparison of pairing and unramified dual characters.

The final FLT axiom audit remains
`[Mazur_statement, propext, sorryAx, Classical.choice, Quot.sound]`.
This wave does not remove `IsHardlyRamified.lifts` or its sorryAx dependency.
No Serre-weight evaluation or arbitrary-p Raynaud leaf was dispatched.

## W14 acceptance — checked 2026-10-03 02:19 UTC

E1c's formal continuous-cohomology comparison is proved. E1c's arithmetic
Tate/Artin comparison and E1d remain **BLOCKED**, not ready. Eight new modules
(750 lines, each ≤200) passed foreground builds and individual-module linting.
All 52 named declarations, including 27 theorems, were axiom-audited separately
and together: only propext, Classical.choice and Quot.sound.

| Item | Module under FLT.GaloisRepresentation | Lines/cap | Commit |
|---|---|---|---|
| E1c1 | Extensions.HomogeneousOne | 103/200 | `fbccf3eb` |
| E1c2 | Extensions.HomogeneousTwo | 114/200 | `2ab22ca1` |
| E1c3 | Extensions.ContinuousH1Comparison | 124/200 | `1c9208f6` |
| E1c3a | Extensions.ContinuousH1Equiv | 103/200 | `cab6e6d0` |
| E1c4 | Extensions.ContinuousH2Comparison | 69/200 | `0c2d241f` |
| E1c5 | Extensions.HomogeneousCup | 106/200 | `169036fd` |
| E1c5a | Extensions.ContinuousCupComparison | 80/200 | `b5497797` |
| E1c6 | Extensions.PeuCohomologyComparison | 51/200 | `3f078335` |

`continuousH1LinearEquiv` identifies the linear continuous quotient with actual
continuous H¹; `continuousH1Equiv` identifies the original splitting quotient,
with its representative formula proved. The H² comparison represents every
class by an explicit jointly continuous cocycle and proves zero iff there is
an actual continuous coboundary witness. `continuousCohomologyCup_class`
identifies the explicit cup with the existing `ContinuousCohomology.cup`.
`isPeuRamifiedClass_cohomology_iff` transports the independent E1b predicate
to the annihilator under this actual cup of inertia-trivial additive characters.
This is not yet a comparison with an arithmetic local Tate pairing.

The coefficient action and scalar action are explicitly jointly continuous;
coefficients are discrete. Local compactness of G is used for the degree-two
inverse/vanishing comparison. These hypotheses hold in the intended
profinite/discrete setting; no continuity witness is replaced by a set map.
The H¹ equivalence is linear, not claimed to be a topological isomorphism.

The source-matched split was committed as `36163adb`; the bounded H¹ quotient
and cup quotient refinements as `98837482` and `3efe37c5`, before those proofs.
The API audit below finds no constructed local Artin reciprocity map, local
H² invariant, or Tate local-duality/evaluation theorem in this checkout.
No arithmetic conclusion was installed as a record field.

Validation: for each new module M, run
`LEAN_NUM_THREADS=2 lake build M`, then
`LEAN_NUM_THREADS=2 lake exe runLinter M`, then
`LEAN_NUM_THREADS=2 lake env lean Scratch/LiftsW14/<ShortName>Axioms.lean`.
All final per-module logs are warning/error-free, under
`Scratch/LiftsW14/<ShortName>-{build,lint,axioms}.log`.
The fresh combined audit was
`LEAN_NUM_THREADS=2 lake env lean Scratch/LiftsW14/FinalAxioms.lean` (exit 0).
It imports the eight new modules and the existing compiled final theorem;
it does not rebuild or lint the whole library. `Final-axioms.log` still gives
sorryAx for lifts and its adapter, and
`[Mazur_statement, propext, sorryAx, Classical.choice, Quot.sound]` for
`PNat.pow_add_pow_ne_pow`. W14 has not removed the lifting admission.
`python3 Scratch/LiftsW14/check.py` verifies recorded logs, all named audits,
line caps, source scope, sorted unique imports and clean tracked state;
use the Lean commands above for fresh execution.

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
Other search hits do not fill the gate: `CyclicBaseChange/Statements.lean`
explicitly supplies Frobenius data and defers its Artin construction;
`GlobalLanglandsConjectures/GLzero.lean` mentions CFT in background prose.
`FreyCurve/Serre/AtP.lean:123` constructs an inertia-fixed torsion functional,
not an H² local invariant. The full read-only search and declaration inventory
are in `Scratch/LiftsW14/api-audit.log` and `api-files.txt`.
Foundational arithmetic programs need their own source-matched splits;
the 200-line adapter caps are not bounds on those missing programs.
No Serre-weight evaluation or arbitrary-p Raynaud leaf is dispatched.

E1d's two directions require arithmetic facts, not just a quotient isomorphism:
unramified characters kill units under local Artin, and a valuation character
modulo p detects every non-unit class in Kˣ/(Kˣ)^p. A class whose valuation is
divisible by p becomes a unit after dividing by a p-th power of a uniformizer.
The actual local invariant must detect zero in H²(K,μ_p), and its Kummer–cup
formula must be checked with the selected Artin/Frobenius normalization.
For extended residual coefficients, one must also transport the pairing and
unramified dual characters under scalar extension; E09c's vector-space
comparison alone does not assert compatibility with the arithmetic pairing.
These are named obligations, not assumptions added to a new Lean record.

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
