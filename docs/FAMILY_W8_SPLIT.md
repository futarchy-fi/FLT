# FAMILY-W8 — finite-flat inertia spectrum and the family boundary

## W19 implemented boundary — 2026-10-03

D10's original-factor transport, maximal scalar lifts, exact original-inertia
comparison and binary local weights are implemented. D11 computes the actual
one-/two-dimensional simple-factor prime-field charpolys, including the
Frobenius-fixed quadratic case. **D12–D14 remain open; this is partial
completion of GOAL-FAMILY-W19.** The original family admission is unchanged.

Checked at 2026-10-03 09:18:42 UTC by `python3 W19_FINAL_CHECKS.py`:
16 individual foreground builds and module-specific lints, 48 named declarations
in `W19_AXIOMS.lean` (only `propext`, `Classical.choice`, `Quot.sound`), and
`W19_BOUNDARY_AXIOMS.lean` (the family still uses `sorryAx`). The 16 whole files
range from 44 to 110 lines, below the 150-line cap. The manifest and per-module
commands are in `W19_MODULES.txt` and `W19_VALIDATE.sh`; audit artifacts and
`FAMILY_W19_DONE.md` remain untracked outside `FLT/`, as required by the brief.

Proved assembly endpoints:

- `IsFiniteFlat.closureChange` and `baseChange_prescribedClosure` retain the
  actual Hopf witness and original point/scalar types using postcomposition
  and `AlgEquiv.autCongr`.
- `inertiaDescentStage` places the actual descent integers in the original
  union; `inertiaDescentFieldToTower_comp` proves the fraction lift recovers
  the original field inclusion.
- `exists_original_factor_tower_action` proves agreement with the same
  original inertia element. `exists_simple_factor_character_model` derives
  the scalar field, maximal lifts and character on both original and model points.
- `exists_original_one_weight` and `exists_original_two_weight` construct
  the scalar models and residue embedding before deriving common binary
  exponents `d` and `p*a+b` for all original inertia elements.
- `original_one_factor_charpoly` and `original_two_factor_charpoly` return
  the original factor charpolys from these weights. Computed characters,
  integral scalar models and charpoly factorizations are not inputs.

The endpoints use the explicit union's fraction-field algebra and prescribed
embedding, supplied by the existing tower construction, plus an original simple
subquotient and chosen root. D12 must instantiate this infrastructure from the
original representation, choose a niveau-two generator before its cyclotomic
norm, combine factor charpolys and apply the determinant. D13 still requires
higher niveaux for larger coefficient fields; D14 and the broader family
statement-scope obligations remain separate. No full spectrum or admission-free
family theorem is claimed.


## W18 implementation boundary — 2026-10-03

D9c's closure placement, original-inertia fixedness, evaluation transport,
and application to actual one-/two-cycle point equations are implemented.
The new local scalar-weight endpoints also identify these ratios through
one compatible residue-field embedding. **D10's original-factor assembly
and D11–D14 are still open; this is not completion of GOAL-FAMILY-W18.**
`Family.lean` is unchanged and its original admission remains.

Checked at 2026-10-03 08:05 UTC by `python3 W18_FINAL_CHECKS.py`,
12 individual foreground builds/lints, `W18_AXIOMS.lean` (31 declarations,
only `propext`, `Classical.choice`, `Quot.sound`), and
`W18_BOUNDARY_AXIOMS.lean` (the family still uses `sorryAx`).

The twelve new modules are listed in `FAMILY_W18_DONE.md`; each whole file
is at most 83 lines (cap 150). Reproduce validation with the per-module
commands and `python3 W18_FINAL_CHECKS.py` recorded there. These audit
artifacts are untracked outside FLT, as required by the brief.

Concrete local endpoints:

- `inertia_fixes_unramifiedStage`, `inertia_fixes_unramifiedUnion`, and
  `inertia_fixes_fractionField` prove fixedness in the original embedding.
  Residue uniqueness uses a power-basis generator and its unit derivative;
  fixedness of the union follows by a subalgebra supremum argument.
- `towerClosureEquiv` extends the prescribed fraction embedding.
  `originalTowerInertia_evaluation` intertwines the actual coordinate
  evaluations and original inertia without a fixedness hypothesis.
- `fundamentalValue_one_original_character` and
  `fundamentalValue_two_original_character` derive integral original-inertia
  ratios from actual point equations, with common digits for all inertia.
- `one_cycle_scalar_weight` and `two_cycle_scalar_weight` identify an actual
  scalar action under `towerResidueMap`, with binary exponent `d` or `p*a+b`.
  They still take the strict-Henselian scalar model, integral scalar lifts,
  rank-one proof, and point-action comparison. They do not construct the
  original representation's factors or assume a tame-character formula.

### Next original-factor transport leaves (each cap 150)

1. Change the algebraic closure in `GaloisModule.IsFiniteFlat` using
   `AlgEquiv.autCongr` and postcomposition of Hopf-algebra points; retain the
   prescribed point type and its scalar action. The canonical absolute-Galois
   restriction map alone does not identify the prescribed closure embedding.
2. Embed the actual finite descent integers as a stage of the original
   unramified union. Use `inertiaDescentIntegers_irreducible`, finiteness and
   separable residue to prove its image is an `UnramifiedStage`.
3. Apply `IsFiniteFlat.baseChange_sameClosure` to the actual descended factor,
   then the closure-change comparison. Keep the equality with the SAME
   original inertia element; an existential matching inertia element from
   `exists_inertia_action_map` is insufficient for a character formula.
4. Construct the maximal scalar model with `exists_maximal_model_scalar_action`,
   transport the derived rank-one finite scalar field and its point action,
   and apply the proved local weights. No scalar-action comparison or
   computed factor character may become a field in the model input.

Only then assemble D11's prime-field factor charpolys and D12's spectrum.
`LocalRoot.rootCharacterToRoots_surjective` supplies the root-character
surjectivity ingredient; choose a niveau-two generator before taking its
cyclotomic norm. D13 still needs a higher-niveau coefficient-field argument:
restriction to the prime field multiplies dimension by the coefficient degree.
D14 and the exact family target retain their existing separate obligations.


## W17 current gate map — 2026-10-03

This section supersedes historical status below. Checked at base `25a54828`
by reading the cited modules and `Family.lean:37–68`, and searching
`rg -n 'sorry' FLT/MoretBailly.lean`. C5 is complete; the family admission
remains. The blueprint (chapter 3, lines 183–215) assumes irreducible reduction;
the Lean target does not. It also covers arbitrary finite free local domains,
every odd prime including 3, and every embedding of the common number field.

### Completed gates

| Gate | Modules (under FLT; abbreviated basenames) | Limit |
|---|---|---|
| S1–S4 | `RaynaudParameterValuation`, `RaynaudTwoCoordinates`, `TameSpectrumDigits`, `RaynaudCoordinateCharacter` | S4 is over number-field completion integers, not the infinite strict henselization. |
| Simple inertia | `RaynaudInertiaSimpleScalars`, `RaynaudAbsoluteTameCommutativity`, `WildInertiaProP` | Derived finite rank-one scalars; no computed inertia characters. |
| S5b | `RaynaudInertiaFactorDescent`, `RaynaudCompatibleSubquotients`, `RaynaudInertiaScalarFiltration`, `RaynaudDescentActionAgreement`, `RaynaudDescentScalarFiltration` | Actual finite-flat factors and descent/action agreement; spectrum transport remains. |
| C3 | `RaynaudStrictHenselian`, `RaynaudStageFamily`, `RaynaudResidueClosure` | Actual unramified strict-Henselian tower. |
| S5c | `RaynaudActualCyclicPresentation`, `RaynaudFundamentalCycleParameters`, `RaynaudCoefficientBounds`, `RaynaudExtremalActions` | Genuine coordinates, parameter products and generation; evaluation on points remains. |
| C5 | `RaynaudPadicPowerExtension` | `ThreeAdicPlan.extend_from_padic_power` and `GenericGaloisHom.integral_of_padic_power`: prescribed maps on original odd-prime p-adic models. |
| Twist obstruction | `TameTraceObstruction`, `CyclotomicInertiaDetection`, `CyclicRestrictionTwist` | Requires actual spectrum and the appropriate generator. |
| Family algebra | `FamilyTracePair`, `BrauerEffectivityCoefficients`, `Assembly/FreyTraceInput` | Conditional algebra/consumer reductions, not existence of a family. |

### S5d and tame-spectrum leaves

Each proposed new module has a **whole-file cap of 150 lines**. Split again
before exceeding it. Sketches suppress ambient instances. Names in later
sketches describe interfaces to construct, not existing APIs. READY means
the displayed inputs exist; it does not mean the classification is proved.

| Leaf / proposed module | Lean endpoint sketch | Dependencies / status |
|---|---|---|
| D1 `InvariantCharpoly` | `T.charpoly = (T.restrict hU).charpoly * (U.mapQ U T hU).charpoly` | READY: `Basis.sumQuot`, block triangular charpoly; no invariant complement. |
| D2 `RankTwoCharpoly` | `T.charpoly=(X-C a)*(X-C b) ↔ trace k V T=a+b ∧ T.det=a*b` | READY: finrank two, charpoly coefficients. |
| D3 `FiniteFieldQuadraticSpectrum` | monic quadratic `P : (ZMod p)[X]`, root a in char p implies root `a^p`; if distinct, `P.map f=(X-C a)*(X-C (a^p))` | READY: Frobenius fixes prime coefficients; root divisibility and degree. |
| D4 `TameSpectrumCharpoly` | binary-digit charpoly factors + cyclotomic determinant imply `trace k V T ≠ 0` and ratio order p−1 or p+1 | READY after D2, `TameSpectrumDigits`; keep supplied factor/digit hypotheses explicit. |
| D5 `SimpleScalarDegree` | rank-one F-module W implies `Nat.card F = p ^ finrank (ZMod p) W` | READY: finite vector-space cardinalities; actual prime-field dimension controls niveau. |
| D6 `RaynaudPointCoordinate` | nonzero point x implies `eval x (fundamentalCoordinate ... i) ≠ 0`; scalar action gives `eval (a • x) c = χ(a)*eval x c` | Character functions and generation; nonzero coordinate-ring element alone does not imply nonzero evaluation. |
| D7 `RaynaudValuationDigits` | actual unramified coefficients imply `∀ i, valuation (a i)=0 ∨ valuation (a i)=1` | C5 parameter products and preserved uniformizer; general DVR, not only S1 over Z_p. |
| D8 `RaynaudPointPower` | r=1,2: `eval x c ^ (p^r-1) = π^m * u`, `u : Rˣ`, m the weighted binary digits | D6/D7, S2 and actual cyclic equations; check coefficient orientation. |
| D9 `RaynaudTowerRootCharacter` | `residue (σ x / x) = θ σ ^ m` over actual strict-Henselian fraction field | D8; generalize S4 unit correction and compatible integral closures/inertia actions. |
| D10 `RaynaudCharacterDescent` | original inertia factor's character in `AlgebraicClosure (ZMod p)` equals the derived digit power | D9, normal descent/action agreement, compatible residue embeddings. |
| D11 `FiniteFlatFactorSpectrum` | each simple factor of prime-field dimension ≤2 has the charpoly of D10 eigenvalues and Frobenius conjugates | D3/D5/D10; scalar-line operator transport. |
| D12 `FiniteFlatTameSpectrum` | `hp,hflat,hdet ⊢ ∃ t, GeneratesCyclotomic t ∧ ∃ a b, charpoly(t)=(X-C a)*(X-C b) ∧ (orderOf(a/b)=p-1 ∨ orderOf(a/b)=p+1)` | D1/D4/D11, determinant product, fundamental-character surjectivity. Choose niveau-two generator FIRST, then its cyclotomic norm; no wild splitting. |
| D13 `FiniteResidueSpectrum` | finite k, rank-two finite-flat k-representation implies analogous spectrum over `AlgebraicClosure k` | D6–D12 with k-linear factors. Restriction to F_p has dimension `2*[k:F_p]`; D12 does not suffice. |
| D14 `CyclotomicRestrictionIrreducible` | residual absolute irreducibility + flatness + determinant + large p implies absolute irreducibility on cyclotomic kernel | D12/D13 and existing self-twist/detection. Small primes separate. |

D6–D14 are arithmetic/assembly obligations, not assumed conclusions. Caps
are implementation stop limits, not certified proof sizes. D13 needs a
further source-based split for higher-niveau coefficient fields.

### From C5 to the exact family target

There is substantial missing theory beyond the spectrum. Each row has a
150-line cap for its named assembly/interface leaf. This does **not** assert
that absent prerequisite theories fit into that cap: those require further
source-based decomposition and definitions before implementation. No record
may carry these conclusions as fields.

| Leaf (cap 150) | Lean sketch / concrete obligation | Dependencies |
|---|---|---|
| F01 compatible torsion maps | `∃ maps, ∀ n, genericHom (maps n) = prescribedTransition n` | C5 and HR torsion models; uniqueness supplies diagram commutativity. |
| F02 integral exact levels | `Function.Exact (points (i n)) (points (q n))` and integral kernel/quotient identifications | F01, `PrimePowerExact`, existing flat closures/quotients. |
| F03 p-divisible object | `∃ H, ∀ n, Nonempty (H.level n ≅ torsionModel n)` | F01/F02; p-divisible-group definition and level axioms missing. |
| F04 weight-two comparison | `finrank K (gr 0 D)=1 ∧ finrank K (gr (-1) D)=1` | F03; period rings/comparison theorem missing, not consequences of C5. |
| F05 coefficient normalization | `∃ L ι, Function.Injective (ι : R →+* integers L)` with compatible continuous base change | Finite free local domain; normalization/continuity; preserve original R and representation. |
| F06 residual/small-prime branches | derive required residual hypotheses from HR, or construct families for the remaining cases | D14 only handles its large-prime irreducible inputs. Cannot add blueprint's omitted assumption to Lean target. |
| F07 potential modularity | `∃ F, IsTotallyReal F ∧ IsModular (ρ.map (algebraMap ℚ F))` with local/disjointness conditions | F04/F06; Snowden potential-modularity theory missing. `MoretBailly.statement` itself has `sorry`. |
| F08 coefficient field | `∃ E, NumberField E ∧ ∀ v, ∃ P : E[X], ...` common Hecke/Frobenius polynomials | F07; Hilbert-form/Hecke coefficient theory missing. |
| F09 attached members | `∀ ℓ φ, ∃ τ, ∀ v, charFrob τ v = (P v).map φ` at good places | F08; attached representations/local-global compatibility missing. |
| F10 Brauer restriction data | actual induced/restricted character identity over one E | F09, Brauer induction and coefficient descent, not integer self-pairing alone. |
| F11 effective descent | `∃ τ, finrank E Vτ=2 ∧ character τ = signedDescentCharacter` | F10, `BrauerEffectivityCoefficients`, semisimple character theory and continuity. |
| F12 all-embedding HR models | `∀ ℓ φ, ∃ A W τ r, IsHardlyRamified ... τ ∧ τ.baseChange.conj r = σ ℓ φ` | F11; stable lattices, local-global compatibility, flatness at ℓ and square-trivial inertia at 2; every embedding. |
| F13 original equivalence | `∃ ψ r', (ρ.baseChange _).conj r' = σ hp ψ` with exact R algebra/continuous action | F05/F11, semisimplicity and Brauer–Nesbitt; trace equalities alone insufficient. |
| F14 family packaging | exact existential of `mem_isCompatible` | F08–F13 and all universe/topology/tower instances; new theorem first. |
| F15 replace admission | delegate old theorem to axiom-clean F14 | Separate integration: current BRIEF forbids edits to `Family.lean`. |

F03/F04 and F07–F11 are **large missing theory**, not ready short proofs.
An exhaustive elaborated Lean split cannot honestly be certified before
those APIs exist. F06 is a mathematical statement-scope gap as well.
W17 algebra checkpoint: D1–D5 are implemented in the five modules named above
under `FLT.Deformations.RepresentationTheory` (59, 52, 61, 73, 41 lines).
Foreground individual builds and module-only lints pass; all 15 declarations
in `W17_ALGEBRA_AXIOMS.log` use only the three standard axioms. D4 gives the
canonical factors and nonzero trace; ratio/norm orders reuse `TameSpectrumDigits`.

D6 is now ready from `CharacterRank.scalar_orbit` and injectivity of
`FF.characterCoordinates`: prove scalar evaluation, then nonvanishing for
integral character vectors, then apply to the actual fundamental generator.
D7 correction: `RaynaudDVRParameterValuation.dvr_valuation_digits` already
proves the general DVR lemma. The new ≤150-line `RaynaudValuationDigits`
only applies it to `fundamentalCoefficient_complement`, with p irreducible
in the actual unramified base. Do not re-prove the abstract digit lemma.
D8 is refined before implementation into `RaynaudEvaluatedCycle` (≤150):
evaluate the actual cyclic equations on points and eliminate cycles of length
one/two; and `RaynaudPointPower` (≤150): apply the actual D7 binary unit
coefficients to give p-power-times-unit equations, with both digits exhibited.
Dependencies are D6/D7 and `RaynaudTwoCoordinates`; these are now ready.
D9 is refined into D9a `RaynaudIntegralUnitCorrection` (≤150), lifting units
from any coefficient ring integral over the original completion integers into
the original integral closure and proving the root correction is a unit;
D9b `RaynaudIntegralCoordinateCharacter` (≤150), identifying its reduced inertia
ratio with the uniformizer-root character power; and D9c actual point/closure
transport (≤150 per further leaf) applying D9a/b to D8 on the constructed tower.
D9a/b are ready and avoid rebuilding the entire root-character API over the
infinite base. D9c/D10 still require compatible embeddings and descent.

### W17 verified endpoint and remaining first gate

Checked at 2026-10-03 07:29 UTC by `python3 W17_FINAL_CHECKS.py`, individual
foreground build/lint logs, and `W17_AXIOMS.lean` (artifacts outside FLT).
D1–D8 and D9a/b are implemented: eleven modules, 29 declarations, each file
≤77 lines and every dependency-axiom set contained in `{propext,
Classical.choice, Quot.sound}`. D6–D9 modules are in `FLT.GroupScheme`.
`W17_BOUNDARY_AXIOMS.lean` still reports `sorryAx` for the original family theorem.

The actual endpoint `FF.fundamentalValue_two_binary` supplies binary digits
and an integral unit for the equation of an actual nonzero point coordinate,
with exponent **p*a+b**. The one-cycle version supplies a binary exponent too.
The scalar lift satisfies algebraic action laws and matches the generic action;
there are no supplied coordinate equations, weights, or spectrum conclusions.
The hypothesis `Irreducible (p : R)` expresses unramifiedness at this local
endpoint; W16 constructs such bases, but the original-model spectrum wrapper
has not been assembled.

`exists_integral_coordinate_ratio` works in the ORIGINAL number-field
completion closure. It allows coefficients from any ring whose image is
integral over the original completion integers. It constructs an integral
ratio and proves its residue equals the original inertia root-character power.
This removes the need to assume that S4's unit was in the original base ring.
It does not itself place the constructed Raynaud model in that closure.

Refine D9c before further implementation (each whole-file cap 150):

| Leaf | Lean sketch | Dependencies |
|---|---|---|
| D9c1 closure placement | construct the algebraic-closure equivalence over the tower fraction field, extending its prescribed embedding into the original closure | Actual `RaynaudStrictHenselian` fraction-field embedding, algebraicity and algebraic-closure universal property. |
| D9c2 original inertia fixes tower | `∀ σ : localInertiaGroup v, ∀ a : Rsh, σ (ι a) = ι a` | Each actual finite stage unramified; residue roots and Henselian uniqueness; pass through directed union. Must prove this for the chosen embedding. |
| D9c3 evaluation transport | transported `fundamentalValue` and coefficient image satisfy D8 equations in the original closure, and evaluation intertwines original inertia | D9c1/c2, generic point base change and action agreement; then apply proved D9a/b. |

D10–D14 and F01–F15 retain their displayed obligations. In particular,
prime-field rank-two algebra does not supply larger coefficient-field spectra,
small-prime/residually reducible branches, or potential modularity.

The current main consumer path, checked by reading the three files, is
`FermatsLastTheorem.lean:19` →
`PNat.pow_add_pow_ne_pow_of_three_inputs` (`Assembly/ThreeInputFinal`) →
`FLT.Assembly.hardlyRamifiedCompatibleFamilies` (`Assembly/ExistingInputs:36`)
→ `IsHardlyRamified.mem_isCompatible`. The adapter already forwards the exact
statement, so no additional mathematical gate lies between it and the main
consumer. `HardlyRamified/PrimeField:61` is a second consumer. Main separately
uses the lifting input and `Mazur_statement`; finishing this family branch
alone would not certify all of main. No whole-library build/lint was run.

Checked 2026-09-30 against `af51e4ea`; commands at the end reproduce the audit.
This is a dependency map, not a proof of `mem_isCompatible`.

## Exact target and proved leaves

`HardlyRamified/Family.lean:29–68` quantifies over every odd prime p, a finite
**free**, local, topological domain R over ℤ_[p], and a finite free rank-two
R-module V. Its sole proposition argument is `IsHardlyRamified hpodd hv ρ`.
The exact conclusion has three jointly chosen components:
1. A number field `E : Type v`, `σ : GaloisRepFamily ℚ E 2`, and `σ.isCompatible`.
2. For **every** odd ℓ and **every** embedding `φ : E →+* AlgebraicClosure ℚ_[ℓ]`,
   a finite free local domain A over ℤ_[ℓ], rank-two free W, HR τ, all displayed
   topology/algebra/tower instances, and a linear equivalence r satisfying
   `(τ.baseChange (AlgebraicClosure ℚ_[ℓ])).conj r = σ hℓ φ`.
3. An algebra/continuous scalar action for the original R, an embedding ψ of E,
   and r' with `(ρ.baseChange (AlgebraicClosure ℚ_[p])).conj r' = σ hp ψ`.
The universes, algebra actions and actual equalities cannot be replaced by traces.

| Target obligation | Proved ingredients | Remaining gate / separate program |
|---|---|---|
| Apply an existence theorem to this input | HR determinant/oddness; global absolute irreducibility under its stated hypotheses | HYP: residual irreducibility, cyclotomic restriction (A1), arbitrary R and small p cases. The Lean theorem has no residual irreducibility assumption; the blueprint explicitly does. |
| Residual cyclotomic restriction (A1) | W2 trace support; W3 scalar obstruction; W4 quadratic self-twist; D1–D4b actual cyclotomic inertia detection | FF-SPECTRUM below, finite-residue-field coefficient extension, then restriction assembly. No implication from global irreducibility alone. |
| Weight two | W1 coefficient exact sequences; W5 uniqueness of generic-fiber extensions | MODEL-MAPS: existence of compatible integral morphisms (Raynaud 3.3.3/3.3.6); PDIV: exact integral p-divisible levels; PADIC-COMPARISON: de Rham periods and graded ranks 1 in degrees 0, −1. Separate programs. |
| E and compatible σ | F3 integer self-pairing calculation | POT-MOD: Snowden 5.1.2; ATTACH: common coefficient field/Hilbert-form representations; DESCENT: Brauer induction, self-pairing and effective actual rank two (Snowden 9.2.1). Separate programs, not consequences of F3. |
| Every odd-ℓ integral HR member | coefficient/base-change and lattice transport APIs | ALL-MODELS: simultaneous integral models, flatness at ℓ and square-trivial inertia at 2, including every embedding. Strong compatibility alone does not give these. |
| Original member identified | conjugacy/trace transport APIs; F1 extracts traces from an existing family | ORIGINAL: actual equivalence and compatible coefficient embeddings in descent; traces alone need semisimplicity. |
| FLT consumer only | F2 reduces to Frey residual cofinite traces; existing three-adic trace theorem | A weaker p/3 trace route is available, but does not prove the exact family statement. |

W1 = `PrimePowerExact`; W2 = `SelfTwistTrace`; W3 = `TameTraceObstruction`;
W4 = `CyclicRestrictionTwist`; W5 = `GroupScheme/GenericFiberMapUnique`.
D1 = `CharacterRange`; D2 = `LocalCyclotomicRamification`;
D3 = `LocalCyclotomic{Character,Inertia,Surjectivity,Tame,Generator}`;
D4 = `Cyclotomic{QuadraticDetection,InertiaDetection}`.
F1/F2/F3 are `FamilyTracePair`, `Assembly/FreyTraceInput`,
`BrauerEffectivityCoefficients`. These are prerequisite proofs, not removed admissions.

## Sources and scope of FF-SPECTRUM

[R] Raynaud, *Schémas en groupes de type (p,...,p)*, BSMF 102 (1974),
[pp. 241–280](https://www.numdam.org/item/BSMF_1974__102__241_0/).
PDF checked locally (`Scratch/raynaud1974.txt`): §3.3 equations (1),(2), p.266;
§3.4 equations (6)–(9), pp.269–270; Thm.3.4.1/3.4.3 and Cor.3.4.4.
**3.4.4**, not the model-uniqueness Cor.3.3.6, is the inertia-weight source.
[S] Serre, *Sur les représentations modulaires de degré 2 de G_Q*, Duke 54
(1987), §2, DOI 10.1215/S0012-7094-87-05413-5: fundamental characters and
rank-two weights. Section reference is a source obligation, not a checked Lean API.
[B] `blueprint/src/chapter/ch03freyreduction.tex:183–215`: family statement
requires irreducible reduction and has an omitted proof. It supplies no inertia lemma.

The source says **Jordan–Hölder factors** have tame characters with digits in
{0,1} over an unramified base. It does not say the entire finite-flat module
has trivial wild inertia: extensions can retain wild unipotent action.
For rank two over F_p and cyclotomic determinant, the semisimple spectra are
`{1, θ₁}` or `{θ₂, θ₂^p}`. Rank two over a larger residue field is a further
coefficient/descent obligation; restriction of scalars is not rank two over F_p.
A θ₁-generator need not be a θ₂-generator. For the niveau-two branch choose
a θ₂-generator first; its norm θ₂^(p+1) generates θ₁. Apply D1/D4's generator
criterion there, not D4b's arbitrary existential witness.

## Five source leaves (whole-module caps; implement ready leaves in order)

All new modules below avoid arithmetic input records. S1–S3 are algebraic
parts of the source proof, not a new name for the finite-flat classification.

### S1 — READY, cap 180: parameter valuations
`FLT/GroupScheme/RaynaudParameterValuation.lean`; namespace `RaynaudParameters`.
[R] §3.3(2), specializing e=1. Binders `p : ℕ`, `[Fact p.Prime]`:
```lean
theorem valuation_pair {a b : ℤ_[p]} (u : ℤ_[p]ˣ)
    (h : a * b = (p : ℤ_[p]) * u) :
    a.valuation + b.valuation = 1
theorem valuation_digits {a b : ℤ_[p]} (u : ℤ_[p]ˣ)
    (h : a * b = (p : ℤ_[p]) * u) :
    (a.valuation = 0 ∧ b.valuation = 1) ∨
    (a.valuation = 1 ∧ b.valuation = 0)
```
Anchors: `PadicInt.valuation_mul`, `valuation_p`, `valuation_one`.
Derive nonvanishing and unit valuation; do not assume the desired bounds.
Dependency: Mathlib only. Strict-henselian/unramified-base generalization is
part of RAYNAUD-PRESENTATIONS below, not claimed by this ℤ_p specialization.

### S2 — READY, cap 200: eliminate cyclic coordinates
`FLT/GroupScheme/RaynaudTwoCoordinates.lean`; namespace `RaynaudParameters`.
[R] §3.4(6), r=1,2. Binders `[Field K]`, `p : ℕ`, `a b x y : K`:
```lean
theorem coordinate_one (hp : 1 ≤ p) (hx : x ≠ 0)
    (h : x ^ p = a * x) : x ^ (p - 1) = a
theorem coordinate_two (hp : 1 ≤ p) (hx : x ≠ 0)
    (hxy : x ^ p = a * y) (hyx : y ^ p = b * x) :
    x ^ (p * p - 1) = a ^ p * b
```
Also expose the swapped equation and automorphism ratio's (p²−1)st power
when an automorphism fixes a,b. Anchors: `pow_mul`, `mul_pow`, `pow_sub_mul`.
Dependency: field algebra only. This does not construct Raynaud coordinates.

### S3 — READY, cap 260: binary digits and generator orders
`FLT/Deformations/RepresentationTheory/TameSpectrumDigits.lean`;
namespace `Representation`. [R] 3.4.1–3.4.3; [S] §2 rank-two specialization.
Binders `[Field k]`, `z : kˣ`, `p a b : ℕ`:
```lean
theorem ordinary_digits (hp : 3 < p) (hz : orderOf z = p - 1)
    (ha : a ≤ 1) (hb : b ≤ 1) (hdet : z ^ a * z ^ b = z) :
    (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)
theorem niveau_two_digits (hp : 3 < p) (hz : orderOf z = p * p - 1)
    (ha : a ≤ 1) (hb : b ≤ 1)
    (hdet : z ^ (a + p * b) * z ^ (p * a + b) = z ^ (p + 1)) :
    (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)
theorem niveau_two_ratio_order (hp : 1 < p) (hz : orderOf z = p * p - 1) :
    orderOf (z / z ^ p) = p + 1
theorem niveau_two_norm_order (hp : 1 < p) (hz : orderOf z = p * p - 1) :
    orderOf (z ^ (p + 1)) = p - 1
```
Add nonzero sums via W3. Anchors: `pow_inj_mod`, `orderOf_pow_of_dvd`,
`orderOf_inv`; dependencies Mathlib and W3. No fundamental characters constructed.

### S4 — IMPLEMENTED, cap 400: integral unit correction and character evaluation
Module `RaynaudCoordinateCharacter`. [R] §3.4(9); uses the lifts root API.
Exact correction sketch using existing local notation: `v` a rational place,
`O := v.adicCompletionIntegers ℚ`, `Kv := v.adicCompletion ℚ`,
`Ω := AlgebraicClosure Kv`, `A := IntegralClosure O Ω`:
```lean
-- π : O, α x : Ω, n m : ℕ, u : Oˣ
(hn : 0 < n) (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ))
(hα : α ^ n = algebraMap Kv Ω π.1)
(hx : x ^ n = (algebraMap Kv Ω π.1) ^ m * algebraMap O Ω (u : O)) :
  ∃ z : Aˣ, algebraMap A Ω (z : A) = x / α ^ m
```
Then inertia fixes the residue of z, so the reduced x-ratio equals the mth
power of `LocalRoot.character v hn ... hα`. Anchor: `LocalCyclotomicTame`
constructs this correction for ζ−1. Application to Raynaud parameters still
needs the source-to-coordinate and unramified-base transports; these are not
part of the 400-line bridge.

### S5 — BLOCKED, cap 400: actual rank-two spectrum assembly
Future module `FiniteFlatTameSpectrum`. [R] Cor.3.4.4; [S] §2.
Exact endpoint sketch: let `v := LocalCyclotomic.rationalPlace p`,
`k := AlgebraicClosure (ZMod p)`, `ρ : GaloisRep ℚ (ZMod p) (Fin 2 → ZMod p)`:
```lean
(hp : 17 ≤ p) (hflat : ρ.HasFlatProlongationAt v)
(hdet : ∀ t : localInertiaGroup v,
  (ρ.toLocal v t.1).det = (LocalCyclotomic.inertiaCharacter p t : ZMod p)) :
∃ t : localInertiaGroup v,
  (∀ c : (ZMod p)ˣ, c ∈ Subgroup.zpowers (LocalCyclotomic.inertiaCharacter p t)) ∧
  ∃ a b : kˣ,
    (ρ.toLocal v t.1).charpoly.map (algebraMap (ZMod p) k) =
      (Polynomial.X - Polynomial.C (a : k)) * (Polynomial.X - Polynomial.C (b : k)) ∧
    (orderOf (a / b) = p - 1 ∨ orderOf (a / b) = p + 1)
```
Dependencies: S1–S4; lifts F1–F5 and wild-inertia pro-p; RAYNAUD-PRESENTATIONS
(construction and parameter bounds); SIMPLE-FACTORS (wild invariants, flat
subquotients, finite-field characters and trace/charpoly preservation).
Those two named programs are not ≤400-line leaves. Only the final assembly is
capped. Existing rank-three Oort–Tate classification is not general-p Raynaud.

## Verification and integration

Inspected sibling `wt-r1d/FLT/AbsoluteGaloisGroup/FundamentalTame.lean` (active
worktree) for ownership/API; do not copy or import its unfinished changes.
Run `rg -n 'mem_isCompatible|sorry' FLT/GaloisRepresentation/HardlyRamified/Family.lean`;
`rg -n 'HasFlatProlongationAt|class GaloisRep.IsFlatAt' FLT/Deformations/RepresentationTheory/GaloisRep.lean`;
`rg -n 'valuation_mul|valuation_p' .lake/packages/mathlib/Mathlib/NumberTheory/Padics/PadicIntegers.lean`;
`rg -n 'orderOf_pow_of_dvd|pow_inj_mod' .lake/packages/mathlib/Mathlib/GroupTheory/OrderOfElement.lean`;
`rg -n 'deRham|HodgeTate|BarsottiTate' FLT .lake/packages/mathlib/Mathlib`.
For S1–S3: foreground `LEAN_NUM_THREADS=2 lake build MODULE`, then individually
`LEAN_NUM_THREADS=2 lake exe runLinter MODULE`; audit every new theorem with
`#print axioms`, check caps and sorted FLT imports. Commit each item locally.
No push; no admission changes; blockers remain explicit programs above.

S1 checked 2026-09-30: `lake build FLT.GroupScheme.RaynaudParameterValuation`,
individual `lake exe runLinter FLT.GroupScheme.RaynaudParameterValuation`, and
`lake env lean W8_S1_AXIOMS.lean` pass. All four theorems use only standard
axioms; module is 56/180 lines. S1 is implemented (READY above records dispatch).

S2 checked 2026-09-30: foreground build, individual module lint and
`lake env lean W8_S2_AXIOMS.lean` pass for `FLT.GroupScheme.RaynaudTwoCoordinates`;
all four theorems use only standard axioms, 58/200 lines. S2 is implemented.

S3 checked 2026-09-30 20:54 UTC: foreground build, individual module lint and
`lake env lean W8_S3_AXIOMS.lean` pass for `TameSpectrumDigits` (104/260 lines).
All seven theorems have only standard axioms. S3 is implemented.
`lake env lean W8_TARGET_CHECK.lean` also elaborates the exact S4/S5 propositions
using existing APIs; neither proposition is proved by that statement check.

S4 checked 2026-10-02 22:49 UTC: foreground build, individual module lint and
`lake env lean W9_S4_AXIOMS.lean` pass for `RaynaudCoordinateCharacter`
(106/400 lines; four theorems, only standard axioms). It uses the merged lifts
`RootCharacter` API, proves the displayed correction, and evaluates the reduced
coordinate ratio and character. No finite-flat presentation is assumed constructed.

## S5 subdivision (W9; caps are stop limits, not feasibility claims)

These four leaves replace the two unsized blocker labels. S5a is implemented;
S5c remains a source-construction gate, not an assumed arithmetic record.

### S5a — IMPLEMENTED, cap 220: normal p-group invariants
`PGroupInvariants`; finite `V`, `ρ : Representation (ZMod p) G V`:
```lean
(hG : IsPGroup p G) [Nontrivial V] :
  ∃ x : V, x ≠ 0 ∧ ∀ g, ρ g x = x
[Representation.IsIrreducible ρ] (N : Subgroup G) [N.Normal]
(hN : IsPGroup p N) : ∀ g : N, ∀ x, ρ g.1 x = x
```
Also prove the first statement for `ρ.comp f` from `IsPGroup p f.range`, and
the second from `IsPGroup p (ρ.toHomUnits.comp N.subtype).range`.
Dependencies: Mathlib p-group fixed-point counting and normal invariants.
Use lifts `wildInertia_finite_image_isPGroup` on the finite automorphism image;
wild inertia itself is not asserted to be a torsion p-group.

### S5b — BLOCKED on base transport, cap 300: flat simple subquotients
For a finite unramified extension L/Kv, let R be its integer ring and Ω an
algebraic closure with the induced L action. For equivariant additive maps
`i : U →+[Gal(Ω/L)] X`, `q : U →+[Gal(Ω/L)] W`, prove:
```lean
(hX : GaloisModule.IsFiniteFlat R L Ω X)
(hi : Function.Injective i) (hq : Function.Surjective q) :
  GaloisModule.IsFiniteFlat R L Ω W
```
Use existing `IsFiniteFlat.subobject` then `.quotient`; construct hX by
unramified base change of the original model, not as an extra S5 hypothesis.
Choose L so each inertia composition factor and its finite-field scalar
endomorphisms descend. Dependencies: existing base-change/subquotient APIs,
S5a, finite tame cyclicity (lifts lane), and finite Galois descent. Include actual
point equivalences; restriction of scalars must preserve the F_p dimensions.

### S5c — BLOCKED, cap 400: rank-one/rank-two Raynaud presentations
Over the strict henselization of R, for each simple factor W from S5b of
F_p-dimension r=1 or 2, construct its F_(p^r)-action on the finite-flat model H.
The action is algebraic data, not a hypothesis asserting inertia weights.
With `B := MvPolynomial (Fin r) R`, the presentation statement is:
```lean
∃ a b : Fin r → R, ∃ u : Fin r → Rˣ,
  (∀ i, a i * b i = (p : R) * u i) ∧
  Nonempty (H ≃ₐ[R] B ⧸ Ideal.span (Set.range
    (fun i ↦ MvPolynomial.X i ^ p -
      MvPolynomial.C (a i) * MvPolynomial.X (i + 1))))
```
Here H denotes the coordinate ring, with rank p^r, killed-by-p Hopf structure
and the constructed field action. Prove compatibility of the coordinates
with that action and the generic point equivalence, not only an algebra iso.
Dependencies: S5b, Raynaud §3.3(1),(2), and generic-morphism extension existence.
Generalize S1 to this unramified DVR and descend the coordinate characters;
S1 over ℤ_p alone does not do this. Neither the strict-henselian transport nor
general-p presentation/endomorphism extension exists in the current API.
If this cannot fit 400 lines, its construction must be split before continuing.

### S5d — BLOCKED on S5b/S5c, cap 400: spectra and assembly
Prove the exact S5 existential above, with only hp, hflat and hdet as inputs.
First prove charpoly preservation for an invariant subspace U of an operator T:
`T.charpoly = (T.restrict hU).charpoly * (U.mapQ U T hU).charpoly`, via an
adapted basis and `Matrix.charpoly_fromBlocks_zero₂₁`. Apply to the factors.
Use S2/S4 on S5c's actual coordinates, identify finite-field Frobenius conjugates,
then S3 selects complementary digits and computes the ratio orders. Dependencies:
S1–S5c; lifts F1–F5/pro-p; D4. Choose a niveau-two generator before its norm,
identify the norm with cyclotomic inertia, and transport residues to the fixed
`AlgebraicClosure (ZMod p)`. No splitting of wild extensions is required.

S5a checked 2026-10-02 23:14 UTC: foreground build, individual module lint and
`lake env lean W9_S5A_AXIOMS.lean` pass (95/220 lines; all five theorems use
only standard axioms). S5b–S5d remain blocked; no classification is claimed.

## W12 refinement of the C3/C5 construction gates

Source checked 2026-10-03: `Scratch/raynaud1974.txt`, pp.266–268,
§3.3(a), Proposition 3.3.2 and Theorem 3.3.3. The source proves uniqueness
using presentations of maximal/minimal models carrying the field action,
then dévissage; it does not supply the proposed direct primitive-denominator
Hopf argument. Constructing presentations using C5 and then proving C5 from
those presentations would be circular. The maximal/minimal-model route must
construct their actions independently (Proposition 3.3.1).

The following are subdivisions, with whole-module caps. They do not assume
the denominator obstruction or mark C3/C5 complete.

| Leaf | Cap | Endpoint | Remaining input |
|---|---:|---|---|
| C5c1 scaled multiplication | 150 | Derive unit and multiplication identities for C5b's actual integral numerator; a positive denominator gives square-zero products modulo the uniformizer. | Generic algebra map and flat target only. |
| C5c2 numerical coordinate bound | 100 | In the source's cyclic valuation relations, a nonzero nonnegative scaling valuation forces p−1 ≤ e. | Actual presentations and compatible coordinate scaling must still be constructed. |
| C5c3 Hopf obstruction | 150 per further leaf | Deduce the bound for arbitrary prescribed p-torsion generic maps. | Either a separate Hopf proof or independent maximal/minimal models, presentations and dévissage; C5c1/C5c2 alone do not suffice. |
| C3d1 directed-union DVR | 150 | The supremum of directed embedded DVR stages with the same base uniformizer is a DVR. | C3c must still construct a directed family containing all required stages. |
| C3f0 finite-stage Henselianity | 100 | Finite unramified domain stages over an adically complete DVR are complete and Henselian. | The extended maximal ideal equals the stage maximal ideal, as proved by C3a. |
| C3f0b actual descent base | 100 | Transport p-adic completeness to the rational completion integers and prove Henselianity of the actual finite inertia descent ring. | C2, finiteness of integral closure and C3f0. |
| C3f1a finite-data descent | 100 | A polynomial and proposed root over a directed union descend together to one stage. | A directed family, still to be constructed by C3c. |
| C3f1 directed-union Henselianity | 150 | A directed union of local Henselian stages is Henselian. | Actual stages must be shown Henselian and inclusions local. |

C5d/C5e remain downstream of C5c3. C3c (compatible common unramified
stage), C3e (separably closed residue field) and final C3f tower packaging
remain construction obligations. A theorem about a supplied directed family
does not construct the strict henselization.

W12 checked 2026-10-03: C5c1 is `GenericFiberScaledMultiplication` (62/150),
C5c2 is `RaynaudScalingValuation` (65/100), C3d1 is `RaynaudDirectedUnion`
(113/150), C3f0 is `RaynaudStageHenselian` (48/100), C3f1a is
`RaynaudDirectedPolynomial` (57/100), and C3f1 is `RaynaudDirectedHenselian`
(77/150). C3f0b is `AbsoluteGaloisGroup/InertiaDescentHenselian` (59/100).
Foreground module builds, individual module lints and
`lake env lean W12_AXIOMS.lean` pass. All 19 new theorems use only
`propext`, `Classical.choice`, `Quot.sound`. The complete-base union theorem
derives stage Henselianity from finiteness and preservation of a uniformizer.

Next construction leaves (caps remain stop limits):

| Leaf | Cap | Required construction |
|---|---:|---|
| C3c1 prescribed-root factor | 150 | Factor the second stage's defining monic polynomial over the first Henselian stage, lifting its separable residue factors; select the factor vanishing at its prescribed root in Ω. |
| C3c2 common embedded stage | 150 | Use that factor's quotient to embed both original stages in one finite DVR preserving π; convert to a subalgebra in the same Ω. |
| C3e1 residue compatibility | 150 | Lift finite separable residue extensions relative to an existing stage, retaining its prescribed embedding and finite degree over R. |
| C3e2 residue closure | 150 | Descend a separable residue polynomial to a stage and use C3e1/C3c2 to place a root in the union residue field. |

The second stage's polynomial can become reducible after passing to the first
stage's residue field. Thus C3a's irreducible-reduction quotient theorem alone
does not prove C3c1/C3c2. No common-stage or separable-closure claim follows
from the completed union lemmas without these constructions.

## W13 construction progress

C3c1 uses the prescribed root's minimal polynomial instead of a general
factor-lifting theorem. A finite domain over a Henselian local ring is local
(by finite-algebra idempotent decomposition). Its separable special fibre is
reduced Artinian local, hence a field. Thus the minimal polynomial has
irreducible separable reduction and divides the original monic polynomial.
`RaynaudHenselianFactor` is 90/150 lines; foreground build, module-only lint,
and the three-theorem axiom audit passed on 2026-10-03.

C3c2 is refined into two leaves before implementation: C3c2a (150 lines),
the actual single-root subalgebra in the prescribed closure, with finite DVR,
uniformizer and unramified properties; C3c2b (150 lines), a common stage for
two finite embedded unramified stages, using a primitive generator of the
second stage and C3c1 over the first. No directed-family property is assumed.

C3e2 is refined before implementation into C3e2a (150 lines), defining the
family of all finite embedded unramified DVR stages preserving π and deriving
its nonemptiness and directedness from C3c2; C3e2b (150 lines), adjoining roots
of lifted separable residue polynomials to an existing stage; and C3e2c
(150 lines), descending residue polynomials to a stage and transporting their
roots into the union residue field. Final C3f packaging (150 lines) combines
the actual family with C3d1/C3f1 and C3e2c, including the fraction-field tower.

W13 C3 construction checked 2026-10-03: C3c2a is `RaynaudRootStage`
(73/150), C3c2b is `RaynaudCommonStage` (84/150), C3e1 is
`RaynaudRelativeResidue` (55/150), C3e2a is `RaynaudStageFamily` (100/150),
C3e2b is `RaynaudStageResidueRoot` (53/150), C3e2c is
`RaynaudResidueClosure` (67/150), and C3f packaging is
`RaynaudStrictHenselian` (107/150). Individual foreground builds and
module-only lints pass. `W13_AXIOMS.lean` checks all 22 proof declarations
(including the new instances), each with only the three standard axioms.

The family is now constructed, not supplied: all finite unramified embedded
DVR stages preserving π form a nonempty directed family. The union is
integral, faithfully flat, Henselian, preserves π, and has separably closed
residue field separable over the original residue field. Its fraction field
is constructed as an algebraic separable extension of the perfect base
fraction field, with a compatible embedding in the prescribed closure.
No finite-dimensionality of the infinite union is asserted.

## W13 independent C5 route: extremal models before presentations

Source checked with `sed -n '686,731p' Scratch/raynaud1974.txt` and
`sed -n '875,930p' Scratch/raynaud1974.txt`: Raynaud 2.2.2 constructs upper
bounds by schematic graph closure; 2.2.3 bounds their coordinate rings in
the finite integral closure of an étale generic algebra. Cartier duality
constructs the minimum. Proposition 3.3.1 extends generic automorphisms to
these extremal models. Only then may the field-action presentation argument
of §1.5/§3.3 be used. C5-dependent presentations remain forbidden inputs.

Each row below is a whole-module leaf capped at 150 lines; split again before
exceeding a cap. This is a dependency plan, not a completion claim.

| Leaf | Construction / checkable endpoint | Dependencies |
|---|---|---|
| C5m1 integral coordinate images | Embed coordinates of any model, along a prescribed generic identification, into one fixed generic algebra; prove they are integral and finite over R. | Generic coordinate comparison and finite flatness only. |
| C5m2 finite ambient bound | Prove the integral closure of an integrally closed Noetherian base in a finite étale generic algebra is a finite module, by its finite product of separable field factors. | Mathlib field integral-closure finiteness and étale decomposition. |
| C5m3 graph upper bounds | The existing graph closure gives a model dominating two identified models; prove the coordinate-image inclusions in the fixed generic algebra. | C5m1, existing schematic closure; no small-ramification theorem. |
| C5m4 maximal model | Apply the ascending-chain condition inside C5m2's ambient module and C5m3 to construct a greatest coordinate image, and select its actual finite flat model. | C5m1–C5m3. |
| C5m5 maximal automorphisms | Transport the maximal model by a generic automorphism; maximality and uniqueness give the prescribed integral automorphism and its inverse. | C5m4, generic map uniqueness. |
| C5m6 minimal model | Apply C5m4/C5m5 to the Cartier dual and dualize back, including the point identifications and reversed domination. | Independent Cartier dual/base-change APIs. |
| C5m7 extremal field actions | Extend nonzero field scalars by C5m5/C5m6, extend zero by the zero morphism, and prove addition/composition/unit laws by generic uniqueness. | Extremal models only; no C5 extension theorem. |
| C5p1 character projectors | Construct scalar-character idempotents on the augmentation algebra of an extremal model. | C3, C5m7; refine C7 with the independent action. |
| C5p2 character ranks | Derive rank-one character eigenspaces and choose their generators from the Hopf/field-action rank calculation. | C5p1; no assumed rank-one eigenspaces. |
| C5p3 cyclic equations | Derive the actual p-power relations and the dual parameter identities a_i b_i = p u_i. | C5p2 and Cartier pairing; refine C9/C10. |
| C5p4 presentations | Prove generation and the polynomial-quotient isomorphism for the extremal models. | C5p2/C5p3; refine C11. |
| C5v1 extremal equality | Derive coordinate scalings for the domination map, apply C5c2, and prove maximum = minimum below e < p−1. | Independent C5p4 presentations. |
| C5v2 dévissage | Pass from simple field-action factors to the prescribed p-torsion model maps via finite-flat closures and quotients. | C5v1 and exactness of the actual models. |
| C5v3 integral extension | Obtain integral coordinates and extend the prescribed generic map using the existing graph extension endpoint. | C5v2; discharges C5d/C5e. |

W13 independent maximal-model refinement: C5m3 works for an arbitrary generic
map to the second model, so C5m4's greatest image contains pullbacks from
**every** target model. C5m5 therefore extends all generic maps out of the
constructed maximum; the automorphism statement is a consequence. This
stronger endpoint still uses only finite integral closure and graph closure.

C5m6 is split before implementation into four ≤150-line leaves: C5m6a packages
the Cartier dual of a general `FF R K` over a DVR with characteristic-zero
fraction field; C5m6b transports generic Hopf maps to generic point maps and
proves Cartier-dual/base-change compatibility; C5m6c proves the bidual
comparisons and naturality; C5m6d dualizes C5m5 to construct the minimum and
its prescribed-map extension property. The existing `FiniteFlatObject` dual
is specialized to rational generic fields, so it cannot be silently substituted
for this general DVR/fraction-field construction.

W13 C5m1–m5 checked 2026-10-03: `RaynaudIntegralCoordinates` (68/150),
`RaynaudIntegralClosureBound` (48/150), `RaynaudModelUpperBound` (62/150),
`RaynaudMaximalModel` (74/150), and `RaynaudMaximalExtension` (68/150)
pass foreground builds and individual module lints. `W13_MAXIMAL_AXIOMS.lean`
audits all 16 new declarations, including definitions with proof obligations;
only `propext`, `Classical.choice`, and `Quot.sound` occur. The constructed
maximum extends every prescribed generic map out of it. C5c is still open.

C5m6b is refined into two ≤150-line modules before completing the leaf:
`RaynaudGenericHopfMap` proves the inverse correspondence between generic
Hopf maps and specified point maps; `RaynaudDualGenericMap` proves the
actual dual base-change compatibility. This avoids assuming functoriality.

C5m6c is refined into `RaynaudDualFaithful` (≤150 lines), proving generic
duality faithful and preserving bijections, and `RaynaudBiduality` (≤150),
proving the integral bidual comparison and the transpose identity used to
turn an extension out of the maximum into an extension into the minimum.

C5m7 is refined before implementation into two ≤150-line leaves:
`RaynaudScalarAction` transports a scalar action across a specified generic
bijection and derives integral action laws from endomorphism extension;
`RaynaudExtremalActions` applies it to both constructed extrema. The scalar
action starts from actual module data and a commuting Galois action.

W13 C5m6/C5m7 checked 2026-10-03: `RaynaudCartierDual` (58/150),
`RaynaudGenericHopfMap` (82/150), `RaynaudDualGenericMap` (79/150),
`RaynaudDualFaithful` (73/150), `RaynaudBiduality` (66/150),
`RaynaudMinimalModel` (72/150), `RaynaudScalarAction` (74/150), and
`RaynaudExtremalActions` (53/150) pass foreground builds and individual
module lints. `W13_DUAL_AXIOMS.lean` audits all 29 declarations, including
definitions with proof obligations; only the three standard axioms occur.

The minimum is the actual integral Cartier dual of the constructed maximum
of the dual generic fibre. It extends every prescribed generic map into it,
and generic automorphisms extend to integral isomorphisms. The maximum and
minimum carry actual integral lifts of any commuting generic scalar action;
the lifts obey zero, unit, addition (convolution) and composition laws.
These constructions prove the independent extremal-model/action prerequisite
of Raynaud 3.3.1 over a principal domain with characteristic-zero fraction
field, including the strict-Henselian DVR needed here.

C5c remains unproved: C5p1–C5p4 must still derive the character decomposition,
rank-one eigenspaces, dual parameter identities and actual presentations.
C5v1 then compares the two extremal models below the ramification bound;
C5v2/C5v3 must pass from simple factors to the prescribed p-torsion maps.
No presentation depending on C5 was used. The original admission in
`IsHardlyRamified.mem_isCompatible` remains at `Family.lean:68` (checked with
`rg -n 'mem_isCompatible|sorry' FLT/GaloisRepresentation/HardlyRamified/Family.lean`).

## W14 C5p1 refinement (before implementation)

Each leaf is a new whole module capped at 150 lines. Inputs are the scalar
maps and their proved laws from C5m7, never eigenspaces or presentations.

| Leaf | Module | Checkable endpoint | Cap |
|---|---|---|---:|
| C5p1a | `RaynaudAugmentationAction` | Restrict scalar units to the actual counit kernel and prove the representation laws. | 150 |
| C5p1b | `RaynaudCharacterProjector` | Twist by inverse characters and use `Representation.averageMap` to construct projections onto the derived eigenspaces. | 150 |
| C5p1c | `RaynaudHenselianCharacters` | Lift prime-to-residue-characteristic roots of unity from the separably closed residue field and obtain the scalar character system. | 150 |
| C5p1d | `RaynaudCharacterOrthogonality` | Prove distinct projectors orthogonal from character separation. | 150 |
| C5p1e | `RaynaudCharacterDecomposition` | Prove their sum is the identity and derive the direct-sum decomposition of the actual augmentation ideal. | 150 |

C5p2–C5v3 stay open until their prerequisites are derived. Split each further
before implementation if its whole-module proof would exceed 150 lines.

C5p1f (`RaynaudAugmentationDecomposition`, ≤150 lines) instantiates C5p1a–e
on the actual model and finite scalar field, deriving invertibility of the
unit-group order from its residue characteristic.

W14 C5p2 refinement, before implementation (whole modules ≤150 lines):
C5p2a scalar orbits and proportionality of equivariant character functions;
C5p2b the generic character-function submodule and its rank bound;
C5p2c actual model coordinates, counit and scalar-map evaluation;
C5p2d injection of integral eigenspaces into the generic character functions;
C5p2e rank sum and rank-one generators derived from decomposition and the
order of the actual generic point group. No eigenspace rank is an input.

C5p2e is split further before implementation: `RaynaudAugmentationRank`
(≤150) derives the counit splitting and total augmentation rank;
`RaynaudCharacterRankOne` (≤150) combines the sum with C5p2d's bounds and
chooses a basis of each derived eigenspace.

C5p3 refinement before implementation (each ≤150 lines):
- C5p3a `RaynaudCharacterPowers`: multiplication and positive powers carry
  the derived integral character spaces to their product characters; the
  rank-one bases supply actual coefficients for power relations.
- C5p3b: lift a residue-field embedding's fundamental character, identify
  its Frobenius cycle, and specialize the power relations.
- C5p3c: restrict the actual Cartier pairing to the derived summands and
  identify multiplication/comultiplication coefficients by transposition.
- C5p3d: derive the universal iterated structure constants from convolution
  addition and evaluate them on the constant field-vector scheme.
- C5p3e: prove the fundamental constant is p times a unit, and the digit
  constants are units (Raynaud 1.3.1), then obtain the dual parameter identities.
C5p3d/e require their own further split if the universal constant calculation
exceeds a cap; rank-one summands alone do not prove the unit identities.

C5p3b is split before implementation into `RaynaudRootReduction` (≤150),
proving reduction is an equivalence on prime-to-p roots of unity using
Henselian surjectivity and equal cardinalities, and
`RaynaudFundamentalCharacter` (≤150), lifting an actual finite-field
embedding into the residue field and proving its Frobenius power relations.

C5p3b cyclic-coordinate endpoint is a separate ≤150-line module,
`RaynaudCyclicCharacterEquations`: choose the proved character generators,
prove Frobenius periodicity, and obtain their actual p-power coefficients.
This endpoint does not assert the dual identities or polynomial generation.

C5p2 integration is split into `RaynaudIdentifiedCharacters` (≤150), which
transports the scalar module structure through the specified generic
bijection, and `RaynaudExtremalCharacters` (≤150), applying the proved basis
construction to the actual maximum and minimum from C5m7.

W14 C5p1 checked 2026-10-03: the six planned modules build and pass individual
module lint (`W14_LINT_<module>.log`). `W14_P1_AXIOMS.lean` audits all 29
construction/proof declarations; only `propext`, `Classical.choice`, and
`Quot.sound` occur. The endpoint `FF.exists_augmentation_decomposition`
derives the character system and invertible averaging denominator from the
strict Henselian domain and the common finite-field/residue characteristic.
Its eigenspaces are the actual scalar-action eigenspaces of the counit kernel.

W14 C5p2 checked 2026-10-03: all eight modules in C5p2a–e and the identified/
extremal integration pass their foreground builds and individual lints.
`W14_P2_AXIOMS.lean` audits every new proof, instance and construction.
The generic hypothesis is rank one of the original F-vector space of points;
no integral eigenspace rank or presentation is assumed. Scalar orbits give
proportional generic character functions, integral evaluation gives rank at
most one, and the augmentation rank sum forces equality for every character.
`exists_maximal_model_character_bases` and
`exists_minimal_model_character_bases` retain the actual extremal extension
properties and derive all character bases after transferring the module
structure through the specified generic bijection.

C5p3c pairing refinement before implementation (each ≤150 lines):
`RaynaudCharacterTranspose` constructs the transpose action and proves how
projectors pair with it; `RaynaudCharacterDuality` identifies a transpose
character summand with the dual of the original summand;
`RaynaudAugmentationDuality` restricts the actual Cartier pairing to the two
augmentation ideals. The comparison with integral scalar duality must be
proved, not installed as model data.

W14 C5p3a/b checked 2026-10-03: `RaynaudCharacterPowers`,
`RaynaudRootReduction`, `RaynaudFundamentalCharacter`, and
`RaynaudCyclicCharacterEquations` build and pass individual module lint.
`W14_P3_AXIOMS.lean` audits all their declarations against the three-axiom
whitelist. The residue field embedding is constructed from separable
closedness; its unit character lifts multiplicatively and faithfully.
Frobenius periodicity and the proved eigenspace bases give nonzero actual
cyclic coordinates and integral p-power coefficients.
`W14_LOCAL_CHECK.lean` checks the extrema, rank-one and cyclic endpoints over
a DVR with its actual fraction ring. Dual parameter identities and algebra
generation are not consequences claimed by this endpoint.

C5p3c's actual scalar comparison is `RaynaudCartierCharacterDuality` (≤150):
prove the dual scalar laws, prove the augmentation pairing intertwines the
actual dual action and the transpose action, and restrict it to a perfect
pairing on each derived character summand. The multiplication/comultiplication
coefficient identity remains a subsequent leaf.

C5p3c coefficient refinement: `RaynaudPairedCharacterBases` (≤150) chooses
the dual bases using the proved perfect pairing, proves normalization, and
derives the dual power coefficients. `RaynaudCharacterParameterProduct`
(≤150) expresses the product of the two actual coefficients as the iterated
Cartier pairing. Evaluation of this universal pairing as p times a unit is
still C5p3d/e, not a hypothesis of these leaves.

W14 C5p3c checked 2026-10-03: all six pairing modules pass their foreground
builds and individual lints. `W14_PAIRING_AXIOMS.lean` audits 23 declarations;
only the three permitted axioms occur. `W14_PAIRING_CHECK.lean` instantiates
the actual character pairing over a strict Henselian DVR with its fraction
ring, deriving the required averaging inverse from the residue characteristic.
The actual dual scalar action is proved to be the transpose under the
augmentation pairing. Matching character summands therefore pair perfectly;
the original derived bases determine actual normalized dual bases. Both
power coefficients are constructed, and `FF.exists_character_parameter_product`
identifies their product with evaluation of the dual generator's power on
the original generator's power.

**W14 remaining:** C5p3d/e must evaluate this pairing as the universal
fundamental constant and prove it is p times a unit; the digit constants
must also be units. C5p4 (monomial generation and presentation isomorphisms)
and C5v1–C5v3 (extremal scalings, small-ramification comparison, dévissage and
prescribed extension) remain unproved. The scalar addition-by-convolution
law is available from C5m7 but has not yet been used to evaluate these
structure constants. No parameter-unit identity is accepted as model data.

## W15 C5p3d refinement before implementation

Each leaf below has a whole-file cap of 150 lines. No universal constant or
unit property is installed as model data.

| Leaf | New module | Proof obligation |
|---|---|---|
| C5p3d1 | `RaynaudRankOneProjector` | The actual augmentation character projector, extended by the counit splitting, is the normalized generator/dual-generator map. |
| C5p3d2 | `RaynaudRankOneConvolution` | Convolution products and powers of rank-one maps are products and powers of their vector and Cartier functional. |
| C5p3d3 | `RaynaudReducedScalarAverage` | Express the extended projector as the character-weighted average of scalar maps minus the zero scalar. |
| C5p3d4 | `RaynaudScalarConvolution` | Expand powers of finite linear combinations of scalar maps using the proved scalar addition law. |
| C5p3d5 | `RaynaudUniversalCharacterConstant` | Evaluate the scalar expansion on actual character vectors, obtaining a constant defined only from finite-field addition and characters. |
| C5p3d6 | `RaynaudUniversalParameterProduct` | Identify the paired-power evaluation and the product of actual power coefficients with the universal constant. |

C5p3e is subsequent arithmetic work: fundamental constants are p times
units and digit constants are units. C5p4 and C5v1–C5v3 retain their earlier
obligations; C5p3d alone does not close them.

W15 C5p3e initial arithmetic refinement (each ≤150 lines):
`RaynaudUniversalConvolutionAlgebra` realizes the explicit constant in the
additive monoid algebra of F; `RaynaudCharacterConstantBaseChange` proves
coefficient-ring functoriality; `RaynaudCharacterPrimeDivisibility` proves
that the p-fold constant is divisible by p using characteristic-p
nilpotence. These are prerequisites, not the p-times-a-unit assertion.
The remaining arithmetic leaves must prove the quotient by p is a unit
and treat mixed digit constants before C5p4 can use them.

W15 C5p3d checked 2026-10-03: the six new modules pass foreground builds
and individual sequential lints. `W15_AXIOMS.lean` audits all 22 declarations
against `propext`, `Classical.choice`, and `Quot.sound` only.
`FF.character_power_pairing_universal` identifies the actual paired-power
scalar with `CharacterAverage.constant χ (χ ^ n) n`, an explicit iteration
of finite differences involving only finite-field addition and characters.
`FF.exists_universal_character_parameter_product` gives both actual power
coefficients and their universal product. The proof uses the actual
addition-by-convolution law, not an assumed parameter identity. This
repeated-character endpoint does not yet cover mixed digit products.

C5p3e single-character factorial refinement before implementation (each
≤150 lines): `RaynaudCharacterDifferenceOperator` bundles the normalized
finite difference and expands it on monomials; `RaynaudCharacterFactorial`
proves its triangular iteration has diagonal n! when the character comes
from a field embedding; `RaynaudFundamentalDigitUnit` reduces the lifted
fundamental character and derives units for repetitions below p. This
single-character calculation does not assume or prove the mixed-digit unit
statement, or the fundamental quotient-by-p unit statement.

C5p3e fundamental-quotient refinement before implementation (each ≤150
lines): `RaynaudAugmentationDerivation` evaluates additive characters as
derivations at the augmentation; `RaynaudDividedPowerSums` controls divided
p-th powers under addition and scalar multiplication; subsequent capped
leaves must calculate a group generator's divided power and apply the
result to the formal average. The intended residue of the resulting
quotient is -1. None of these intermediate lemmas may assume that the
fundamental constant is p times a unit.

W15 arithmetic prerequisites checked 2026-10-03: the six modules through
`RaynaudFundamentalDigitUnit` pass foreground builds, individual lints and
`W15_ARITHMETIC_AXIOMS.lean` (22 declarations; only the three permitted
axioms). `prime_dvd_constant` proves p-divisibility in R itself by passage
to R/(p). `fundamental_constant_residue` proves the n! residue, and
`isUnit_fundamental_digit_constant` proves the single-character constants
are units for 0 < n < p. Neither theorem claims the mixed-digit calculation
or the p-fold quotient's being a unit.

The final fundamental-quotient leaves are `RaynaudDividedGroupGenerator`
(binomial calculation for [a]-1), `RaynaudDividedCharacterAverage` (weighted
sum and normalized residue -1), `RaynaudCharacterPrimeQuotient` (actual
scalar quotient via character evaluation), and `RaynaudFundamentalPrimeUnit`
(specialize to the constructed fundamental lift). Each cap is 150 lines.

Integration of the arithmetic results is split into
`RaynaudResidueCharacterUnits` (≤150; any character reducing to a field
embedding, including Frobenius twists) and `RaynaudCharacterParameterUnits`
(≤150; the actual original/dual coefficients have p-times-unit product,
and their powers below p have unit coefficients).

## W15 boundary and next leaves

The new repeated-character calculation and the divided-power argument now
prove the fundamental p-times-unit identity without parameter data.
`FF.exists_character_prime_parameter_units` derives both integral power
coefficients and a unit u with a*b = p*u and residue(u) = -1.
`FF.exists_character_digit_parameter_units` derives both unit coefficients
for n repetitions of any residue-embedding character, with 0 < n < p.
The residue-embedding formulation covers every fundamental Frobenius twist.
These are proof statements; validation evidence is recorded below after the
module checks finish.

The mixed-digit gap is still open: a general character has p-adic digits
across several fundamental characters, not just repetitions of one. The
next work must extend the rank-one convolution and universal-average
comparison to finite lists, then prove the mixed constant has residue
product_i (a_i!). A viable proof uses the existing finite-difference
operator: on polynomials in the residue embeddings, its top-degree action
is the corresponding partial derivative; orthogonality removes the other
embeddings. Split that work before implementation into ≤150-line leaves:
mixed rank-one products, mixed universal averages, residue embedding
orthogonality, the degree-lowering calculation, and the mixed factorial/unit
endpoint. The equality of constants across Frobenius twists has not been
asserted here; the proved individual p-times-unit bounds do not require it.

C5p4 (monomial generation and genuine polynomial-quotient isomorphisms)
and C5v1–C5v3 remain unproved. No presentation, generation, general simple
factor dévissage, or prescribed generic-map extension follows merely from
the new coefficient identities. The original family target admission is
unchanged; W15 is partial completion of the requested route.

W15 final validation checked at 2026-10-03 03:38:11 UTC: all 20 modules pass
foreground builds and individual sequential lint. The three W15 axiom
audits cover all 65 named declarations and allow only `propext`,
`Classical.choice`, and `Quot.sound`. `W15_LOCAL_CHECK.lean` instantiates
the actual parameter-product endpoint over a strict Henselian DVR and its
fraction field for every fundamental Frobenius twist; it constructs the
averaging inverse from the residue characteristic and exits 0. All new
modules are below the 150-line cap. `W15_FINAL_CHECKS.log` records source,
artifact, edit-scope and target-admission checks.

## W16 mixed-digit refinement before implementation

All new files have a whole-file cap of 150 lines. Work follows C5p3e,
C5p4, C5v1, C5v2, C5v3 in that order. No model supplies constants,
eigenspaces, generation, or presentations as fields.

| Leaf | New module | Obligation |
|---|---|---|
| C5p3e-m1 | `RaynaudMixedCharacterAverage` | List-indexed finite differences, coefficient base change, and scalar convolution expansion. |
| C5p3e-m2 | `RaynaudPowerCharacterOrthogonality` | Embedding power characters distinguish exponents in 1,…,q−1; compute their weighted sums. |
| C5p3e-m3 | `RaynaudPowerCharacterDifference` | The normalized difference of degree m≤q−1 by weight k is the Hasse derivative of order k. |
| C5p3e-m4 | `RaynaudMixedPowerConstant` | Mixed constants reduce to the product of successive binomial coefficients. |
| C5p3e-m5 | `RaynaudDigitBinomialUnit` | Lucas arithmetic proves those factors nonzero for successive removal of nonzero base-p digits. |
| C5p3e-m6 | `RaynaudMixedDigitUnit` | Lift the computed nonzero residue to a unit in the local coefficient ring. |
| C5p3e-m7 | `RaynaudMixedRankOneConvolution` | Mixed products of actual projectors and normalized rank-one maps. |
| C5p3e-m8 | `RaynaudMixedCharacterParameters` | Actual original/dual mixed monomials have unit coefficients. |

The power-character route computes exact Hasse derivatives on functions
of degree at most q−1. It replaces the proposed multivariate top-degree
argument by orthogonality and Lucas's theorem. It must handle q−1 and the
trivial output character as well as the other positive exponents.
C5p4 and later obligations will be split further before implementation;
the existing gates remain open until their actual proofs are built.

C5p3e-m8 is split before implementation into three ≤150-line leaves:
`RaynaudCharacterMonomials` proves membership and integral coefficients for
nonempty mixed products in the derived bases; `RaynaudMixedCharacterParameters`
identifies the product of the actual coefficients with the mixed universal
constant; `RaynaudMixedDigitParameters` proves both coefficients are units
for every admissible digit vector. This separates the algebraic membership,
Cartier comparison, and arithmetic specialization.

## W16 C5p4 refinement before implementation

Each new file has cap 150. The mixed constants above are the input, not
extra model data.

| Leaf | New module | Obligation |
|---|---|---|
| C5p4a | `RaynaudFundamentalCharacterPowers` | Every integral character is a positive power ≤q−1 of the constructed fundamental character. |
| C5p4b | `RaynaudDigitMonomialGeneration` | The mixed unit identity puts every character generator in the algebra generated by the fundamental coordinates. |
| C5p4c | `RaynaudCoordinateGeneration` | The actual character projectors and counit splitting prove generation of the full coordinate algebra. |
| C5p4d | `RaynaudCyclicPolynomialSpanning` | Cyclic degree-p relations reduce every polynomial to digit monomials; refine again if this exceeds its cap. |
| C5p4e | `RaynaudCyclicPresentation` | The quotient-to-coordinate map is an isomorphism, using generation and the proved rank bound, not an assumed presentation. |

C5p4d/e further refinement (all whole-file caps ≤150):
`RaynaudCyclicMonomials` records elementary product/degree identities;
`RaynaudCyclicMonomialReduction` reduces an excessive exponent by a cyclic
relation and strict total-degree descent; `RaynaudCyclicPolynomialSpanning`
passes from monomials to all polynomial images. `RaynaudSpanningPresentation`
proves the finite-generator/rank criterion for an algebra map to be an
isomorphism, without assuming the source free. `RaynaudCyclicPresentation`
constructs the actual relation quotient and applies that criterion.
The finite-period coordinate restriction and actual-model specialization
will be separate ≤150-line leaves.

C5p4 finite/actual leaves are `RaynaudFiniteCoordinateGeneration` and
`RaynaudActualCyclicPresentation`, both ≤150 lines. They derive periodic
finite generation, coefficients, rank, and the variable-preserving quotient
isomorphism from the actual model.

## W16 C5v1 refinement before implementation

Each leaf has whole-file cap 150. No coordinate scaling is supplied as data.

| Leaf | New module | Obligation |
|---|---|---|
| C5v1a | `RaynaudCharacterMorphism` | Generic scalar compatibility gives integral compatibility; derive the map on character lines and injectivity from generic surjectivity. |
| C5v1b | `RaynaudCoordinateScalings` | Derived rank-one bases give actual nonzero integral scaling coefficients for a generically bijective map. |
| C5v1c | `RaynaudCoefficientBounds` | The actual p-times-unit products bound the actual cyclic coefficients in the DVR valuation. |
| C5v1d | `RaynaudScalingUnits` | Transport actual cyclic equations to the numerical valuation lemma and prove all scaling coefficients are units below the ramification bound. |
| C5v1e | `RaynaudScalarModelIso` | Proved generation makes the domination map bijective; apply to the independently constructed extrema. |

Further refinement is required before any leaf exceeds its cap. C5v2 and
C5v3 retain their separate simple-factor and prescribed-extension obligations.

C5v1c/d are further separated before implementation: `RaynaudCoefficientBounds`
transfers the universal parameter product to any actual coefficient satisfying
the proved power equation; `RaynaudFiniteValuation` supplies finite natural
DVR valuations and product bounds; `RaynaudScalingUnits` applies the existing
integer-valued numerical lemma. All three caps are 150.

C5v1e integration is split before implementation into
`RaynaudFundamentalCycleParameters` (derive complementary products for the
chosen finite-cycle coefficients), `RaynaudFundamentalScalingUnits`
(derive and prove units for the actual cycle scalings), and
`RaynaudScalarModelIso` (use generation to prove the coordinate map
bijective). The transfer to extrema follows separately; every cap is 150.

The final C5v1 extremal application is split into `RaynaudIdentifiedScalarIso`
(transport the actual scalar structures through prescribed generic
identifications) and `RaynaudExtremalScalarIso` (construct and identify the
two extrema). Each file remains capped at 150 lines.

A further ≤150-line C5v1 consequence, `RaynaudRankOneScalarExtension`,
uses the actual sandwich maximum → original → minimum to identify the
original model with its maximum. It extends prescribed generic maps out
of any rank-one finite-field scalar model without assuming integral scalar
lifts on that original model. This does not replace C5v2 for arbitrary
p-torsion point modules.

## Earlier W16 checkpoint: C5v2 proof obligations

The C5v1 rank-one theorem cannot be applied directly to arbitrary p-torsion
models. Before further implementation, split each obligation below into
≤150-line modules (and refine again if needed):

1. Descend each simple point-space factor and its action through a finite
   Galois level over the relevant strict-Henselian fraction field. The
   existing `WildInertiaProP` endpoints are for local inertia at a number-field
   completion; that identification/transport is an obligation here.
2. Use normal p-group invariants and the finite tame cyclic quotient to
   construct a finite scalar field commuting with Galois and prove point
   rank one over it. Do not install that rank as an input for arbitrary
   simple factors.
3. Construct compatible simple-factor closures and contracted quotient
   models inside both actual ambient models. `RaynaudFlatQuotient` gives
   base-flat quotient coordinates and generic surjectivity; it explicitly
   does not assert faithful flatness over the quotient coordinate ring.
4. Prove the required integral quotient/kernel exactness and middle-map
   isomorphism lemma. The order-three/unramified specializations in
   `RaynaudUnramifiedQuotient` do not supply the general statement.
5. Induct on the actual finite point cardinality, retaining prescribed maps
   through the closure/quotient comparisons, then carry C5v3 through the
   existing integral-coordinate/graph-extension endpoint.

These are outstanding proof obligations, not model assumptions or a request
for approval. The family admission and the wider post-C5 obligations remain.

## Earlier W16 verified completion boundary (04:43 UTC)

Checked 2026-10-03 04:43 UTC. This supersedes the earlier open labels for
C5p3e, C5p4 and the rank-one scalar C5v1 route. The broader C5c obligation
is still open pending C5v2/C5v3.

- C5p3e: mixed digit constants have residue the product of digit factorials;
  both actual original and dual mixed-monomial coefficients are units.
  The q−1 total-weight endpoint is included.
- C5p4: all character generators and then the full coordinate ring are
  generated by the actual fundamental coordinates. The finite cyclic
  polynomial quotient is isomorphic to that ring, with each quotient
  variable sent to its constructed coordinate. The quotient's freeness
  or presentation is never an input; bounded monomial spanning and the
  actual target rank prove the isomorphism.
- C5v1: actual coordinate pullback gives nonzero integral scalings. The
  exact chosen coefficients have complementary p-times-unit products;
  the DVR calculation and `scaling_eq_zero_of_small_ramification` prove
  the scalings are units. Generation proves the integral map bijective.
  `exists_extremal_scalar_iso` constructs and identifies both extrema;
  `extend_from_rank_one_scalar_model` uses their sandwich through the
  original model to extend each prescribed generic map out of it.

There are 31 new modules, all ≤150 lines; all have successful foreground
`LEAN_NUM_THREADS=2 lake build FLT.GroupScheme.MODULE` and individual
`LEAN_NUM_THREADS=2 lake exe runLinter FLT.GroupScheme.MODULE` checks.
The three W16 axiom-audit scripts outside `FLT/` check all 100 definitions
and theorems against exactly `propext`, `Classical.choice`, `Quot.sound`.
`W16_LOCAL_CHECK.lean` checks the mixed base-three q−1 boundary and applies
the prescribed extension theorem over an unramified strict-Henselian DVR
with its fraction ring. `python3 W16_FINAL_CHECKS.py` reruns artifact,
line-cap, scope, import-order and admission checks.

**At this earlier checkpoint C5v2 and C5v3 were not proved.** In particular no finite-field rank-one
structure is inferred for an arbitrary p-torsion point module. The source
check `rg -n 'mem_isCompatible|sorry' FLT/GaloisRepresentation/HardlyRamified/Family.lean`
still reports the original admission at line 68. No removal of `sorryAx`
from that theorem or from `PNat.pow_add_pow_ne_pow` is claimed.

## C5v2a scalar-field construction refinement

Before implementation, split the algebraic simple-factor step into these
≤150-line leaves:

- `RaynaudSimpleEndomorphismField`: Schur's endomorphism division ring of
  an actual finite simple module is a finite field; commuting scalar actions
  imply that the module has rank one over this field.
- `RaynaudSimpleScalarField`: transport that field action to an actual
  irreducible representation of a commutative group, proving its
  characteristic, rank, and commutation with the original action.
- `RaynaudCommutativeImageScalars`: apply the construction to a representation
  whose actual automorphism image is commutative, without assuming a scalar
  field or its rank as input.

These algebraic leaves do not assert that arbitrary local simple factors
have commutative image. Finite-level descent, wild/tame transport, and integral
quotient exactness remain separate obligations.

The C5v2a arithmetic connection is further split before implementation:
`RaynaudTameQuotientScalars` kills a normal p-group on an actual simple
representation, then derives commuting image through a commutative quotient;
`RaynaudFiniteInertiaScalars` applies this to the proved first-ramification
p-group and finite tame character of a faithful finite DVR action. Each cap
is 150 lines. The fraction-field/infinite-inertia transport remains open.

Before implementation, refine the absolute-inertia passage into
`RaynaudAbsoluteTameCommutativity` (prove the actual inertia/wild-inertia
quotient commutative by checking finite tame characters) and
`RaynaudInertiaSimpleScalars` (use the proved pro-p image result to derive
rank-one scalars for every continuous simple finite local-inertia
representation). Both caps are 150. These statements concern local inertia
of number-field completions; identifying it with the relevant
strict-Henselian fraction-field Galois group is still required.

`RaynaudSimpleCommutingExtension` (cap 150) connects the constructed field
to C5v1: every prescribed generic map out of an actual model with a simple
commuting generic action extends. Its inputs are the representation and
its equality with the model's actual action; scalar fields, scalar rank,
and integral scalar lifts are all derived. The commuting-image hypothesis
must still be supplied by the arithmetic transport for the chosen base.

`RaynaudInertiaFactorDescent` (cap 150) uses the existing actual
`InertiaDescent.subquotient_model`: construct the finite scalar field on a
simple inertia subquotient, then descend its commuting scalar endomorphisms
with its finite-flat model. This avoids assuming a new scalar rank during
descent. Subsequent strict-Henselian base change must retain this action;
general integral exactness is still not established.

## C5v2 exactness correction and general layer split

The earlier remaining-work note overlooked existing general results:
`IntegralQuotientFaithfullyFlat` proves relative faithful flatness and kernel
exactness for contracted quotients over a PID, using `FiniteHopfFreeness`.
These modules predate W16. Audit their dependency axioms before applying them.
The order-three middle-map code therefore needs generalization, not a new
Hopf-subalgebra freeness proof.

Before implementation, `RaynaudGeneralLayerDescent` (cap 150) generalizes
`RaynaudLayerDescent` to arbitrary PID fraction fields, using the actual
kernel closure, quotient, and comparison maps. Subgroup and quotient
isomorphisms are induction hypotheses; no model assumes middle-map rigidity.

The generic scalar-filtration dévissage is split before implementation into
`RaynaudScalarFiltration` (actual exact generic sequences with finite-field
rank-one quotient factors, and transport through a prescribed generic
isomorphism), `RaynaudScalarFilteredRigidity` (induction using general integral
kernel/quotient comparison), and `RaynaudScalarFilteredExtension` (the graph
projection extends each prescribed map). Caps are 150 each. The filtration
is a generic representation hypothesis whose construction from the descended
inertia composition factors is a separate obligation, not a model field
asserting extension or integral presentations.

Split out `RaynaudScalarQuotientComparison` (cap 150) before implementing
the induction: rank-one extension supplies the inverse to the actual
contracted-quotient comparison when both quotients retain the same prescribed
point group. This keeps the induction module under its cap.

The remaining filtration construction is split before implementation into
`RaynaudSimpleRepresentationQuotient` (maximal proper invariant subspaces
have simple quotients), `RaynaudRepresentationContinuity` (continuity of the
finite quotient and restricted actions), `RaynaudCompatibleSubquotients`
(actual subgroup/quotient models for an action agreeing with inertia), and
`RaynaudInertiaScalarFiltration` (cardinality induction using the derived
simple-factor scalar fields). Caps are 150; refine again before exceeding
one. These leaves must construct the filtration, rather than add it as a
hypothesis to the unrestricted extension theorem.

Split `RaynaudAgreedPointAction` (cap 150) out before the compatible-model
construction: derive the prime-field-linear Galois action from the actual
additive point action, and transfer an inertia-stable subrepresentation to
that action using the proved pointwise agreement.

`RaynaudInertiaCompatibleExtension` (cap 150) applies the constructed
filtration and integral dévissage to extend every prescribed generic map
from a model whose actual Galois action agrees with continuous local inertia.
No scalar field, rank, filtration, or presentation is an input. Establishing
this action agreement for the chosen strict-Henselian base change, and
returning to the original integral base, are the remaining assembly steps.

For the remaining base-change assembly, split before implementation:
`RaynaudScalarFiltrationBaseChange` (cap 150) preserves the constructed
filtration under the actual restricted scalar-extension models. This lets
one construct the filtration over the finite unramified descent field
and then pass to the strict-Henselian tower without redoing the inertia
comparison at every stage. The descent-field action comparison and faithful
flat descent back to the initial ring need separate leaves.

Split `RaynaudDescentActionAgreement` (cap 150) before implementation:
normality of the finite descent field forces the chosen absolute-Galois
restriction map into its fixing subgroup, even though the chosen closure
embedding need not fix the given copy of that field. This proves actual
point-action agreement with inertia on the restricted scalar extension.
`RaynaudDescentScalarFiltration` (cap 150) then constructs the filtration
on that actual model, with continuity inherited from its original points.

The faithful descent assembly is split before implementation into
`RaynaudScalarExtensionRigidity` (generic bijectivity survives actual scalar
extension; faithful flatness descends surjectivity of model maps),
`RaynaudUnramifiedOrder` (a preserved uniformizer preserves natural order),
and `RaynaudHenselianScalarRigidity` (construct the strict-Henselian tower and
descend integral rigidity for the constructed scalar filtration). Each cap
is 150; further prescribed-map and local-inertia assembly remains separate.

`RaynaudLocalInertiaRigidity` (cap 150) will combine the actual finite
unramified descent filtration with Henselian rigidity, then reflect
surjectivity back to the original completion ring. Its only representation
input is a prime-field module structure on the original points.
`RaynaudLocalPrescribedExtension` (cap 150) will apply this to the actual
graph closure and recover integral coordinates and the prescribed generic map.

After the p-killed local case, split `RaynaudLocalPowerRigidity` (cap 150)
before implementation: exponent induction uses the actual flat p-torsion
closure and the image of multiplication by p, with the existing general
kernel/quotient comparison. `RaynaudLocalPowerExtension` (cap 150) then
extends every prescribed map from a p-power-killed local model and proves
integrality in its original coordinate ring.

The general local endpoint explicitly assumes adic completeness of the
completion integers until that topological bridge is formalized in general.
The rational place already has `rationalCompletionIntegers_adicComplete`.
Split `RaynaudPadicPowerRigidity` (cap 150) to transport the original p-adic
model along the actual integral-ring equivalence and its fraction-field
lift, apply the rational-place theorem, and descend surjectivity.
`RaynaudPadicPowerExtension` (cap 150) recovers the prescribed map over the
original p-adic integers. This endpoint has no completeness or filtration
hypothesis beyond those derived from the standard p-adic ring.

Split `RaynaudPowerDevissage` (cap 150) out of the local power proof before
implementation. It isolates the exponent induction over a PID fraction field
from the dependent local-completion types. The local theorem supplies the
already proved p-killed rigidity theorem; no model or final endpoint assumes
rigidity, a filtration, or a presentation as input.

Split `RaynaudPowerPrescribedExtension` (cap 150) before extracting the
graph proof: the generic PID argument converts proved p-power rigidity into
the unique prescribed extension and integral coordinate pullbacks. Local
and p-adic endpoints supply their derived rigidity theorems explicitly,
avoiding repeated elaboration of graph closures over completion type aliases.

## W16 final C5 completion checkpoint

Checked 2026-10-03 06:58 UTC with `python3 W16_FINAL_CHECKS.py`, the per-module
foreground build/lint logs, and the eight W16 axiom-audit logs outside `FLT/`.
This supersedes the earlier W16 remaining-work paragraphs above.

C5p3e, C5p4, C5v1, C5v2 and C5v3 now give
`ThreeAdicPlan.extend_from_padic_power` in `RaynaudPadicPowerExtension`:
for every prime `p > 2`, actual models `X Y : FF ℤ_[p] ℚ_[p]`, a source
`KilledByPowerOf p X`, and a prescribed generic map `f`, there is a unique
integral model morphism whose generic map is `f`.
`GenericGaloisHom.integral_of_padic_power` proves the corresponding pullback
of each coordinate lies in the original source coordinate ring.

The finite scalar fields and rank-one factors are derived from actual simple
inertia modules. Normality proves agreement for the actual chosen closure
embedding; coatom quotients construct the finite scalar filtration. General
integral kernel/quotient exactness proves dévissage. The constructed
strict-Henselian tower and finite unramified descent preserve the valuation
bound; faithful flatness returns rigidity to the original ring. Exponent
induction and the graph construction handle every p-power-killed source.
The generic induction/graph helpers receive the arithmetic rigidity theorems
as proved arguments. The final p-adic endpoints assume no scalar fields,
filtrations, eigenspaces, presentations, or extension conclusions.

All 65 new modules are at most 106 lines (cap 150), with successful individual
builds and lints. All 159 new named declarations, plus two reused exactness
endpoints, have dependency axioms contained in `{propext, Classical.choice,
Quot.sound}`. `W16_POWER_CHECK.lean` checks the original three-adic prescribed
extension and integral-coordinate statements directly.

The general local-number-field version retains an explicit adic-completeness
instance. The p-adic endpoint derives it through the actual rational-place
comparison. Downstream spectrum/family integration is not completed here:
`rg -n 'mem_isCompatible|sorry' FLT/GaloisRepresentation/HardlyRamified/Family.lean`
still reports the original admission at line 68. No admission-free claim is
made for that theorem or `PNat.pow_add_pow_ne_pow`.

## W18 D9c implementation refinement

Before implementation, split D9c into the following whole-file caps of 150:
`RaynaudTowerClosure` extends the prescribed fraction embedding;
`RaynaudUnramifiedHom` proves residue uniqueness for finite unramified DVR maps;
`RaynaudTowerInertia` applies it to each actual stage and its directed union;
`RaynaudTowerAction` conjugates original inertia through the prescribed closure
equivalence; `RaynaudTowerPointCharacter` transports actual coordinate equations
and applies the integral-coefficient root-character theorem. Further split
evaluation/action comparisons if needed before exceeding any cap.

D9c3 is further separated into `RaynaudTowerEvaluation` (equivariance of
actual coordinate functions), `RaynaudTowerRootCharacter` (transport of
integral-coefficient equations), `RaynaudTowerPointCharacter` (actual one-
and two-cycle equations with common digits for all original inertia), and
`RaynaudOriginalTowerAction` (the actual union action, deriving fixedness).
The compatible-residue part of D10 is `RaynaudTowerResidue`: construct the
integral embedding, prove locality, and induce the residue-field embedding.
Each has a whole-file cap of 150 lines.

Before scalar-character identification, split out `RaynaudScalarCoordinateRatio`
(cap 150): if the actual transported automorphism sends a nonzero point to
`u • x`, derive its coordinate ratio from the proved scalar-evaluation law,
then identify its residue with the compatible scalar-field embedding. This
is an evaluation lemma; constructing the original factor and its comparison
is still required for the unconditional D10/D11 wrapper.

`RaynaudScalarCharacterBridge` (cap 150) is the next D10 comparison leaf:
reduce the actual scalar-coordinate ratio through `towerResidueMap` and
identify it with the original integral ratio. It must not assume a tame
character formula; its scalar-action equality is an explicit comparison
input to be derived when assembling the original descended factor.

`RaynaudTowerScalarWeights` (cap 150) combines the actual point root equations
with the compatible scalar-ratio comparison. Its output computes every
actual scalar action, with common binary digits and the original root
character. The scalar action is identified on a nonzero point; it is not a
supplied inertia-character formula. Original-factor construction/transport
must precede using this local endpoint in the unconditional spectrum theorem.


## W19 D10 implementation split (whole-file cap 150)

The original-factor transport is split before implementation into:

1. `HopfPointsClosureChange`: postcomposition of the actual convolution points
   and conjugation equivariance.
2. `FiniteFlatClosureChange`: retain the prescribed point group and coefficient
   module while transporting the actual finite-flat Hopf witness.
3. `RaynaudDescentStage`: prove the actual descent integers formally unramified,
   embed their image as an original unramified stage, and map into its union.
4. `FiniteFlatTowerClosure`: combine same-closure base change and the prescribed
   closure equivalence, retaining the exact original automorphism action.
5. Original descended factor comparison and maximal scalar model transport;
   split further before any file exceeds 150 lines.

D11/D12 and D13/D14 remain dependent on the original-factor assembly.

The D10 leaves are further split before assembly (each whole-file cap 150):
`RaynaudDescentFraction` extends the actual integral embedding;
`FiniteFlatPrescribedClosure` handles an arbitrary prescribed closure comparison;
`RaynaudOriginalFactorTransport` constructs tower actions on actual descended
factors and proves agreement with each original inertia element;
`RaynaudMaximalScalarModel` constructs maximal scalar lifts from finite flatness;
`RaynaudSimpleFactorTower` assembles the derived simple scalar field and transport.

`RaynaudSimpleFactorMaximal` (cap 150) combines the derived tower factor with
its maximal scalar model. `RankOneScalarCharacter` (cap 150) derives the unit
character of a commuting rank-one action for the local-weight assembly.

`RaynaudSimpleFactorCharacter` (cap 150) derives the character and identifies
its action on both the original factor and the maximal model.
`RaynaudOriginalOneWeight` and `RaynaudOriginalTwoWeight` (each cap 150) apply
the existing local weights after constructing all scalar-model inputs.

D11's algebraic bridge is split into `ScalarActionCharpoly` (cap 150):
transport the actual scalar operator to multiplication on its rank-one scalar
field, then apply Cayley–Hamilton and Frobenius to the prime-field charpoly.

`RaynaudOriginalFactorCharpoly` (cap 150) consumes the constructed original
one-/two-factor weights and returns their actual prime-field charpolys,
including the Frobenius-fixed quadratic case.
