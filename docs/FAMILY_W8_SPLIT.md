# FAMILY-W8 — finite-flat inertia spectrum and the family boundary

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

### S4 — BLOCKED, cap 400: integral unit correction and character evaluation
Future module `RaynaudCoordinateCharacter`. [R] §3.4(9); use lifts F1–F5.
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
constructs this correction for ζ−1. Blocked on the source-to-coordinate and
unramified-base transports; not on S1–S3's elementary algebra. The cap covers
this bridge after those transports, not their construction.

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
axioms; module is 57/180 lines. S1 is implemented (READY above records dispatch).
