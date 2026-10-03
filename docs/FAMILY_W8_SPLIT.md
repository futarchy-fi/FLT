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
