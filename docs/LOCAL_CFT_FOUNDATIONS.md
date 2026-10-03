# E1c7: local reciprocity and the local invariant

Source/API check: 2026-10-03, FLT base `4bb55369`, Mathlib
`c32e1ec0d1eb5237ba344eee50162f45d5b0fc76`. This is a foundational program,
not a claim that local class field theory fits in a 200-line adapter.
Each proposed module below has a **200-line hard cap**. Blocked contracts
are design sketches, not elaborated declarations or certified size estimates;
split again before implementation if a proof exceeds the cap. No missing
theorem may become a structure field, parameter standing for E1c7, or axiom.

Latest accepted scope: see the **W23 proved scope** section below and the
W23 table in `LIFTS_GOAL_LEDGER.md`. Earlier wave sections record historical
state; W23 proves the unramified continuous comparison that W22 left open.

## W23 proved scope — 2026-10-03T08:37:58.585982+00:00

Checked 2026-10-03T08:37:58.585982+00:00; branch `task/goal-lifts-w23`; base `3b918b73`.
**E1c7/E1d remain blocked; the final FLT theorem still depends on sorryAx.**

19 new modules; **1421 Lean lines, 90 named declarations**. Every module is at most
200 lines. All changes are local commits; nothing pushed.

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

## Source match and conventions

J.S. Milne, [Class Field Theory, v4.03 (2020)](https://www.jmilne.org/math/CourseNotes/CFT.pdf).
Printed page numbers below are PDF page numbers minus nine. Download and
page-labelled extraction: `Scratch/LiftsW15/MilneCFT.{pdf,txt}` (untracked).

* I, Theorem 1.1, p.20: `rec_K : Kˣ → Gal(Kab/K)` sends a uniformizer
  to **arithmetic** Frobenius on every finite unramified extension; residue
  action is `x ↦ x^q`. It induces `Kˣ/N(Lˣ) ≃ Gal(L/K)` for finite abelian L/K.
* I, 1.8, p.23: a unit acts trivially on Kun, since both π and πu are
  uniformizers. I, 1.10–1.11, pp.23–24: completion replaces the valuation's
  Z by Z-hat and leaves compact units intact. Hence rec maps units onto the
  **image of inertia in the abelian quotient**, `Gal(Kab/Kun)`. Do not
  identify this group with the full nonabelian inertia subgroup of G_K.
  Inclusion suffices for the forward annihilator argument; equality needs
  the completion/surjectivity argument and is a separate leaf.
* III, 1.2–1.6, pp.98–99: norm surjectivity on unramified units uses residue
  norm, successive principal-unit quotients, residue trace, and completeness.
  Their higher cohomology vanishes. This is missing arithmetic, not a
  consequence of merely having a local-field typeclass.
* III, §1, pp.99–100, Theorem 1.7: the unramified invariant is the composite
  `H²(G,Lˣ) --ord--> H²(G,Z) --δ⁻¹--> Hom_cont(G,Q/Z) --eval(Frob)--> Q/Z`.
  Here `δ` comes from `0 → Z → Q → Q/Z → 0`, with differential
  `db(g,h) = g • b(h) - b(gh) + b(g)`. The finite degree-n fundamental class
  has invariant `+1/n mod Z`. III, pp.101–102 computes its carry cocycle:
  `c(Frob^i,Frob^j) = π^(if n ≤ i+j then 1 else 0)`, for `0 ≤ i,j < n`.
* III, 1.8 and 2.1, pp.100,103–105: restriction multiplies the invariant
  by `[L:K]`; inflation from Kun to the separable closure is an isomorphism.
  The general local invariant is obtained by **inverting this proved
  inflation isomorphism**. A cyclic carry formula alone does not construct it.
* III, 3.1,3.4,3.6–3.7, pp.107–110: Tate's class-formation theorem constructs
  the finite Artin maps; evaluation is `χ(rec_K(a)) = inv_K(a ∪ δχ)`.
  The proof printed for tower compatibility 3.3 has an explicit caveat in
  footnote 3: use 3.6, not an unchecked appeal to (33). The proof of 3.6 is
  referred to Serre, *Local Fields*, Ch.XI, appendix; it is not supplied by
  a Mathlib declaration. It remains a proof obligation below.
* III, §4 Step 2–3, p.112 and Proposition 4.3, p.113: for n invertible in K,
  Kummer and Hilbert 90 identify `H²(K,μ_n)` with the n-torsion of
  `H²(K,Ksepˣ)`. Under `j_n : Z/n → Q/Z`, `j_n(t)=t/n`,
  `inv_K(χ ∪ κ(a)) = j_n(χ(rec_K(a)))`.
  No assumption that K contains μ_n is needed for this particular pairing.
  Full finite-module Tate duality (Remark 4.6, p.114) is stronger than E1d
  needs; invariant injectivity and this evaluation formula suffice here.

**Sign contract.** W14's cup is `κ(a)(g) • χ(h)` in additive notation,
namely `χ(h) • c(g)`. The opposite cup is `χ(g) • (g • c(h))`.
For `b(g)=χ(g) • c(g)`, `db = -(cup + oppositeCup)`. Therefore the W14
order has invariant **`-j_p(χ(rec_K(a)))`** with the above arithmetic
Frobenius/positive-invariant conventions. Vanishing is unaffected, but the
minus sign must not be dropped from a claimed evaluation theorem.
The formal cochain identity is a ready leaf; the arithmetic identification
is not. Reversing Frobenius without changing the other conventions is invalid.

## Checkout audit: reusable API versus missing theorems

Reproduce with `rg -n -i 'reciprocity|artin|brauer|local.{0,15}duality|invariant'
FLT .lake/packages/mathlib/Mathlib`, and inspect the files below. The broad
search has irrelevant linear-algebra, quadratic-reciprocity and invariant
subspace hits. The saved inventory is `Scratch/LiftsW15/api-audit.log`.

| API | What is actually available |
|---|---|
| `Mathlib/NumberTheory/LocalField/Basic.lean` | DVR, complete/compact integers, finite residue field, discrete value group; no Artin map |
| `Mathlib/Algebra/BrauerGroup/Defs.lean` | quotient of CSA by matrix equivalence; even abelian group structure and functoriality are TODOs |
| `GroupCohomology/Hilbert90.lean` | genuine H¹ Hilbert 90 and cyclic norm-one theorem |
| `GroupCohomology/FiniteCyclic.lean` | odd/even positive-degree cohomology via periodic complex and explicit quotient maps |
| `TateCohomology/Basic.lean` | Tate complex, degree comparisons and long exact sequence; not the class-formation isomorphism of Milne II.3.11 |
| `GroupCohomology/LongExactSequence.lean` | connecting maps, including cochain formulas `δ₁_apply`; abstract/discrete theory |
| `ContCohomology/{Basic,Functoriality,LowDegree,Sha}.lean` | continuous complex and functoriality; no local invariant or arithmetic duality |
| FLT `ContCohomology/CupProduct` and W14 modules | actual cup, H¹ quotient equivalence, H² representatives and zero criterion |
| `FLT/GroupScheme/{KummerUnitClass,LinearKummerClass}.lean` | Kummer quotient, independent unit subgroup, valuation-power criterion, H¹ comparison |
| `FLT/PoitouTate.lean` | a supplied pairing/order formula, not a proof of local duality |
| `FLT/CyclicBaseChange/Statements.lean` | supplied Frobenius data, Artin construction explicitly deferred |
| `FLT/FreyCurve/Serre/AtP.lean` | inertia-fixed torsion functional, not an H² invariant |

We use the cohomological route, which does not require constructing the
CSA Brauer group. It still requires a real invariant on the existing
continuous complex with discrete Ksepˣ coefficients. In particular, W14's
field-linear coefficient interface is not by itself a Z-linear Ksepˣ interface.
S01 uses `AddCircle (1 : ℚ)` only as an additive group. Its inherited
quotient topology is **not** the discrete coefficient topology needed here;
C07 must explicitly use discrete coefficients and prove the continuous
boundary comparison. There is no continuity assertion in S01.

## Dependency split committed before implementation

All module names in the table are under `FLT/LocalClassFieldTheory/`, except
S03 (`FLT/GaloisRepresentation/Extensions/ContinuousCupSwap`). `Hc`, `Hd`,
`U`, `Unr`, `inv`, `rec`, `δ`, `Inf`, and `Res` below are **sketch notation**,
not invented existing Lean identifiers. Every `≃+` must be constructed with
its stated computation rule proved. All rows have cap 200.

S01–S03 and, after the refinement below, V01–V02 are certified ready in this wave.
Other rows are BLOCKED on
the dependencies listed and/or the named unresolved implementation bridge.
Absence of a dependency edge does not certify API readiness. No general
class-field theorem is counted as completed by proving an abstract adapter.

| ID / module | Lean-shaped contract / proof sketch | Dependencies / gate |
|---|---|---|
| S01 / RationalTorsion | `zmodToRatCircle : ZMod n →+ AddCircle (1:ℚ)`; `map_intCast`, injectivity, range = `{x | n • x = 0}`. Descend `z ↦ z/n`; clear denominators. | READY: `ZMod.lift`, quotient group, rational arithmetic |
| S02 / CyclicCarry | `carry : ZMod n → ZMod n → ℤ`; `carry_cast = j.val/n - (i+j).val/n + i.val/n`; cocycle equation and zero normalization. | READY after S01; `ZMod.val_add`, arithmetic |
| S03 / ContinuousCupSwap | Construct opposite continuous cup and `b(g)=d(g) • c(g)`; prove `db=-(cup+opposite)`, and equivalence of coboundary conditions. | READY: W14/E1b continuous cochains |
| V01 / NormalizedOrder | `ord : Kˣ →* Multiplicative ℤ`; surjectivity, kernel = valuation-ring units; a chosen element has order +1. | READY after API refinement below |
| V02 / PowerClassOrder | `PowerClass K n →* Multiplicative (ZMod n)` with representative formula and kernel = `unitClasses A n`. | READY after V01; existing `isUnitClass_iff` |
| U01 / ResidueExtension | finite unramified L/K: construct `Gal(L/K) ≃* Gal(l/k)` from reduction; prove bijectivity. | BLOCKED: finite étale/residue equivalence and lifting automorphisms must be source-matched, not assumed |
| U02 / Frobenius | finite unramified L/K: construct `Frob`, prove residue q-power formula and generator property. | U01; finite-field Galois API |
| U03 / UnramifiedTower | compatible Frobenius elements and residue degrees in towers; construct finite unramified extensions of each degree. | U01/U02; BLOCKED existence/lifting polynomial bridge |
| U04 / MaximalUnramified | construct Kun as supremum; its Galois group = inverse limit of U03; inertia is restriction kernel. | U03; BLOCKED topology/infinite Galois comparison |
| U05 / UnramifiedCharacters | construct continuous `χ_p : G_K →+ ZMod p`, χ_p(Frob)=1, all inertia-trivial characters factor through unramified quotient. | U04 |
| N01 / UnitFiltration | `Uᵐ/Uᵐ⁺¹ ≃+ l` for m>0; residue units quotient `U/U¹ ≃* lˣ`. | U01; BLOCKED principal-unit quotient/action bridge, Milne III.1.3 |
| N02 / NormOnGradedUnits | norm on residue units is finite-field norm; norm on Uᵐ/Uᵐ⁺¹ is trace. | N01; finite product expansion, III.1.2 proof |
| N03 / SuccessiveNormLifts | for u∈U_K construct v_m with norm discrepancy in U_K^(m+1). | N02; finite-field norm/trace surjectivity |
| N04 / CompleteNormLifts | prove products of v_m converge and their norm equals u; conclude unramified unit norm surjectivity. | N03; norm continuity and local completeness |
| C01 / IntegralLowDegree | degree-one/two explicit continuous complex comparison over Z for `Additive Lˣ`, with representative/differential formulas. | BLOCKED: generalize comparison in new modules from W14 field-linear setup; split degrees separately if needed |
| C02 / FiniteContinuous | `Hc i G M ≃+ Hd i G M` for finite discrete G, with cup and δ compatibility. | C01; BLOCKED comparison of complex presentations |
| C03 / CyclicUnitsCohomology | finite unramified `Hd i G U_L = 0` for i>0 using norm-surjectivity/Hilbert 90 and periodic complex. | N04, C02; finite cyclic positive-degree API |
| C04 / ContinuousFiniteDescent | each continuous cocycle on profinite G/discrete M descends to a finite quotient with invariant values; coboundary descent. | BLOCKED: compactness/open-normal refinement with actions, not just finite image |
| C05 / CohomologyColimit | build cohomology isomorphism with filtered colimit of finite-stage cohomology. | C04; exact filtered colimits/quotient comparison |
| C06 / RationalAcyclic | positive finite-group rational cohomology vanishes by averaging; pass to continuous via C05. | C05; BLOCKED explicit averaging homotopy compatibility |
| C07 / IntegralBoundary | `Hc 1 G (ℚ/ℤ) ≃+ Hc 2 G ℤ`, with boundary carry formula S02. | C06, S01/S02; continuous exact-sequence comparison |
| C08 / UnramifiedOrderH2 | order induces `Hc 2 G Lˣ ≃+ Hc 2 G ℤ` for unramified L/K. | C03/C05; continuous exact sequence, V01 |
| I01 / FiniteInvariant | finite unramified `Hc 2 G Lˣ ≃+ (ℚ/ℤ)[n]`; inverse sends 1/n to π^carry. | C07/C08,U02,S01/S02 |
| I02 / UnramifiedInvariant | `Hc 2 Gal(Kun/K) Kunˣ ≃+ ℚ/ℤ`; inflation compatibility, restriction multiplies by degree. | I01,C05,U03/U04; III.1.7–1.8 |
| R01 / InflationKernel | injectivity of H² inflation and exactness at H² for a tower using Hilbert 90. | C01/C05; BLOCKED continuous inflation-restriction bridge, III.2 opening |
| R02 / RelativeLowerBound | finite Galois L/K: relative H² contains cyclic subgroup of order [L:K] via unramified base change. | R01,I02; III.2.2 |
| R03 / DeepUnitsLinear | a sufficiently deep principal-unit subgroup of finite L/K has a normal-basis lattice comparison. | BLOCKED: local analytic/lattice argument, III.2.3–2.4; source-match and subdivide before coding |
| R04 / CyclicHerbrand | multiplicativity of Herbrand quotient and h(Lˣ)=[L:K] for cyclic L/K. | R03; BLOCKED finite-kernel/cokernel Euler characteristic API, III.2.5 |
| R05 / RelativeOrder | prove finite H² order = [L:K] by cyclic case and induction on solvable local Galois group. | R01/R02/R04; BLOCKED local Galois solvability bridge, III.2.6 |
| R06 / UnramifiedInflation | `Inf : H²(Kun/K) → H²(Ksep/K)` is bijective by finite descent and R05. | R05,C05,I02; III.2.1 |
| I03 / LocalInvariant | construct `inv_K : Hc 2 G_K Ksepˣ ≃+ ℚ/ℤ`, restriction/corestriction and fundamental class formulas. | R06,I02; III.2.1,2.7; split functoriality if cap requires |
| T01 / TateDimensionShift | construct the two connecting isomorphisms from a splitting module of a 2-cocycle. | BLOCKED: class-formation proof II.3.11, beyond Tate complex/LES API |
| T02 / FundamentalCup | prove T01 equals cup with fundamental class and is iso in the needed degree -2. | T01,I03; BLOCKED negative Tate cup comparison |
| A01 / FiniteArtin | inverse of T02 gives `Kˣ/N(Lˣ) ≃* Gal(L/K)` for finite abelian L/K. | T02; III.3.1 |
| A02 / ArtinEvaluation | `χ(rec_LK a)=inv_K(a ∪ δχ)` by explicit cocycle/connecting computation. | A01,I03,C07; III.3.6 and Serre XI appendix; do not assume formula |
| A03 / ArtinTower | restriction compatibility proved by A02 and character separation. | A02; respects Milne's caveat on III.3.3 |
| A04 / LocalArtin | inverse-limit construction of `rec_K`, continuous and dense, with uniformizer/Frob formula. | A03,U04,I01; III.3.4,3.7 |
| A05 / UnitsInInertia | `rec_K(U_K) ≤ Gal(Kab/Kun)` by comparing π and πu. | A04,V01; I.1.8 |
| A06 / UnitsOntoInertia | equality using compactness of U_K, density and Z→Z-hat injectivity; finite quotient inertia images agree. | A04/A05,U04,V01; I.1.10–1.11; topology/completion bridge |
| K01 / KummerH2 | inclusion μ_p→Ksepˣ identifies actual H² with p-torsion, with representative formula. | C01/C05; continuous Kummer exact sequence and Hilbert 90, III.4 Step 2 |
| K02 / KummerCupBoundary | image of `χ ∪ κ(a)` equals `a ∪ δ(j_p χ)`; verify connecting-map signs. | K01,C07; cochain computation, III.4 Step 2 |
| K03 / LocalTateComparison | `inv_p(cup κ(a) χ) = -j_p(χ(rec_K a))`; `inv_p x=0 ↔ x=0`. | K02,I03,A02/A04,S03; E1c7 adapter |
| D01 / ExtensionKummer | independent E1b annihilator iff independent unit class: units killed by A05, converse detected by U05 and V02. | K03,A05,U05,V02; E1d1 |
| D02 / ScalarPairing | construct scalar extension of H² pairing and unramified characters; prove formulas on pure tensors. | D01; BLOCKED cohomology/base-change comparison, beyond existing E09c |
| D03 / ExtendedExtensionKummer | tensor/actual-Hom transport yields residual-field annihilator = extended unit subspace. | D02 and E09c; E1d2 |

Rows R03, R04, T01/T02 and U01–U04 are especially substantial missing
programs; their individual contracts are not ready proof jobs merely because
they have names and caps. Their named bridges must be decomposed further
against concrete APIs before dispatch. This prevents a fake 200-line wrapper
from silently assuming local CFT. S01–S03 are bounded implementation leaves
that can be validated now. E1c7, E1d1 and E1d2 remain BLOCKED.

### V01–V02 refinement (before implementation)

No new arithmetic hypothesis is required: take `A = (valuation K).valuationSubring`
for an actual `IsNonarchimedeanLocalField K`. Mathlib provides both
`valueGroupWithZeroIsoInt K` and `valuation_surjective`. Set
`ord(u) = -WithZero.log (valueGroupWithZeroIsoInt K (valuation K u))`.
The minus sign converts Mathlib's multiplicative uniformizer value exp(-1)
to classical order +1. `Valuation.mem_unitGroup_iff` and
`ValuationSubring.unitGroupMulEquiv` identify its zero kernel with the actual
valuation-ring units, without assuming that kernel in a record.

V01 constructs the homomorphism, proves surjectivity and its unit kernel,
and chooses an order-one element by surjectivity (cap 200).
V02 reduces ord modulo n, descends through `powerClassMap`, and proves its
kernel equals the already-defined `unitClasses`. For the reverse inclusion,
write ord(q)=n*m, choose b with ord(b)=m, and turn q/b^n into an actual
valuation-ring unit by V01. This works for arbitrary positive n, not just
prime n (cap 200). These are valuation facts, not Artin or Tate theorems.

The ramified-invariant route R03–R06 is restricted to characteristic zero,
as is Milne's proof of III.2.4 using exp/log. This suffices for the p-adic
application. An equal-characteristic version would need additional sources
and proofs; no such generality is asserted here.

### Expansion of the large blocked nodes

The following replaces the corresponding broad rows above by smaller leaf
contracts. A broad row is a dependency milestone, not an additional proof
leaf. **Every child has cap 200 and status BLOCKED**: none has an audited
complete dependency/API chain. Module suffixes are the child names below;
the contracts use the same explicitly hypothetical `Hc`/`Hd` notation.
The sketches specify individual outputs, not assumed class-field records.

| Parent / child | Lean-shaped output and proof step | Dependencies |
|---|---|---|
| U01 / ResidueAction | `reduction : Gal(L/K) →* Gal(l/k)` from preservation of the unique extended valuation | finite local extension valuation uniqueness; existing ramification/inertia API needs matching |
| U01 / ResidueActionKernel | `reduction.ker = inertia`; unramified means this kernel is bottom | ResidueAction; integral unramified criterion |
| U01 / ResidueActionSurjective | `Function.Surjective reduction` by lifting a residue primitive element's conjugates | ResidueAction; Hensel simple-root lifting and integral primitive presentation |
| U01 / ResidueGaloisEquiv | `Gal(L/K) ≃* Gal(l/k)` with actual reduction formula | ResidueActionKernel, ResidueActionSurjective |
| U03 / LiftResiduePolynomial | lift a degree-n irreducible finite-field polynomial to integral coefficients; separable reduction | finite-field extension/primitive-element API, coefficient lifts |
| U03 / UnramifiedRootField | adjoining a root of the lifted polynomial has residue degree n and ramification index one | LiftResiduePolynomial; integral basis and degree comparison |
| U03 / UnramifiedUniqueness | any two unramified degree-n subextensions of Ksep coincide | UnramifiedRootField, Hensel uniqueness |
| U03 / FrobeniusRestriction | `restrict Frob_EK = Frob_LK` by residue q-power and U01 injectivity | U02, UnramifiedUniqueness |
| U04 / UnramifiedUnion | define the supremum Kun, show each element belongs to a finite unramified stage | U03 and finite compositum residue compatibility |
| U04 / UnramifiedLimit | `Gal(Kun/K) ≃* inverseLimit (finiteUnramifiedGalois K)` with topological proof | UnramifiedUnion; Krull topology/inverse-limit comparison |
| U04 / InertiaKernel | restriction `G_K → Gal(Kun/K)` is surjective and its kernel is the existing inertia group | UnramifiedLimit, residue action on Ksep |
| C01 / IntegralOne | integral homogeneous/inhomogeneous degree-one mutually inverse maps | W14 coordinate formulas, continuous discrete abelian-group coefficients |
| C01 / IntegralTwo | degree-two maps and differential/cocycle formulas | IntegralOne; locally compact uncurrying |
| C01 / IntegralH2 | `explicitContinuousH2 ≃+ Hc 2 G M`, computation and zero criterion | IntegralTwo; kernel/cokernel quotient API |
| C02 / FiniteComplex | chain isomorphism from continuous to ordinary complex for finite discrete G | IntegralOne/IntegralTwo, finite discrete continuous maps |
| C02 / FiniteComparison | cohomology equivalence and explicit low-degree representative formulas | FiniteComplex |
| C02 / FiniteBoundaryCup | finite comparison commutes with δ and degree-(1,1) cup | FiniteComparison, connecting/cochain formulas |
| C04 / CochainFiniteImage | continuous cochains from compact G^r to discrete M have finite image | topology compact/discrete API; choose finite support of coefficient action |
| C04 / CochainOpenNormal | refine the stabilizers of those values and clopen fibers to one open normal subgroup | CochainFiniteImage; profinite open-normal basis |
| C04 / DescendedCochain | construct finite quotient cochain with invariant values and prove differential compatibility | CochainOpenNormal |
| C05 / ColimitCocycles | surjectivity from finite-stage cocycles onto continuous cocycles | DescendedCochain |
| C05 / ColimitBoundaries | equality in continuous cohomology is witnessed at a common finite stage | DescendedCochain applied to the bounding cochain |
| C05 / ContinuousColimit | descend to an additive equivalence, natural in restrictions and coefficient maps | ColimitCocycles, ColimitBoundaries |
| R03 / IntegralNormalLattice | construct G-stable integral lattice from a scaled normal basis, equivariant to induced O_K | normal basis; common denominators |
| R03 / NormalLatticeOpen | lattice contains a high power of the maximal ideal and is open | IntegralNormalLattice; finite-dimensional local topology |
| R03 / LocalExpDomain | convergence of exp and log on explicitly bounded local-field neighborhoods | characteristic zero, complete local field; p-adic series estimates |
| R03 / LocalExpInverse | exp/log inverse group equivalence on those neighborhoods | LocalExpDomain; power-series composition/product identities |
| R03 / LocalExpEquivariant | the equivalence commutes with Galois action | LocalExpInverse; continuity of action and rational coefficients |
| R03 / AcyclicOpenUnits | transport a small scaled normal lattice to an open unit subgroup with vanishing cohomology | NormalLatticeOpen, LocalExpEquivariant, Shapiro |
| R04 / HerbrandFinite | finite cyclic module has Herbrand quotient one, by counting kernel/image of norm and σ−1 | finite cyclic complex API |
| R04 / HerbrandExact | Herbrand quotient multiplicative in short exact sequences with finite cohomology | cyclic six-term exact sequence and finite cardinal arithmetic |
| R04 / UnitHerbrand | h(U_L)=1 via finite quotient by AcyclicOpenUnits | HerbrandFinite, HerbrandExact, compact/open quotient |
| R04 / FieldHerbrand | h(Lˣ)=[L:K] via the order exact sequence and trivial Z module | UnitHerbrand,V01; cyclic cohomology |
| R05 / CyclicRelativeOrder | `Nat.card (Hd 2 Gal(L/K) Lˣ) = [L:K]` for cyclic extensions | FieldHerbrand, Hilbert 90 |
| R05 / LocalGaloisSolvable | finite local Galois groups are solvable via wild inertia p-group, tame cyclic and residue cyclic quotients | existing ramification-filtration API must be connected; U01 |
| R05 / RelativeOrderInduction | order ≤ degree by proper normal subgroup and inflation-restriction; combine with R02 | LocalGaloisSolvable,CyclicRelativeOrder,R01/R02 |
| I03 / AbsoluteInvariant | compose I02 with inverse of R06 to construct `inv_K` | R06,I02 |
| I03 / InvariantRestriction | `inv_L (Res x) = [L:K] • inv_K x` | AbsoluteInvariant; I02 restriction and finite descent |
| I03 / FundamentalClasses | inverse image of 1/[L:K], prove restriction and inflation formulas | InvariantRestriction,R01,S01 |
| T01 / SplittingModule | construct the extension module attached to an actual two-cocycle, verify the action | explicit cocycle identity, Milne II.3 proof |
| T01 / SplittingExact | short exact sequence from SplittingModule and augmentation ideal; compute connecting map | SplittingModule |
| T01 / SplittingAcyclic | prove needed cohomology vanishing by restriction to subgroups and the fundamental-class generator | SplittingExact,I03, Hilbert 90; class-formation argument |
| T02 / TateMinusTwo | identify degree −2 Tate cohomology of Z with abelianization, with generator formula | Tate/group-homology low-degree comparison |
| T02 / FundamentalShift | compose the two boundary isomorphisms at −2 and verify it is the fundamental-class shift | SplittingAcyclic,TateMinusTwo; negative-degree connecting maps |
| T02 / UnramifiedShiftValue | arithmetic Frobenius maps to the uniformizer class by the carry product computation | FundamentalShift,I01,S02; Milne III.1.9 |
| A06 / CompactUnitImage | image of U_K under rec_K is closed by compactness and Hausdorffness | A04/A05; local compact units |
| A06 / UnitImageDense | finite abelian quotients: every inertia element comes from a unit after removing a norm of suitable order | A01/A04,U01,V01; valuation-of-norm formula |
| A06 / UnitImageEquality | closed and dense image = inertia image; translate to `Gal(Kab/Kun)` | CompactUnitImage,UnitImageDense,U04 |
| K01 / ContinuousKummerExact | exact coefficient sequence μ_p→Ksepˣ→Ksepˣ with discrete continuous action | separable pth roots, char(K)≠p, C01/C05 |
| K01 / KummerH2Torsion | actual H² inclusion is injective with image killed by p | ContinuousKummerExact, continuous Hilbert 90 |
| D02 / ScalarH2 | finite-dimensional scalar extension commutes with cocycle/coboundary quotient | integral/field coefficient comparison, finite direct sums |
| D02 / ScalarUnramified | identify inertia-trivial dual characters after scalar extension | U05; finite direct sums and restriction kernel |
| D02 / ScalarCup | evaluation on pure tensors agrees with scalar extension of prime-field cup | ScalarH2,ScalarUnramified; actual cup formula |

Some prerequisite bridges in this table are still research obligations
(notably Hensel/finite étale comparison, local exp/log and class formation).
The sketches do not certify that these unimplemented proofs fit their caps.
They make the expected mathematical output and obstruction explicit so the
next worker can refine one bridge, rather than assume all of local CFT.

## Acceptance checks

For each implemented module M, sequentially run
`LEAN_NUM_THREADS=2 lake build M`, `LEAN_NUM_THREADS=2 lake exe runLinter M`,
and `#print axioms` for every new named declaration. Only propext,
Classical.choice, Quot.sound may occur. Builds stay in the foreground;
never run whole-library lint. Record actual line counts and local commits.
Audit the final theorem separately; support lemmas do not remove sorryAx.


## W16 residue comparison audit and refined execution order

Checked 2026-10-03 against the pinned checkout (read-only `rg` and direct
source inspection; inventory in `Scratch/LiftsW16/api-audit.log`). The W15
U01 and U03 gates were too broad: several arithmetic ingredients already
exist. The following refinement precedes implementation.

* `IsLocalRing.ResidueField.mapAlgEquiv'` reduces local algebra automorphisms.
  Ring automorphisms preserve the unique maximal ideal; valuation uniqueness
  is unnecessary for this integral-ring leaf.
* `Ideal.Quotient.stabilizerHom_surjective` in
  `Mathlib/RingTheory/Invariant/Basic.lean` proves residue surjectivity for
  finite invariant actions. In a local ring every automorphism stabilizes
  the maximal ideal. `Algebra.isInvariant_of_isGalois'` derives invariance
  for the full integral closure in a finite Galois fraction-field extension.
  Thus surjectivity need not be reproved by Hensel lifting.
* FLT `DiscreteValuationRing/ResidueGenerator.lean` constructs a power
  basis of a finite free DVR algebra with separable residue extension.
  FLT `Unramified/PowerBasis.lean` proves rigidity of its homomorphisms
  under formal unramifiedness using the unit derivative and Hensel uniqueness.
  This yields injectivity without assuming trivial inertia or a power basis.
* `galRestrict` and fraction-ring extension of algebra equivalences connect
  field automorphisms with integral automorphisms. These are the next
  interface to assemble, not hypotheses asserting residue bijectivity.
* FLT `Unramified/LocalRing.lean` already proves
  `exists_unramified_extension_of_residueField`: finite separable residue
  extensions lift to finite separable fraction-field extensions of equal
  degree with a DVR of integers. U03's polynomial/root-field construction
  is therefore available. Galois normality, placement inside the chosen
  separable closure, uniqueness there, and tower compatibility remain to
  be assembled; the existence theorem alone does not supply them.
* `ValuationSubring.inertiaSubgroup` is a kernel on a decomposition group;
  `Ideal.inertia` is the congruence subgroup on the integral ring. A theorem
  using either must identify its actual action and domain, not interchange
  the two definitions silently.

Refined leaves, each capped at 200 lines:

| ID | Output and proof | Readiness before implementation |
|---|---|---|
| U01a / ResidueAction | Bundle reduction of local algebra automorphisms, prove residue formula and kernel = ideal inertia | READY from residue functor and quotient equality |
| U01b / ResidueActionSurjective | Derive surjectivity for a finite invariant integral action using the existing stabilizer theorem | READY; field application must derive invariance |
| U01c / ResidueActionFaithful | Construct the integral power basis and prove reduction injective for finite free formally unramified DVR algebras with separable residue | READY from the two FLT lemmas above |
| U01d / ResidueGaloisEquiv | Combine a finite Galois fraction extension's integral closure restriction with U01a–c; prove the actual reduction formula | Next after U01a–c; resolve restriction equivalence and instances, do not assume bijectivity |
| U02a / Frobenius | Pull back finite residue q-power through U01d; prove uniqueness, order and generation | Next after U01d; `FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow` |
| U03a / FrobeniusTower | Prove restriction compatibility by the residue q-power formula and faithful reduction | Next after U02a; resolve integral tower action |
| U03b / UnramifiedRealization | Install the already constructed DVR extension in the chosen separable closure, prove normality and uniqueness | BLOCKED pending embeddings/normality and Henselian comparison |

The general `IsNonarchimedeanLocalField` frontend still needs its extended
valuation ring identified with the finite integral closure, finite/free
instances, and ramification-index-one converted to formal unramifiedness.
The integral theorem will state these standard ring hypotheses explicitly;
it is not yet the assertion that every pair of local-field instances has a
compatible unramified extension structure. U04/U05 and E1c7 remain blocked.

### W16 next prerequisite refinement

After U01a–d/U02a/U03a, the next audit found N01's residue-unit quotient
already fully implemented by
`ValuationSubring.unitsModPrincipalUnitsEquivResidueFieldUnits`, including
surjectivity and its representative formula. Reuse it; no duplicate module.
The higher principal-unit quotients in N01 remain separate work.

| ID / module | Ready output and proof, cap 200 | Boundary |
|---|---|---|
| N02a / ResidueNorm | Norm and trace commute with the actual residue maps for finite free formally unramified local algebras; transport the existing quotient theorems along equality of maximal ideals | No assertion about higher principal-unit quotients |
| N03a / ResidueNormLift | Every base unit has a unit whose norm agrees modulo the maximal ideal; finite-field norm surjectivity and surjective residue-unit map | First approximation only; successive approximation and convergence remain N03/N04 |
| C04a / CochainFiniteImage | A compact-domain continuous discrete cochain has finite image and finite action saturation; find one open normal subgroup fixing every value | Common refinement of the cochain's fibers, descent and differential compatibility remain C04b/c |

These contracts are refined before their implementation. The norm leaf
requires formal unramifiedness to identify the tensor/ideal quotient with the
actual residue field; it does not assert this identity for a ramified algebra.
The cochain leaf uses the compact/discrete image theorem and the profinite
open-normal neighborhood basis. Fixing values alone does not make a cochain
constant on quotient fibers, so it does not finish finite descent.

C04 refinement after the value-support leaf: the remaining fiber argument
can also be isolated without assuming descent. For a compact group H and a
discrete target, the bad translation set `{(g,x) | c(x*g) ≠ c(x)}` is closed;
its projection is closed because H is compact. Its complement is an open
identity neighborhood, hence contains an open normal subgroup. Apply this
to H=G^n, then intersect the inverse images along the finitely many coordinate
inclusions to obtain one subgroup of G. `Subgroup.pi_mem_of_mulSingle_mem`
handles noncommutative G. This gives ready `CochainOpenNormal` (cap 200).
Intersect with the value-fixing subgroup and descend through the coordinate
quotient using surjectivity and the proved fiber equality: ready
`DescendedCochain` (cap 200). The quotient is finite and discrete. These are
cochain results; comparison with the continuous complex's differentials,
cocycles, common-stage boundaries and colimits remains separate work.


### W16 proved boundary and next missing bridges

Checked 2026-10-03 03:19 UTC by the per-module builds/lints/axiom audits
and `Scratch/LiftsW16/check.py`; exact modules, caps and commits are recorded
in the W16 acceptance section of LIFTS_GOAL_LEDGER.md. The W15 BLOCKED table
is historical: the integral U01a–d, U02a, U03a, N02a, N03a, and the cochain
parts C04a–c above are now proved. U01's valued-field specialization and the
remaining cohomology statements are not implied by those completions.

The equivalence takes actual DVRs R,S with fraction fields K,L, an
`IsIntegralClosure S R L`, a finite Galois L/K, a local R→S map and
`Algebra.FormallyUnramified R S`. It derives finite/free R-module structure,
separable residue, and Galois invariance. These are standard arithmetic
hypotheses on an extension, not assumed conclusions about reduction.
There is no valuation-topology hypothesis in this integral theorem, and no
claim that two independent local-field valuations are automatically compatible.

The first unresolved U-series bridge is now **realization and normality**,
not residue-action surjectivity. Refine the following before coding; each
proposed leaf retains cap 200 and is not certified ready by this document:

1. U03b1: specialize `exists_unramified_extension_of_residueField` to a
   finite residue extension; derive `IsIntegralClosure`, formal
   unramifiedness, and Henselianity/completeness of its constructed DVR.
   Existing finite-extension and `RaynaudStageHenselian` lemmas are candidates;
   their hypotheses must be matched to the constructed ring, not assumed.
2. U03b2: in that Henselian DVR, lift all distinct roots of the residue
   polynomial and prove that the lifted defining polynomial splits.
   Hensel existence and uniqueness are available; the splitting/counting
   proof and its concrete polynomial presentation remain to assemble.
3. U03b3: deduce normality of the fraction extension from that splitting,
   combine with the existing separability, and obtain a Galois stage of
   every requested residue degree. A finite separable extension of the
   right degree alone does not supply normality.
4. U03b4: embed the stages into the chosen separable closure, prove uniqueness
   of the unramified image and finite compositum compatibility. Then build
   U04's supremum/inverse-limit comparison and U05's continuous characters.

For a general valued-local-field frontend, identify the extended valuation
ring with the integral closure and match the chosen unramified predicate.
Mathlib already has `Ideal.ramificationIdx_eq_one_iff` (with separable
residue-field hypotheses) and
`Algebra.FormallyUnramified.iff_map_maximalIdeal_eq`. Do not mark those
criteria themselves missing; the remaining obligation is transporting the
actual local extension into their contexts.

For the norm route, reuse the existing residue-unit quotient equivalence.
N01's higher principal-unit graded quotient and N02's norm-as-trace formula
on it remain unimplemented; these enable the successive corrections of N03
and convergence of N04. N03a proves only the first residue approximation.

For the cohomology route, `exists_descended_cochain` is stronger than finite
image: it supplies a continuous function on `(G/N)^n`, finite G/N, the
inflation formula, and N-invariance of every value. Next construct the G/N
action on the N-fixed coefficient module, identify the differential on that
finite complex, and descend cocycles and bounding cochains to common stages.
The integral low-degree comparison C01, colimit C05, and later invariant and
class-formation gates remain. No class-field conclusion is smuggled into
these cochain hypotheses.

## W17 refinement (2026-10-03)

The implementation sequence below refines U03b before its proofs. Each new
module has a 200-line cap; these are targets until validated.

| Leaf | Contract | Dependency |
|---|---|---|
| U03b1a / UnramifiedDegree | From equal fraction/residue degrees in a finite separable DVR extension, derive maximal-ideal equality, formal unramifiedness, integral closure, completeness and Henselianity | local fundamental identity, integral-closure rank, ideal factorization |
| U03b1b / UnramifiedExistence | Apply those results to the existing residue-extension constructor | U03b1a |
| U03b2a / HenselianRoots | Lift simple residue roots uniquely and transfer splitting of a monic polynomial | Hensel existence/uniqueness, root count |
| U03b2b / UnramifiedPolynomial | Construct an integral power basis whose minimal polynomial has separable reduction and splits upstairs for finite residue fields | U03b1, U03b2a, existing residue-generator API |
| U03b3 / UnramifiedNormal | Deduce normality and Galois structure of the actual fraction extension | U03b2b, fraction-field power basis |
| U03b4 | Embed into the separable closure; prove uniqueness and compositum compatibility | U03b3, integral-root uniqueness |

U03b4 must be refined further after the normality interface is known. U04/U05
and E1c7 remain blocked, and no bridge is to be supplied as a new hypothesis.

W17 U03b4 refinement after the normality proof:

| Leaf (cap 200 each) | Concrete contract |
|---|---|
| UnramifiedEmbeddings | Lift a residue-field embedding to a fraction-field embedding using the constructed monic generator and Hensel; obtain embeddings when residue degrees divide |
| UnramifiedUniqueness | For actual intermediate fields with integral unramified DVRs, residue-degree divisibility implies containment; equal residue degrees imply equality |
| UnramifiedStages | Embed each constructed Galois stage in the chosen separably closed overfield, retain its actual integral ring and degree data |

A common overfield plus normality turns the constructed embeddings into
literal containment. No uniqueness, containment, or residue lift is an input.
The compositum and inverse-limit leaves require an explicit stage interface
and will be refined after these statements are checked.

W17 ready follow-ons after stage uniqueness (200 lines per module):

- `UnramifiedStageTower`: choose the unique stage indexed by positive degree;
  prove containment iff divisibility, compositum = the lcm stage, and directedness.
  The compositum proof uses containment in the lcm stage and degree divisibility,
  so it does not require an unproved hereditary-unramifiedness bridge.
- `UnramifiedUnion`: define the supremum, prove every element lies in a finite
  stage, prove normality and include every finite unramified stage.

These statements do not establish a topological inverse-limit equivalence,
restriction surjectivity from the absolute Galois group, or the inertia kernel.
Those remain distinct U04 obligations before U05.

W17 U04 API audit: Mathlib already supplies
`InfiniteGalois.continuousMulEquivToLimit` and
`AlgEquiv.restrictNormalHom_surjective`; neither is a missing general theorem.
The next two bounded leaves (cap 200) are:

- `UnramifiedCofinality`: every finite intermediate field contained in the
  union is contained in a degree-indexed stage, using a primitive element.
- `UnramifiedGaloisLimit`: specialize the existing topological inverse-limit
  equivalence to the constructed union, and prove continuous surjective
  restriction from the chosen separable closure.

The generic limit is indexed by all finite Galois intermediate fields of
the union. Reindexing it explicitly by positive degrees is distinct from
cofinality. Identifying the restriction kernel with the existing valuation
inertia group remains blocked on the valued-field/residue-closure frontend.

## W17 proved scope and next gates

The U03b realization chain is now implemented under a complete DVR base
with finite residue field. The constructor's equal degree output implies
maximal-ideal equality, formal unramifiedness and complete Henselian integral
closure. A primitive residue element lifts to an integral algebra generator;
its polynomial splits by lifting all simple residue roots. The fraction field
is consequently normal. Each positive degree gives a Galois stage in the
chosen separable closure, and these stages are unique with containment iff
degree divisibility and compositum equal to the lcm stage.

`IsUnramifiedStage` is an existential predicate for an actual finite
unramified Henselian DVR model, not an assumed normality/uniqueness interface.
Normality and equal fraction/residue degree are proved consequences. This
frontend uses algebraic complete-DVR hypotheses; it has not yet been matched
to every analytic valued-local-field representation used elsewhere in FLT.

The directed supremum is constructed and Galois. Each element lies in a
finite stage; each finite subextension of the supremum is contained in one.
Its Galois group is topologically equivalent to the existing inverse limit
over **all finite Galois intermediate fields of the supremum**. Restriction
from the chosen separable closure is continuous and surjective, with kernel
exactly the automorphisms fixing every degree-indexed stage pointwise.

Remaining U gates (not certified ready):

1. Reindex that explicit profinite limit by positive degrees and identify
   its transition maps with the compatible arithmetic Frobenius maps. The
   required field-containment cofinality is proved; categorical reindexing
   and the Frobenius coordinate comparison are not yet assembled.
2. Identify this restriction kernel with the repository's valuation inertia.
   Reuse `NumberField.map_localInertiaGroup_eq_inertia` and
   `map_localInertiaGroup_eq_finiteInertia` for their actual number-field
   completion contexts. The missing match is between the constructed models,
   the canonical integral closures/valuation rings, and the inertia-fixed
   finite subextensions; the existing finite inertia comparison is not missing.
3. Construct the normalized continuous unramified characters and prove the
   universal inertia-trivial factorization (U05) after that identification.

E1c7/E1d remain blocked. These U leaves do not provide local reciprocity,
principal-unit norm convergence, continuous cohomology comparison, the local
invariant/class formation, or Kummer–Artin evaluation, and do not remove
`IsHardlyRamified.lifts`. The independent Serre-weight and arbitrary-p
Raynaud classification gates remain untouched.

## W18 refinement (2026-10-03)

The next leaves retain a 200-line cap and use existing constructions:

- `UnramifiedDiagram`: positive degrees ordered by divisibility, finite Galois
  stages inside the union, and a final stage functor proved from W17 cofinality.
- `UnramifiedDegreeLimit`: apply the initial opposite functor to the explicit
  profinite limit cone; prove the resulting equivalence has restriction coordinates.
- `UnramifiedIntegralModel`: identify the existential integral DVR with the
  canonical integral closure and transport formal unramifiedness; transport the
  stage predicate across fraction-field equivalences.
- `UnramifiedStageFrobenius`: construct arithmetic Frobenius using those canonical
  rings and compare the diagram's transitions with W16 Frobenius restriction.

The inertia step must use the existing completion-specific finite comparison
and derive the converse finite unramifiedness from trivial inertia. No equality
of inertia with the constructed restriction kernel is an input hypothesis.

W18 inertia and character refinement, after matching the canonical models:

- `UnramifiedLocalInertia` (cap 200): prove ideal inertia is trivial using
  faithful residue action on the canonical integral closure; apply the existing
  number-field-completion restriction comparison.
- `UnramifiedInertiaConverse` (cap 200): from inertia fixing a finite Galois
  field, derive ramification index one, preserve a base uniformizer, and prove
  the canonical ring is an unramified Henselian DVR.
- `UnramifiedInertiaKernel` (cap 200): use finite Galois subfields of the
  inertia fixed field for the reverse inclusion; closedness of inertia turns
  fixed-field equality into equality of restriction kernels.
- `UnramifiedCyclicStages` (cap 200): use the actual arithmetic Frobenius as
  the cyclic generator, obtain Z/n coordinates, and prove continuity and
  normalization of the characters on the union's Galois group.
- `UnramifiedCharacterDescent` (cap 200): continuous surjective restriction
  from a compact group is a quotient map; derive unique continuous descent
  for all inertia-trivial homomorphisms.
- `UnramifiedCharacters` (cap 200): compose the normalized characters with
  absolute restriction, prove inertia triviality, and show Frobenius lifts exist.

The completion-specific statements retain W17's adic-completeness hypothesis
on the base DVR. This is an arithmetic hypothesis, not an assumed residue or
inertia comparison. The general analytic completeness transport is distinct
from the existing `rationalCompletionIntegers_adicComplete` specialization.

W18 next ready cochain leaves after U05 (cap 200 each): Mathlib already has
`Representation.quotientToInvariants` and `quotientToInvariants_lift`, and
`groupCohomology.cochainsMap` is already a chain map for the inhomogeneous
complex. These APIs are not missing. `FixedCoefficientCochain` can package
W16's descended cochain into that actual invariant coefficient module.
`FixedCoefficientDifferential` can specialize the existing chain map,
prove inflation injective, and reflect cocycles. This is a finite-stage
inhomogeneous-complex comparison; a separately constructed continuous complex,
common-stage boundaries, filtered colimits, and class formation remain distinct.

## W18 proved scope and next gates

Checked 2026-10-03 by the foreground per-module builds, individual lints and
axiom audits in `Scratch/LiftsW18/`; acceptance, caps and commits are in the
W18 section of LIFTS_GOAL_LEDGER.md. Recheck recorded evidence with
`python3 Scratch/LiftsW18/check.py`; that checker does not rerun Lean.

The limit is now explicitly indexed by positive degrees ordered by divisibility.
Its equivalence with the union's Galois group has proved restriction coordinates.
Canonical integral closures supply the actual DVR tower used by W16's Frobenius
comparison, giving a compatible arithmetic Frobenius point and a union automorphism.

In the number-field-completion frontend with complete base DVR, the constructed
union equals the fixed field of existing valuation inertia. The forward finite
comparison uses faithful residue action on the canonical integral closure. The
converse derives ramification index one, an integral uniformizer, formal
unramifiedness and Henselianity. Closedness of inertia identifies the restriction
kernel, rather than merely identifying a closure of the subgroup.

Normalized continuous Z/n-valued unramified characters and unique continuous
descent of inertia-trivial homomorphisms are proved. The target is expressed as
`Multiplicative (ZMod n)` for multiplicative Galois groups; the additive character
law is also proved. Frobenius lifts exist, and every such lift has value one.
`RationalUnramifiedCharacters` uses the existing rational-completion completeness
theorem, leaving no additional completeness hypothesis at any rational prime.

The two cochain leaves package W16 descent into the existing invariant coefficient
module and quotient representation. The existing inhomogeneous cochain map gives
injective inflation, differential compatibility and reflection of cocycles.
Continuous inhomogeneous cocycles therefore descend to actual finite quotient
cocycles with invariant coefficients.

Next contracts to refine, each retaining cap 200:

1. Common-stage boundary descent: for a continuous cochain b with d b = c,
   construct one open normal stage carrying b and c in compatible invariant
   coefficients and prove the finite differential equation. Do not assume a
   common stage or a differential bridge. The completed cocycle reflection alone
   does not identify boundaries at arbitrary independently chosen stages.
2. Construct or identify the continuous inhomogeneous complex and the directed
   transition maps between invariant coefficient stages; prove the filtered
   cohomology comparison. Mathlib's quotient action and algebraic cochain map
   already exist and are now used, so they are not missing APIs.
3. The norm route still needs higher principal-unit graded quotients, the norm
   as residue trace on them, successive corrections and convergence. The residue
   unit norm and first approximation from W16 do not finish those steps.
4. Extend the analytic completeness/valuation-ring frontend beyond the proved
   rational specialization when required by callers. The complete-DVR and
   number-field-completion results do not claim that independently supplied
   valuations automatically agree.

E1c7/E1d remain blocked on the outstanding reciprocity/cohomological program:
local invariant and class formation, norm convergence, and Kummer–Artin
evaluation. Serre-weight evaluation and arbitrary-p Raynaud classification are
still independent blocked gates; no implementation of either was dispatched.
The final lifting admission and final FLT axiom set are unchanged.

## W19 refinement (2026-10-03)

Each following leaf has a 200-line cap. Acceptance requires a foreground
module build, an individual-module lint and an audit of every declaration.

- `FixedCoefficientBoundary`: descend a continuous bounding cochain and take
  its finite differential, proving the boundary equation at that same stage.
- `InvariantStageTransition`: construct quotient pullback with invariant
  coefficient inclusion; prove identity, composition and inflation compatibility.
- `ContinuousCochainComplex`: define the submodules of continuous functions,
  prove differential stability and construct the continuous complex.
- `ContinuousStageDiagram`: use reverse inclusion of open normal subgroups
  for a filtered diagram of the actual quotient complexes and its inflation cocone.
- `ContinuousCochainColimit`: prove that cocone is a colimit degreewise, using
  finite descent and injective inflation, then a colimit of complexes.
- Common-refinement boundary detection and the cohomology colimit follow once
  the continuous complex interface is checked; refine those proofs into separate
  leaves if needed. No assumed boundary-detection or colimit bridge is permitted.

The higher principal-unit norm and class-formation gates remain distinct;
Serre-weight evaluation and arbitrary-p Raynaud classification stay blocked.

W19 cohomology and ready follow-on refinement (cap 200 each):

- `CochainHomologyClass`: representative surjectivity, vanishing iff boundary,
  and functoriality in the existing categorical homology; includes degree zero.
- `FilteredComplexDescent`: injective cocone maps reflect cocycles; descend a
  bounding cochain and construct a common refinement using filteredness.
- `FilteredHomologyDescent`: descend cohomology classes and detect vanishing
  and equality after refinement, using the preceding proved boundary theorem.
- `ContinuousCohomologyColimit`: apply those lemmas to the constructed cocone
  and prove the module colimit universal property and canonical isomorphism.
- `FiniteContinuousComparison`: identity-on-cochains comparison of finite
  discrete continuous and ordinary complexes, over an arbitrary commutative ring.
- `FiniteCharacteristicZeroCohomology`: use Mathlib's proved Maschke theorem
  and the existing Ext presentation to prove positive finite-group vanishing.
- `ContinuousCharacteristicZeroCohomology`: descend each continuous class
  to a finite quotient, then apply the finite vanishing theorem.

The finite comparison's compatibility with connecting maps and cup products,
restriction/coefficient naturality of the colimit comparison, and comparison
with W14's explicit homogeneous low-degree presentation are separate leaves.
Characteristic-zero vanishing does not assume an averaging homotopy; it uses
Mathlib's existing proof of Maschke and projectivity of semisimple modules.

## W19 proved scope and next gates — checked 2026-10-03 05:17 UTC

The W19 acceptance table in LIFTS_GOAL_LEDGER.md records the module commits,
caps, validation commands and evidence. Recheck recorded evidence with
`python3 Scratch/LiftsW19/check.py`; it does not rerun Lean.

Common-stage boundary descent, refinement maps, the continuous inhomogeneous
complex, and its filtered colimit of invariant-coefficient finite quotient
complexes are proved. `ContinuousStageBoundary` detects a boundary after a
constructed refinement of any independently supplied stage. Continuous
cohomology is the corresponding filtered colimit in every degree.

The next ready finite discrete comparison is proved over arbitrary commutative
rings. Positive continuous cohomology vanishes over any characteristic-zero
field, by finite descent and the proved Maschke/Ext route. This establishes the
vanishing conclusion of C06, including rational coefficients; no averaging
homotopy is supplied as a hypothesis.

C01's explicit integral low-degree comparison, C02's connecting-map/cup
compatibility, and restriction/coefficient naturality of C05's comparison
remain. C07 still needs the continuous exact-sequence construction and its
explicit boundary formula for Q/Z and Z. These interfaces must be proved,
not passed as bridges. The principal-unit norm convergence, local invariant,
class-formation and Kummer–Artin evaluation gates remain, as do the independent
Serre-weight and arbitrary-p Raynaud gates. E1c7/E1d and the final lifting
admission remain blocked; the final FLT axiom set is unchanged.

## W20 proved scope — checked 2026-10-03T06:04:11.614329+00:00

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

## W21 proved scope — 2026-10-03T06:41:20.511369+00:00

Checked 2026-10-03T06:41:20.511369+00:00; branch `task/goal-lifts-w21`; base `3ee6889c`.
**E1c7/E1d remain blocked; the final FLT theorem retains sorryAx.**

The module/commit/cap table is in the W21 acceptance section of
`LIFTS_GOAL_LEDGER.md`. Recheck accepted evidence with
`python3 Scratch/LiftsW21/check.py`; final axiom evidence is
`Scratch/LiftsW21/Final-axioms.log`.

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

## W22 historical proved scope — 2026-10-03T07:40:35.747894+00:00

Checked 2026-10-03T07:40:35.747894+00:00; base `c2adcddb`. Evidence:
`python3 Scratch/LiftsW22/check.py` and the separate module build/lint/axiom logs.
The full module/commit/cap table is in the W22 ledger section.
**E1c7/E1d remain blocked; the final FLT theorem still depends on sorryAx.**

The new arithmetic and cohomology endpoints concern **finite unramified extensions**.
`unramifiedStageOrderH2Iso` applies to every stage of the existing degree-indexed
diagram, using its canonical integral closure. The continuous multiplicative
H2 comparison for the whole unramified union is still unproved.

1. The principal units are actual kernels of reduction modulo πⁿ. For n > 0,
   the divided-coefficient symbol is surjective, its kernel is Uⁿ⁺¹, and the
   quotient is the additive residue field. The generator condition is the
   structural equality of the maximal ideal with (π).
2. The determinant expansion proves the norm's linear term is trace, with a
   quadratic remainder. The induced map on the actual graded unit quotients
   is residue trace. Separable residue trace surjectivity constructs each
   correction; it is not an input hypothesis.
3. The residue norm starts a recursive sequence. Each correction improves the
   norm error and preserves the preceding congruence upstairs. Finite freeness
   transfers base completeness to the extension; adic convergence, norm
   congruence, and separatedness give an exact unit norm.
4. Integral Hilbert 90 is strengthened to an integral **unit** witness by
   removing a fixed base-uniformizer power. The actual unit representation has
   algebra norm as its group norm and base units as its invariants. Both
   periodic cyclic complexes are exact. Frobenius generation then proves
   every positive finite-stage unit cohomology group is zero.
5. The maximal-ideal valuation defines integer order, zero on integral units
   and +1 on a uniformizer. The actual order sequence is short exact as Galois
   representations. Its long exact sequence and proved unit acyclicity make
   order an isomorphism in every positive degree, including multiplicative H2.
   Canonical-stage instances are derived, including freeness; no arithmetic
   conclusion is assumed as a parameter or record field.
6. Integer order is preserved by embeddings in unramified towers. This is a
   coefficient-level compatibility theorem; the continuous colimit comparison
   and its naturality are not claimed by it.

### W22 remaining comparisons (historical; see W23 above)

1. Construct the discrete continuous Galois action on the integral units of
   the unramified union and identify its invariant coefficient modules with
   the canonical integral units of finite stages. The existing
   `continuousCohomologyColimitIso` uses `invariantStageCohomologyDiagram`,
   indexed by open normal subgroups; the new finite-stage representation
   endpoints are not yet connected to that diagram. This is the immediate
   unresolved comparison, not an assumed vanishing theorem.
2. Prove the compatible coefficient/cohomology maps under finite-stage
   inflation and restriction, using `discreteOrder_unramified_tower`, then
   derive continuous unit acyclicity and the continuous order-H2 isomorphism.
   Compose with W21's integral Frobenius/Q/Z coordinates and check the carry
   normalization in the multiplicative comparison.
3. Inflation to the full separable closure, class formation, and Kummer–Artin
   evaluation remain unproved. W14's cup-order minus sign remains unchanged.
   Serre-weight evaluation and arbitrary-p Raynaud classification remain
   independently blocked; neither was dispatched or assumed available.

The first two steps require refining against the existing invariant-stage APIs;
do not replace their proofs with hypotheses. No claim is made here that all
principal-unit subgroups are themselves acyclic. The proved vanishing is for
the full integral-unit group of a finite unramified extension.

Read-only API boundary check: `Scratch/LiftsW22/remaining-api-check.log`.
The generic continuous-colimit theorem and the new canonical-stage endpoints
exist, but no new declaration identifies their coefficient representations.
The finite-stage cohomology endpoints use `Type`, matching Mathlib's integral
Hilbert-90 and cyclic-cohomology interfaces; the ring-only filtration, norm,
and order lemmas retain their more general universe parameters.

Final audit: `LEAN_NUM_THREADS=2 lake env lean Scratch/LiftsW22/FinalAxioms.lean`,
exit 0; evidence `Scratch/LiftsW22/Final-axioms.log`:

- `GaloisRepresentation.IsHardlyRamified.lifts` and `FLT.Assembly.hardlyRamifiedLifting`:
  `[propext, sorryAx, Classical.choice, Quot.sound]`.
- `PNat.pow_add_pow_ne_pow`:
  `[Mazur_statement, propext, sorryAx, Classical.choice, Quot.sound]`.
- The new graded quotient, graded trace, unit norm, unit acyclicity, and
  canonical-stage multiplicative H2 comparison use only the three standard axioms.
