# E1c7: local reciprocity and the local invariant

Source/API check: 2026-10-03, FLT base `4bb55369`, Mathlib
`c32e1ec0d1eb5237ba344eee50162f45d5b0fc76`. This is a foundational program,
not a claim that local class field theory fits in a 200-line adapter.
Each proposed module below has a **200-line hard cap**. Blocked contracts
are design sketches, not elaborated declarations or certified size estimates;
split again before implementation if a proof exceeds the cap. No missing
theorem may become a structure field, parameter standing for E1c7, or axiom.

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

## Dependency split committed before implementation

All module names in the table are under `FLT/LocalClassFieldTheory/`, except
S03 (`FLT/GaloisRepresentation/Extensions/ContinuousCupSwap`). `Hc`, `Hd`,
`U`, `Unr`, `inv`, `rec`, `δ`, `Inf`, and `Res` below are **sketch notation**,
not invented existing Lean identifiers. Every `≃+` must be constructed with
its stated computation rule proved. All rows have cap 200.

Only S01–S03 are certified ready in this wave. Other rows are BLOCKED on
the dependencies listed and/or the named unresolved implementation bridge.
Absence of a dependency edge does not certify API readiness. No general
class-field theorem is counted as completed by proving an abstract adapter.

| ID / module | Lean-shaped contract / proof sketch | Dependencies / gate |
|---|---|---|
| S01 / RationalTorsion | `zmodToRatCircle : ZMod n →+ AddCircle (1:ℚ)`; `map_intCast`, injectivity, range = `{x | n • x = 0}`. Descend `z ↦ z/n`; clear denominators. | READY: `ZMod.lift`, quotient group, rational arithmetic |
| S02 / CyclicCarry | `carry : ZMod n → ZMod n → ℤ`; `carry_cast = j.val/n - (i+j).val/n + i.val/n`; cocycle equation and zero normalization. | READY after S01; `ZMod.val_add`, arithmetic |
| S03 / ContinuousCupSwap | Construct opposite continuous cup and `b(g)=d(g) • c(g)`; prove `db=-(cup+opposite)`, and equivalence of coboundary conditions. | READY: W14/E1b continuous cochains |
| V01 / NormalizedOrder | `ord : Kˣ →* Multiplicative ℤ`; surjectivity, kernel = valuation-ring units; uniformizer has order +1. | BLOCKED implementation bridge: negate exponent in `valueGroupWithZeroIsoInt`, connect to `ValuationSubring` used by Kummer |
| V02 / PowerClassOrder | `PowerClass K p →* Multiplicative (ZMod p)` with representative formula and kernel = `unitClasses A p`. | V01; existing `isUnitClass_iff_valuation` |
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

## Acceptance checks

For each implemented module M, sequentially run
`LEAN_NUM_THREADS=2 lake build M`, `LEAN_NUM_THREADS=2 lake exe runLinter M`,
and `#print axioms` for every new named declaration. Only propext,
Classical.choice, Quot.sound may occur. Builds stay in the foreground;
never run whole-library lint. Record actual line counts and local commits.
Audit the final theorem separately; support lemmas do not remove sorryAx.
