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
