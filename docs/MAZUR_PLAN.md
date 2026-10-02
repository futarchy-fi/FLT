# MZ0: an honest route to `MazurTorsionExclusion`

Checked against FLT commit `ebda856762c41368c7942d2aa004c51b7d2d2dc4`
on 2026-09-28 UTC. This is a source-grounded research plan, not a proof of
Mazur's theorem. The first elementary leaf is implemented in
`FLT/EllipticCurve/FullTwoPrimeTorsion.lean`.

## Decision

Use the **prime-level argument in Mazur (1977), Chapter III, §5,
pp. 156–160**, to prove `NoLargePrimeTorsion`, then apply the existing
`FLT.Assembly.mazurTorsionExclusion_of_noLargePrimeTorsion`.
This is the shortest complete route substantiated in this investigation,
not a claim that no shorter proof could exist. It discards the extra
full-two-torsion hypothesis deliberately: the existing prime-level adapter
is ready, and the cited proof needs less machinery than a complete torsion
classification or a composite-level isogeny classification.

**The remaining arithmetic is months-scale infrastructure.** A preliminary
engineering allowance is **25,000–70,000 new Lean lines and 2,500–7,000
worker-hours**, including foundational APIs, proof development, and review.
These are rough estimates, not measured throughput or a delivery promise;
source-level design of the modular Jacobian may increase them substantially.
Several contributors over many months is a realistic planning unit. No
weekend-sized path from the current category-D results was found.

The immediate deliverable is this committed plan and a clean elementary
leaf. It does **not** remove `Mazur_statement` from the FLT proof, prove
`NoLargePrimeTorsion`, or prove `MazurTorsionExclusion` unconditionally.

## Exact target and the already completed adapters

The target at `FLT/Assembly/Mazur.lean:25` is:

```lean
def MazurTorsionExclusion : Prop :=
  ∀ (p : ℕ), p.Prime → 17 ≤ p →
    ∀ (E : WeierstrassCurve ℚ), E.IsElliptic →
      ¬ ∃ f : ((ZMod 2 × ZMod 2) × ZMod p) →+ (E⁄ℚ).Point,
        Function.Injective f
```

All point notation below uses `open scoped WeierstrassCurve.Affine`.
The quantifier is over **all** rational elliptic curves, without restrictions
on conductor, reduction, or discriminant. Full rational two-torsion is not
an FLT counterexample, and a split cubic need not have coefficients that
are p-th powers satisfying the Frey equation.

| Existing declaration | What is actually available |
|---|---|
| `FLT/MazurWOfPrimeTorsion.lean:23`, `NoLargePrimeTorsion` | Definition of the stronger prime-point exclusion; not a proof. |
| Same file:29, `mazur_W_of_noLargePrimeTorsion` | Proved adapter: restrict `f` to `(0,1)` and preserve additive order. Do not schedule it again. |
| Same file:42, `no_fullTwoTimesPrime_of_torsion_bound` | Proved generic finite-cardinality adapter. Its finite bound is a hypothesis. |
| `FLT/Assembly/Mazur.lean:32`, `mazurTorsionExclusion_of_noLargePrimeTorsion` | Proved final adapter, about five lines. |
| `FLT/FreyCurve/Mazur.lean:35`, `FreyPackage.mazurW_counterexample_of_reducible` | Reducible **Frey** representation produces an elliptic curve with the forbidden injection. This is the forward construction, not an exclusion. |
| `FLT/FreyCurve/Serre/JoinCoprimeTorsion.lean:27`, `SerrePlan.join_coprime_torsion` | Injective two-primary and odd-cyclic homomorphisms combine. |
| `FLT/FreyCurve/Serre/FreyTwoTorsion.lean:57`, `FreyPackage.frey_full_two_torsion` | Two-torsion injection for a Frey package. |
| `FLT/FreyCurve/Serre/FixedLineDescent.lean:72`, `rational_torsion_of_fixed_line` | A fixed line in geometric torsion descends to rational points. |
| `FLT/FreyCurve/Serre/QuotientCurve.lean:52`, `quotient_curve_of_trivial_quotient` | Quotient construction from a trivial odd-prime quotient, useful for isogeny work. |
| `FLT/MazurW.lean:59`, `fullTwoTorsion_survives_of_kernel_killed` | Pure group argument preserving two-torsion under an odd-primary kernel. |

Trust distinction: an existing declaration is not automatically a clean
arithmetic theorem. `FLT/MazurW.lean:23` (`mazur_W`) uses the explicit
`Mazur_statement` assumption at `FLT/Assumptions/Mazur.lean:103`;
`mazur_W_ge11` at `FLT/MazurW.lean:50` has an admitted proof. Neither is an
acceptable input to its own replacement. The new elementary file imports
Mathlib only. The reuse table is a source audit; it does not certify every
transitive dependency of the larger Frey modules.

## Comparing the requested routes

### (a) Full two-torsion, reducibility, and the Frey/category-D machinery

An injected `ZMod p` gives a Galois-fixed line in `E[p]`, hence reducibility.
The Weil pairing supplies the other diagonal character, cyclotomic; the
representation can still have a nontrivial extension class. This does not
force its ramification to be confined to `{2,p}`.

`IsHardlyRamified` at
`FLT/GaloisRepresentation/HardlyRamified/Defs.lean:96` requires all of:
rank two, cyclotomic determinant, unramifiedness away from `{2,p}`,
flatness at p, and a prescribed quotient at two. The Frey verification
`torsion_isHardlyRamified` in `HardlyRamified/Frey.lean:95` uses a
`FreyPackage`. General rational torsion gives none of its discriminant
p-divisibility input. Changing curves by isogeny does not justify deleting
arbitrary bad primes; in particular, good reduction of elliptic curves is
isogeny invariant.

Even granting hardly ramifiedness, a result saying the representation is
**reducible** agrees with the rational-point hypothesis. It is not a
contradiction. The lifting/family path starts from **irreducibility**, so
using it here to manufacture irreducibility would be circular.

| Relevant existing machinery | Why it does not close this target |
|---|---|
| `HardlyRamified/PrimeField.lean:42`, `not_isIrreducible_of_prime_field` | Concludes reducibility and goes through the admitted `lifts` in `HardlyRamified/Lift.lean:37`. |
| `HardlyRamified/CategoryD.lean:73`, `ThreeAdicPlan.InCategoryD` | Finite flat objects over `ℤ[1/2]`, three-primary order, square-zero inertia at two. These are extra hypotheses. |
| `HardlyRamified/CategoryDClassification.lean:94`, `simpleDThree` | Classifies simple category-D objects as constant-three or μ₃. Constant torsion is allowed. |
| `FLT/GroupScheme/FontaineDifferentBound.lean:26`, `fontaineDifferentBoundKilledThree` | Local bound for finite flat objects over `ℤ_[3]` killed by three; not an arbitrary-p global torsion bound. |
| `FLT/GroupScheme/ReverseExtVanishing.lean:24`, `reverseExtVanishing` | Splits the specified constant-three/μ₃ extensions over `ℤ[1/2]`; does not supply an arbitrary-p theorem over the bases required below. |
| `FLT/TateCurve/AlgebraicUniformization.lean:101`, `algebraicUniformization` | Substantial local Tate-curve machinery exists. It needs a local Tate presentation and does not prove global rational torsion exclusion. |
| `FLT/MazurChapter/AdmissibleGroupSchemes.lean:101,168,190` | General-prime classification/cohomology declarations exist, but their bodies are admitted. They are not a completed Mazur chapter. |

The first five `HardlyRamified/...` paths in these tables are relative to
`FLT/GaloisRepresentation/`. Ext and Fontaine results may contribute proof
techniques, but three cannot simply be renamed to p: base rings, ramification
bounds, and global cohomology all change.

A restricted theorem only for the original Frey curve and its odd-isogenous
quotients would suffice for a redesigned FLT assembly, but is **not the
requested universally quantified target**. The current counterexample
witness forgets that provenance. No independent short exclusion for this
restricted class was found either.

**Verdict:** no justified reduction to existing endpoints. No finite estimate
for a purported shortcut; the missing global step is the research problem.

### (b) Eisenstein ideal / modular curves — chosen prime-level variant

The injection supplies a point of order p and also one of order 2p (first
leaf below). Thus maps to `X₁(p)`, `X₁(2p)`, and `X₀(2p)` are candidates.
The actual full-level configuration belongs to a mixed-level moduli problem;
a cyclic 2p point forgets one independent two-torsion generator. Never infer
full two-torsion from a point of order 2p.

Choose `X₀(p)` and the pair `(E, ⟨P⟩)`, retaining the rational generator in
the elliptic-curve arguments. Mazur's original prime-level proof gives a
complete dependency chain, and avoids composite-level integral geometry.
Proving all relevant rational cyclic-isogeny degrees to exclude degree 2p
would also work, but imports a further deep classification and its exceptional
cases. Neither that classification nor these algebraic modular curves were
located as usable endpoints in FLT/Mathlib. Analytic modular-form spaces and
Jacobian coordinate formulas are not modular Jacobian varieties.

**Source pinned:** B. Mazur, *Modular curves and the Eisenstein ideal*,
Publ. Math. IHÉS **47** (1977), 33–186,
[DOI 10.1007/BF02684339](https://doi.org/10.1007/BF02684339),
[Numdam PDF](https://www.numdam.org/item/PMIHES_1977__47__33_0.pdf).
The PDF was downloaded and its introduction and III §5 read for this plan.
The introduction on pp. 35–36 explicitly explains that torsion of the
Eisenstein quotient's rational points and nonzero cuspidal image suffice.
For its finiteness input, it points to I §1, II §§6, 8.10, Proposition 14.1,
and III §3. Do not implement the entire 154-page paper by default.

III §5, pp. 157–160, supplies:

1. `0 → Z/p → E[p] → μ_p → 0` and a cyclotomic extension `L/K`.
2. Semistability; bad multiplicative reduction at two and three, with the
   rational p-point outside the identity component at three.
3. A **global** Eisenstein-quotient argument makes that last assertion hold
   at every bad prime. Two cusp specializations cannot coexist, because
   rational torsion specializes injectively at odd good primes and the cusp
   difference has nonzero image.
4. Local splitting/unramifiedness at all primes, then Herbrand's theorem:
   the cyclotomic inverse-character component would force p to divide the
   numerator of `B₂ = 1/6`, which it does not.
5. Splitting yields repeated μ_p-isogenies retaining rational p-torsion.
   Finiteness of `X₀(p)(ℚ)` (already supplied by the Eisenstein quotient)
   forces a repetition, hence a nonscalar rational endomorphism of an
   elliptic curve over ℚ, impossible. This avoids adding Shafarevich's
   finiteness theorem as a second major global input.

For p ≥17 the genus and small-prime inequalities in this argument hold.
There is no need to formalize Kubert's small composite-order cases, all
fifteen torsion groups, or torsion finiteness for arbitrary elliptic curves.
The local finite-flat rigidity in Step 1 is for ramification index at most
six with `6 < p - 1`; the existing three-primary Fontaine bound is not this
rigidity theorem.

A formal-immersion proof is an alternative presentation of the modular
argument, not a proved shortcut here. This plan follows the explicit
original cusp-specialization/Herbrand route instead of silently assuming
formal immersion or a winding quotient.

### (c) Kamienny / Merel

Degree-one uniform boundedness alone gives a bound B, not the exact exclusion
p ≥17. An explicit larger B would leave all primes between 17 and B to
exclude. The modular-symbol, symmetric-power/formal-immersion, and winding
quotient/nonvanishing inputs were not located as ready theorems here.

**Verdict:** not selected. Rough scope: 40,000–100,000+ lines,
4,000–10,000+ worker-hours, plus any exceptional-prime computations.
This is no saving over a rational prime-level argument.

### (d) Elementary exclusion for `(Z/2)² × Z/p`

No sourced uniform elementary proof was found. This is a search result,
not a theorem that such a proof is impossible. Lutz–Nagell constrains points
on a fixed integral curve; its discriminant is not uniformly bounded as E
varies. Reduction at a good prime bounds prime-to-residue-characteristic
torsion, but neither two nor three is guaranteed good. At split
multiplicative primes, p-torsion can lie in the component group; local Tate
parameters can be p-th powers. Full rational two-torsion does not eliminate
that possibility.

Division polynomials or genus calculations for individual modular curves
can settle particular orders, but need a uniform argument to cover all
p ≥17. Replacing this gap with a claim that positive genus implies no
rational points is false. An elementary route needs an independently
verified global lemma before it can be budgeted as an implementation route.

## First three bounded leaves

These are honest algebraic interfaces, not three steps that nearly finish
Mazur. L2/L3 clarify the exact special-case hypothesis for an alternative
route; the selected stronger prime-level route can use L1 directly.
No task may count the already existing prime-exclusion adapter again.

**L1 — extract exact orders, implemented.**
New file `FLT/EllipticCurve/FullTwoPrimeTorsion.lean`; 40 lines,
allowance 1–2 worker-hours. Statements:

```lean
theorem FLT.addOrderOf_fullTwoPrime_last
    {A : Type*} [AddCommGroup A] {n : ℕ}
    (f : ((ZMod 2 × ZMod 2) × ZMod n) →+ A)
    (hf : Function.Injective f) : addOrderOf (f (0, 1)) = n

theorem FLT.addOrderOf_fullTwoPrime_mixed
    {A : Type*} [AddCommGroup A] {n : ℕ} (hn : Nat.Coprime 2 n)
    (f : ((ZMod 2 × ZMod 2) × ZMod n) →+ A)
    (hf : Function.Injective f) : addOrderOf (f ((1, 0), 1)) = 2 * n
```

Dependencies: Mathlib `addOrderOf_injective`, `Prod.addOrderOf`,
`ZMod.addOrderOf_one`, `Nat.Coprime.lcm_eq_mul`. The last-factor calculation
already occurred inside an existing proof; exposing it is a refactoring,
while the mixed-order result records the composite-level alternative.
No primality or ellipticity assumption is needed, including for n=1.

**L2 — separate the two independent factors.** New, 30–70 lines,
1–3 worker-hours. For `{A} [AddCommGroup A] {p : ℕ}`:

```lean
theorem fullTwoPrime_iff_factor_embeddings (hp : Nat.Coprime 2 p) :
    (∃ f : ((ZMod 2 × ZMod 2) × ZMod p) →+ A, Function.Injective f) ↔
    (∃ f₂ : (ZMod 2 × ZMod 2) →+ A, Function.Injective f₂) ∧
    (∃ fₚ : ZMod p →+ A, Function.Injective fₚ)
```

Forward: compose with `AddMonoidHom.inl/inr`. Reverse: existing
`SerrePlan.join_coprime_torsion`. No geometry or new finite-flat claims.
Acceptance: compile and audit this equivalence without the Mazur assumption.

**L3 — exact-order point versus cyclic embedding.** New wrapper,
40–100 lines, 2–4 worker-hours; check Mathlib's cyclic-subgroup equivalences
before duplicating their construction.

```lean
theorem cyclic_embedding_iff_exact_order
    {A : Type*} [AddCommGroup A] {n : ℕ} (hn : 0 < n) :
    (∃ f : ZMod n →+ A, Function.Injective f) ↔
    ∃ P : A, addOrderOf P = n
```

Forward: preserve order of one. Reverse: factor `ℤ →+ A`, `k ↦ k • P`,
through `ZMod.lift`, using the exact-order characterization of its kernel.
L2 + L3 convert the target into: for an elliptic E with an injected
`(ZMod 2)²`, there is no point of order p. Estimate a further 20–40 lines /
1–2 hours for that curve-specific equivalence; no global theorem is gained.

## Missing arithmetic: statements, dependencies, and budgets

The following are **statement sketches**, not declarations to add with
unproved fields. Identifiers such as `X0Integral`, `EisensteinQuotient`,
`TorsionField`, `EverywhereUnramified`, and `CyclicIsogeny` name APIs to be
constructed. Every symbol must acquire its usual geometric meaning and
its own invariants. In this section fix prime p ≥17, an elliptic E/ℚ, and
`P : E(ℚ)` of exact order p. `(hP : addOrderOf P = p)` is retained in all
elliptic-curve statements. Estimates include each row's new prerequisites
and overlap; do not sum them as independent fixed-price bids.

### G1. Algebraic modular curve and its integral moduli interpretation

```lean
def primeLevelPoint (E) (P) (hP) : NoncuspidalPoint (X0 p) ℚ

theorem primeLevelPoint_integral (hsemi : SemistableEverywhere E) :
  ∃ x : Section (X0Integral p) (SpecZInvert (2 * p)),
    x.genericFiber = primeLevelPoint E P hP

theorem specialization_cusp_iff (q) (hq : q.Prime) (hq2 : q ≠ 2)
    (hqp : q ≠ p) (hbad : MultiplicativeReduction E q) :
  (specializesTo x q cuspZero ↔ LiesInIdentityComponent E P q) ∧
  (specializesTo x q cuspInfinity ↔ ¬ LiesInIdentityComponent E P q)
```

New: generalized elliptic curves, level structures, compactification,
coarse/fine moduli issues, cusps and their integral specialization. Existing
Weierstrass points and schemes are building blocks only. **8,000–20,000
lines / 800–2,000 hours.** Source: I §1; III §5 Step 3 and its cited
Deligne–Rapoport moduli interpretation.

### G2. The qualitative Eisenstein quotient

```lean
def eisensteinProjection : X0 p ⟶ EisensteinQuotient p

theorem eisenstein_rational_points_finite :
  Finite (RationalPoints (EisensteinQuotient p))

theorem eisenstein_cusps_distinct :
  eisensteinProjection cuspZero ≠ eisensteinProjection cuspInfinity

theorem eisenstein_projection_nonconstant :
  ¬ IsConstant eisensteinProjection

theorem x0_rational_points_finite : Finite (RationalPoints (X0 p))
```

New: modular Jacobian as an abelian variety, Hecke correspondences/algebra,
Eisenstein ideal/quotient, its descent and rational-point finiteness,
nontrivial cuspidal image, integral abelian schemes and the projection.
Last theorem uses nonconstant maps of proper curves having finite fibers.
Dependencies: G1, general-prime finite-flat/cohomology foundations, abelian
varieties; the admitted `MazurChapter` statements cannot discharge them.
**12,000–35,000 lines / 1,200–3,500 hours.** Source locations are the
introduction's abbreviated chain quoted above, and III (4.1).
The target only needs nonzero cusp image, not the entire exact rational
point group computation, although a chosen proof may establish more.

### A1. Rational p-torsion forces semistability and controls small primes

Implemented subcase: `FLT/EllipticCurve/SmallResidueTorsion.lean` proves that
a good integral Weierstrass model over a valuation subring with finite residue
field of cardinality at most three has no generic-fiber point of prime order
at least seventeen. The coordinate bound `#E(k) ≤ #k² + 1` replaces Hasse's
bound here. A unit leading coefficient of the division polynomial forces
torsion coordinates to be integral, proving that the reduction kernel has no
torsion of invertible order. The unit condition for large primes follows from
the small residue cardinality. This proves the good-reduction obstruction,
not semistability, the bad-reduction cases, or `NoLargePrimeTorsion`.

The same module now proves integral affine coordinates for torsion of
invertible order without a good-reduction assumption. Consequently any point
of prime order at least seventeen specializes to a **singular** affine point
over residue fields of cardinality at most three, and the reduced
discriminant vanishes. These statements apply to arbitrary integral models.
They do not classify additive versus multiplicative reduction, identify
Néron components, or exclude torsion specializing to the singular point.
All these distinctions are necessary before claiming A1 is complete.

For split multiplicative reduction, `FLT/FreyCurve/Serre/TateRationalTorsion.lean`
proves that the Tate torsion exponent on points over the local field is
injective when the prime exceeds the finite residue cardinality; the
prime-torsion group then has cardinality at most that prime. The proof uses
the existing Tate uniformization and proves that the local field has no
nontrivial roots of unity of that prime order. This is a statement about
the Tate exponent, **not yet about the Néron component group**. It does not
exclude a cyclic rational prime-torsion subgroup. Identifying components,
handling nonsplit/additive reduction, and A2–A5 remain open.

```lean
theorem semistable_of_large_prime_point (hP) : SemistableEverywhere E

theorem component_at_two_of_large_prime_point (hP) :
  MultiplicativeReduction E 2 ∧ ¬ LiesInIdentityComponent E P 2

theorem component_at_three_of_large_prime_point (hP) :
  MultiplicativeReduction E 3 ∧ ¬ LiesInIdentityComponent E P 3

theorem component_at_p_of_large_prime_point (hP)
    (hbad : MultiplicativeReduction E p) : ¬ LiesInIdentityComponent E P p
```

New: Néron models, component groups and specialization for general E,
potential semistability with ramification index ≤6 at residue characteristic
p≥17 (after excluding additive reduction away from p), generic-fiber rigidity
for order-p finite flat groups when `e < p-1`, and the finite-field point
bound. The p-case also needs the absence of p-torsion in the formal group
over ℚ_p and in the rational points of the reduced multiplicative identity
component. Reuse local good-reduction and Tate implementations after checking
their generality; they do not yet supply this packaged result.
**2,000–6,000 lines / 200–600 hours.** Source: III §5 Steps 1–2.
This work can start independently of G1/G2 after its precise APIs are fixed.

### A2. The indispensable global step at every bad prime

```lean
theorem torsion_specialization_injective_odd
    (T : OpenSubscheme (Spec ℤ)) (A : AbelianScheme T)
    (q) (hq : q.Prime) (hqOdd : Odd q) (hqIn : q ∈ T) :
  Function.Injective (specializeTorsion A q)

theorem component_at_every_bad_prime (hP) (q) (hq : q.Prime)
    (hbad : BadReduction E q) : ¬ LiesInIdentityComponent E P q
```

Dependencies: G1, G2, A1; integral projection and the odd-prime torsion
specialization theorem. If P lay in the identity component at bad q, its
moduli point would specialize to opposite cusps at three and q. Finiteness
of the Eisenstein rational group makes all images torsion; injectivity of
specialization identifies both with the same image, contradicting distinct
cusps. Cases q=2,3,p need the source's local handling, not the integral map
over a base that inverts 2p. **800–2,500 lines / 80–250 hours**, after APIs.

### A3. Cyclotomic torsion extension and local unramifiedness

```lean
theorem torsion_extension_description (hP) :
  CyclicDegreeOneOrPrime (TorsionField E p) (CyclotomicField p ℚ) p ∧
  ConjugationCharacterInverseCyclotomic (TorsionField E p) p

theorem torsion_extension_unramified (hP) (hcomponents : ...) :
  EverywhereUnramified (TorsionField E p) (CyclotomicField p ℚ)
```

Dependencies: A1/A2, Weil pairing, fixed-line linear algebra, Tate
uniformization at bad primes, finite-flat connected/étale analysis at p,
and good-reduction unramifiedness. Splitting fields and local/global
comparison must be actual field extensions. **1,500–4,000 lines /
150–400 hours.** Source: III §5 (5.4), third reduction, and Step 4.

### A4. The Herbrand weight-two component vanishes

```lean
theorem inverse_cyclotomic_unramified_extension_trivial
    (L) (hGalois : IsGalois ℚ L) (hcyclic : CyclicDegreeOneOrPrime L (CyclotomicField p ℚ) p)
    (hunr : EverywhereUnramified L (CyclotomicField p ℚ))
    (hchar : ConjugationCharacterInverseCyclotomic L p) :
  ExtensionDegree L (CyclotomicField p ℚ) = 1

theorem rational_prime_torsion_sequence_splits (hP) :
  SplitsGaloisSequence (constantLine E P) (torsionCyclotomicQuotient E P)
```

New: required class-field-theoretic comparison and the particular Herbrand
component result, with `B₂ = 1/6`; not the false claim that cyclotomic fields
always have trivial p-class groups. Second theorem uses A3 and first theorem.
**3,000–8,000 lines / 300–800 hours.** Source: I (2.9); III §5 third reduction.
Searches did not locate a ready FLT Herbrand endpoint. Existing three-primary
reverse Ext vanishing has different coefficients and base.

### A5. Isogeny iteration gives the contradiction

```lean
theorem quotient_by_mu_retains_rational_prime_point (E) (P) (hP)
    (hsplit : SplitsGaloisSequence ...) :
  ∃ (E') (φ : CyclicIsogeny E E' p) (P' : E'(ℚ)),
    KernelIsMuPrime φ ∧ addOrderOf P' = p

theorem constant_prime_pairs_over_coarse_point_finite
    (x : RationalPoints (X0 p)) :
  Finite (RationalIsomorphismClassesOfPairsOver x)

theorem no_infinite_mu_prime_chain
    (hfinite : Finite (RationalPoints (X0 p))) :
  ¬ Nonempty (MuPrimeIsogenyChainOverRat p)

theorem noLargePrimeTorsion : NoLargePrimeTorsion
```

Dependencies: A4, G2; quotient curves and their duals; iteration retaining
rational points, repeated isomorphism class, and the proof that rational
endomorphisms of elliptic curves over ℚ are scalar. The cyclic nature of
composites must be proved before declaring a repeated isogeny nonscalar;
it is not enough that its degree is a prime power. The chain structure must
record the surviving rational p-point and its compatibility under every
map. Prove no backtracking: the dual of a μ_p-isogeny has constant kernel,
and μ_p is not the constant group over ℚ for p≥17. The next μ_p-kernel
therefore differs from the preceding dual kernel. Prove that this implies
cyclic composites; equivalently, no composite kernel contains all of E[p].

**Coarse moduli caveat:** finite `X₀(p)(ℚ)` alone does not imply finitely
many rational isomorphism classes of elliptic curves: quadratic twists
have the same coarse point. The pairs in the fiber lemma above must carry
an actual rational point of exact order p. Prove its finite-fiber assertion
using the finite forgetful map from the rational-generator moduli problem
(`X₁(p) → X₀(p)`, with fine moduli for p≥5), or prove directly that only
finitely many twists of a fixed pair can retain a rational p-generator.
This is an additional obligation, not a consequence of finiteness of
coarse points. Budget 500–1,500 lines / 50–150 hours within A5 for it;
the direct twist proof may avoid constructing the full compactified X₁(p).

Existing Vélu/quotient
files can help, but exporting actual isogenies and their kernels is work.
**2,000–6,000 lines / 200–600 hours.** Source: III §5 second reduction.
Use modular finiteness, not an unimplemented Shafarevich theorem.

### A6. Target assembly

```lean
theorem mazurTorsionExclusion : FLT.Assembly.MazurTorsionExclusion :=
  FLT.Assembly.mazurTorsionExclusion_of_noLargePrimeTorsion noLargePrimeTorsion
```

Dependency: A5 with a clean complete dependency audit. **5–20 lines /
1–2 hours** plus integration checks. The existing adapter is reused.
This is the first point at which claiming unconditional exclusion is valid.

## Dependency graph and stopping gates

```text
L1 -------------------------------> existing final prime-point adapter
L2 + L3 --------------------------> optional exact special-case interface
G1 ---> G2 ---> finite X0(Q) -------------------------------> A5
G1 + G2 + A1 ---> A2 ---> A3 ---> A4 ---> A5 ---> A6
A1 ---------------------> A3
```

Before dispatching the large packages, refine G1/G2 into source-linked
contracts and review the finite-flat/cohomology dependencies in G2.
The sketches above expose those packages; they are not capped leaves.
A source review that finds a shorter special-case proof should replace
this route before those large implementations begin. Do not spend months
building composite-level modular curves merely because the input includes
two-torsion.

No admitted structure field, imported torsion axiom, or circular invocation
of the Frey irreducibility theorem may count as completion. Check dependencies
with `#print axioms` on each accepted endpoint, not just a textual scan of
its immediate body. A lemma conditional on `NoLargePrimeTorsion` is an
interface, not a proof of that proposition.

## Validation of this delivery

The new module was built alone under the 10 GB memory constraint:

```sh
lake build FLT.EllipticCurve.FullTwoPrimeTorsion
lake lint -- --no-build FLT.EllipticCurve.FullTwoPrimeTorsion
```

The separate audit file imports that module and runs:

```lean
#print axioms FLT.addOrderOf_fullTwoPrime_last
#print axioms FLT.addOrderOf_fullTwoPrime_mixed
```

Checked on 2026-09-28 at 09:49 UTC: the module build and targeted Batteries
lint passed; both printed dependency lists were exactly
`[propext, Classical.choice, Quot.sound]`. The new Lean source contains no
`sorry`, `admit`, `axiom`, or `native_decide`. Check the
three-line `LAST.txt` for the completed verification time and commits.
Other project modules were source-audited, not rebuilt or trust-certified.
