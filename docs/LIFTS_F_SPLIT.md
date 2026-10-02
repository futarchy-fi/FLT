# F: fundamental characters from reduced root ratios

Audit: 2026-09-30, parent `0534178c`; commands below reproduce the API checks.
W7 F4a checked 20:05 UTC: build, module lint, five axiom audits passed;
logs `Scratch/LiftsW7/F4a-{build,lint,axioms}.log`; 183/300 lines.
W7 F4 checked 20:13 UTC: build, module lint, 17 axiom audits passed;
logs `Scratch/LiftsW7/F4-{build,lint,axioms}.log`; 300/400 lines.
W7 F5a checked 20:17 UTC: build, module lint, ten axiom audits passed;
logs `Scratch/LiftsW7/F5a-{build,lint,axioms}.log`; 92/250 lines.
Source-lemma leaves, each at most 400 lines including headers. F1–F3
are DONE (W6); F4a is DONE (W7, RootInertiaTransitivity, cap 300).
F4 endpoints are DONE (W8); F5–F6 and finite-tower surjectivity remain.
Caps are hard stop limits, not claims that unimplemented proofs fit.
This document is capped at 200 lines. No weight definition or classification
is supplied by this split.

Sources: S = Serre, *Sur les représentations modulaires de degré 2*, Duke
Math. J. 54 (1987), §2, DOI 10.1215/S0012-7094-87-05413-5 (fundamental
characters, conjugacy, cyclotomic normalization). L = Serre, *Local Fields*,
Ch. IV §2 (tame inertia), Ch. IV §4 (cyclotomic extensions), Ch. V §2
(unramified extensions). These are mathematical references, not a claim
that the missing local-field proofs already exist in Mathlib.

## Shared notation and contracts

All sketches use the existing number-field/completion context:
```lean
variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
-- Kv := v.adicCompletion K; O := v.adicCompletionIntegers K
-- L := AlgebraicClosure Kv; A := IntegralClosure O L
-- k := IsLocalRing.ResidueField A; k0 := IsLocalRing.ResidueField O
-- I := localInertiaGroup v; q := Nat.card k0
variable {n : ℕ} (hn : 0 < n) {a b : Kv} (ha : a ≠ 0) (hb : b ≠ 0)
  {α β : L} (hα : α^n = algebraMap Kv L a)
  (hβ : β^n = algebraMap Kv L b)
-- cα := LocalRoot.character v hn ha hα; cβ analogously
```
The abbreviations in comments expand literally in the declarations below.
For n=q^r−1 require r>0; q>1 follows from `residueCard_one_lt`.
Use the geometric ratio σ(α)/α. Never silently invert this convention.

## F1 — root-choice independence, DONE, cap 250

New `FLT/AbsoluteGaloisGroup/RootCharacterIndependence.lean`.
Source S §2: roots of the same element differ by an integral unit.
```lean
theorem character_eq_of_unit_ratio
    (z : Aˣ) (hz : (z : A).1 = β / α) : cβ = cα
theorem character_root_independent
    {β : L} (hβ : β^n = algebraMap Kv L a) :
    LocalRoot.character v hn ha hβ = cα
```
Prove that β/α has n-th power one, hence belongs to A and is a unit;
reduce σ(z)/z using inertia's trivial residue action. No prime-to-p
hypothesis is needed for equality of the *reduced* characters.
Anchors: RootCharacter `root_ne_zero`, `integralRatio`, `coe_ratioUnit`;
TameCharacter `residue_smul_eq` and the unit calculation in
`reducedKummerRatio_uniformizer_independent`. Dependencies: W5.1 only.

## F2 — uniformizer independence and compatible levels, DONE, cap 300

New `FLT/AbsoluteGaloisGroup/RootCharacterUniformizer.lean`.
Sources S §2, L IV §2: equal valuations give unit ratios; powers give norms.
```lean
theorem exists_unit_ratio_of_uniformizers {π π' : O}
    (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ))
    (hπ' : Valued.v π'.1 = Multiplicative.ofAdd (-1 : ℤ))
    {α β : L} (hα : α^n = algebraMap Kv L π.1)
    (hβ : β^n = algebraMap Kv L π'.1) :
    ∃ z : Aˣ, (z : A).1 = β / α
-- With the same π,π',α,β,hπ,hπ',hα,hβ binders:
theorem character_uniformizer_independent :
    LocalRoot.character v hn (uniformizer_nonzero hπ') hβ =
      LocalRoot.character v hn (uniformizer_nonzero hπ) hα
-- uniformizer_nonzero is the existing completion.uniformizer_ne_zero,
-- followed by Subtype.ext to pass from O to Kv.
theorem character_degree_mul_independent (m : ℕ) (hm : 0 < m)
    {β : L} (hβ : β^(n*m) = algebraMap Kv L a) (σ : I) :
    LocalRoot.character v (Nat.mul_pos hn hm) ha hβ σ ^ m = cα σ
```
Last statement removes the compatible-root *choice* from W5.1's identity;
for r|s set n=q^r−1 and m=(q^s−1)/(q^r−1). Divisibility arithmetic is
independent of the character theorem. It does not identify coefficient fields.
Anchors: TameCharacter `exists_unit_root_ratio_of_uniformizers` (degree-one
pattern), AdicValuation `maximalIdeal_eq_span_uniformizer`, Mathlib
`isUnit_pow_iff`, RootCharacter `character_degree_mul`. Dependencies: F1.

## F3 — continuity and finite image, DONE, cap 250

New `FLT/AbsoluteGaloisGroup/RootCharacterTopology.lean`.
Sources S §2, L IV §2: the character is constant on root-stabilizer cosets.
```lean
theorem character_isLocallyConstant : IsLocallyConstant cα
theorem character_continuous [TopologicalSpace kˣ] : Continuous cα
theorem character_ker_isOpen : IsOpen (cα.ker : Set I)
theorem character_range_finite : Finite cα.range
```
Prove local constancy using the open sets {τ | τ(α)=σ(α)} in the Krull
topology, then continuity for any target topology (in particular discrete).
Finite image follows by injection into `rootsOfUnity n k`, using
`character_pow`. Do not call this finite quotient *the tame quotient*.
Anchors: `ContinuousSMulDiscrete.isOpen_smul_eq`,
`IsLocallyConstant.iff_exists_open`, `.continuous`, `.isOpen_fiber`,
the `Finite (rootsOfUnity n k)` instance. Dependencies: W5.1 (F2 fixes canonical choices).

## F4 — tame quotient endpoints DONE (W7–W8), cap 400

New `FLT/AbsoluteGaloisGroup/FundamentalTame.lean`.
Sources L IV §2, S §2. Define `rootCharacterToRoots` by codRestrict using
`character_pow`, for an n-th root α of a uniformizer π. Exact endpoints:
```lean
theorem rootCharacterToRoots_surjective (hnk : (n : k) ≠ 0)
    (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ)) :
    Function.Surjective (rootCharacterToRoots v hn hπ hα)
theorem wildInertia_le_ker (hnk : (n : k) ≠ 0)
    (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ)) :
    wildInertia v ≤ (LocalRoot.character v hn (uniformizer_nonzero hπ) hα).ker
```
`LocalRamification.wildInertia v` is defined by first-ramification congruences
at every finite Galois level. W7 proves normality, kernel containment and the
surjective quotient character via `QuotientGroup.lift`, independently of kernels.
W7 F4a: `LocalRoot.inertia_transitive` proves transitivity in every positive
degree via Eisenstein over finite inertia fixed fields and restriction
surjectivity. W7 `FundamentalTame` proves both displayed endpoints (in all
positive degrees), plus `LocalRamification.tameRootCharacter_surjective`.
W8 filtration DONE (274/300); finite p-groups and tower stability DONE (228/250).
W8 pro-p endpoint and explicit compatible-family homeomorphism DONE (235/250).
BLOCKED: first-group tower surjectivity; exact target and capped split in `BLOCKED.md`.
Checked 20:59 UTC: all three builds, individual lint and 49 axiom audits passed.
Evidence: `Scratch/LiftsW8/{Filtration,PGroup,Wild}-{build,lint,axioms}.log`.
Anchors: HilbertTheory `IsInertiaField`, `InertiaComparison` restriction
surjectivity, QuotientGroup `lift`, `quotientKerEquivRange`. Dependencies:
F1–F3; the existing level-one tame kernel is not enough.

## F5 — finite coefficients and Frobenius conjugacy, READY after W7 F5a, cap 400

New `FLT/AbsoluteGaloisGroup/FundamentalCoefficients.lean`.
Sources S §2, L V §2. For p prime and r>0, define the subfield
`levelField p r` of k by x^(p^r)=x (requires `[CharP k p]`). Prove its
cardinality p^r, then construct embeddings in Ω := AlgebraicClosure (ZMod p).
For `[Fact p.Prime]`, `hr : 0 < r`, exact target sketches are:
```lean
noncomputable def levelEmbedding : levelField p r →+* Ω
theorem levelEmbedding_frobenius (ι j : levelField p r →+* Ω) :
    ∃ i < r, ∀ x, j x = (ι x) ^ (p^i)
-- ωι := Units.map ι.toMonoidHom composed with the level-field character
theorem fundamentalCharacter_frobenius (ι j : levelField p r →+* Ω) :
    ∃ i < r, ∀ σ : I, ωj σ = ωι σ ^ (p^i)
```
For residue cardinality q=p^f distinguish niveau r over Fp from degree r
over k0 (exponent q^r−1 gives niveau f*r); do not identify the two.
W7 F5a DONE: `RootCharacterResidue` proves algebraic closedness and transports
characteristic from the completion residue field, via an explicit algebra
equivalence with its algebraic closure. It also proves existence of a prime
characteristic. Finite coefficients and Frobenius conjugacy remain to be
implemented; no arbitrary embedding of all of k into Ω is assumed.
Anchors: Mathlib `IsAlgClosed.lift`, `GaloisField`,
`bijective_frobeniusAlgEquivOfAlgebraic_pow`, `residueFieldMap`.
Dependencies: W7 F4 surjectivity and W7 F5a residue bridge (both proved).

## F6 — omega-one equals cyclotomic, BLOCKED, cap 400

New `FLT/AbsoluteGaloisGroup/FundamentalCyclotomic.lean`.
Sources S §2 and L IV §4. Restrict to K=ℚ and the place over p, transport
the completion to ℚ_[p], and use F5's canonical Fp embedding. Exact endpoint:
```lean
theorem fundamentalCharacter_one_eq_cyclotomic
    (p : ℕ) [Fact p.Prime] :
    omegaOne p = (Units.map (algebraMap (ZMod p)
      (AlgebraicClosure (ZMod p))).toMonoidHom).comp
      ((modCyclotomic p).comp (localInertiaGroup v).subtype)
```
Here `omegaOne`, `modCyclotomic` and the completion transport are NEW adapters
with the displayed common domain I; use the existing cyclotomic action on
μp, not a character newly defined to equal omega. Include p=2 (both trivial).
Missing arithmetic lemma for p>2: for primitive ζp, ζp−1 is a uniformizer
in ℚp(ζp), and reducing σ(ζp−1)/(ζp−1) gives the mod-p cyclotomic value.
Prove the normalized valuation/ramification bridge in this leaf;
no cyclotomic equality may be passed as an input. Dependencies: F1–F5.
Anchor: FLT's `cyclotomicCharacter.toZMod`; valuation and primitive-root APIs.

## Rerunnable API evidence and acceptance

```sh
rg -n 'root_ne_zero|character_pow|character_degree_mul' FLT/AbsoluteGaloisGroup/RootCharacter.lean
rg -n 'unit_root_ratio|residue_smul_eq|uniformizer_independent|residueFieldMap' FLT/AbsoluteGaloisGroup/TameCharacter.lean
rg -n 'isOpen_smul_eq' FLT/Mathlib/Topology/Algebra/ContinuousSMulDiscrete.lean
rg -n 'Finite \(rootsOfUnity' .lake/packages/mathlib/Mathlib/RingTheory/RootsOfUnity/Basic.lean
rg -n 'iff_exists_open|isOpen_fiber|theorem continuous' .lake/packages/mathlib/Mathlib/Topology/LocallyConstant/Basic.lean
rg --no-ignore -n 'IsInertiaField|wildInertia|ramificationGroup' .lake/packages/mathlib/Mathlib/NumberTheory/RamificationInertia FLT/AbsoluteGaloisGroup
rg --no-ignore -n 'bijective_frobeniusAlgEquivOfAlgebraic_pow|def lift' .lake/packages/mathlib/Mathlib/FieldTheory
rg -n 'cyclotomicCharacter.toZMod' FLT/Mathlib/NumberTheory/Cyclotomic
```
Foreground builds only, LEAN_NUM_THREADS=2. Lint each new MODULE separately:
`lake exe runLinter MODULE`. Audit all new declarations with `#print axioms`;
only propext, Classical.choice, Quot.sound permitted. Check caps and sorted
FLT.lean imports with `grep '^public import' FLT.lean | LC_ALL=C sort -c`.
Commit this document, then each ready leaf separately; never push. Keep logs
and completion/blocker notes untracked outside FLT/.
