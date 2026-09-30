# W5: independent Serre weight and the finite-flat boundary

API audit: 2026-09-30, parent `3d4558e1`; rerun the searches below.
This refines W4.4, not W4.5. Five leaves, two READY, each capped at 400
lines including headers. The remaining leaves are adapters **after** named
foundation programs; they are not claims that those programs fit in 400 lines.
No weight-bearing record, new axiom, or identification of flatness with weight.

## Sources and mathematical contract

S: Serre, *Sur les représentations modulaires de degré 2*, Duke Math. J.
54 (1987), 179–230, §2 (fundamental characters, ramification of extensions,
weight normalization), DOI 10.1215/S0012-7094-87-05413-5.
R: Raynaud, *Schémas en groupes de type (p,...,p)*, Bull. SMF 102 (1974),
241–280, https://www.numdam.org/item/BSMF_1974__102__241_0.pdf.
K: Khare–Wintenberger II, §3.2.2–3.2.3,
https://www.math.ucla.edu/~shekhar/papers/proofs.pdf;
local text `Scratch/kw-proofs.txt:1180–1210` explicitly distinguishes the
finite-flat weight-2 case from weight p+1 with the same diagonal characters.
S and R are primary references, not claims that their proofs are in Lean.

For p>2 and cyclotomic determinant, the ordinary finite-flat case has
inertial semisimplification χ ⊕ 1 **and a peu ramifiée extension class**.
The same semisimplification with a très ramifiée extension has weight p+1.
The irreducible local case has niveau-two characters ω₂, ω₂^p and weight 2.
Thus determinant or semisimplification alone does not prove weight 2.
General finite-flat models without the rank/determinant hypotheses do not
have this conclusion. Keep unramified twists and coefficient embeddings.
Use geometric roots with action σ(α)/α throughout; check this convention
against the existing cyclotomic character before invoking the normalization.

## W5.1 — reduced root characters, READY, cap 350

New `FLT/AbsoluteGaloisGroup/RootCharacter.lean`, namespace `LocalRoot`.
Source S §2's construction of fundamental characters by roots of a uniformizer.
Import `FLT.AbsoluteGaloisGroup.TameCharacter`. Shared context:

```lean
variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
-- L := AlgebraicClosure (v.adicCompletion K)
-- A := IntegralClosure (v.adicCompletionIntegers K) L
variable {n : ℕ} (hn : 0 < n) {a : v.adicCompletion K} (ha : a ≠ 0)
  {α : L} (hα : α ^ n = algebraMap (v.adicCompletion K) L a)
noncomputable def character : localInertiaGroup v →* (IsLocalRing.ResidueField A)ˣ
 theorem character_pow (σ : localInertiaGroup v) : character v hn ha hα σ ^ n = 1
```

Prove the integral ratio is a root of unity and use `residue_smul_eq` to
prove multiplication. Also prove the compatible-root identity, for m>0:
`character v hn ha hα σ ^ m = character v hn ha' hα' σ`,
where `ha' : a^m ≠ 0` and `hα' : (α^m)^n = algebraMap _ _ (a^m)`.
This is an actual character on existing inertia, not an abstract input field.
It permits n=q^r−1, a a uniformizer. No assertion of surjectivity, continuity,
coefficient identification, or choice independence is hidden in this leaf.
Dependencies: existing inertia/residue action, none of W5. Consumer: F below.

## W5.2 — arbitrary-exponent Kummer classes, READY, cap 300

New `FLT/GroupScheme/KummerCocycle.lean`, namespace `KummerTheory`.
Source S §2's Kummer description of the exceptional extension class;
Hilbert 90 is the algebraic descent step, not the local ramification theorem.
Import Mathlib Hilbert90 and existing `FLT.GroupScheme.KummerParameter`.
For fields K,L with `[Algebra K L] [FiniteDimensional K L] [IsGalois K L]`:

```lean
 theorem exists_kummer_parameter {n : ℕ} (hn : 0 < n) (f : Gal(L/K) → Lˣ)
    (hf : groupCohomology.IsMulCocycle₁ f) (hpow : ∀ g, f g ^ n = 1) :
    ∃ a : K, ∃ b : L, a ≠ 0 ∧ b ≠ 0 ∧ b^n = algebraMap K L a ∧
      ∀ g : Gal(L/K), g b = (f g : L) * b
 theorem kummer_parameter_power_iff {n : ℕ} (hn : 0 < n)
    (f : Gal(L/K) → Lˣ) (a : K) (b : L) (hb : b ≠ 0)
    (hpow : b^n = algebraMap K L a)
    (heq : ∀ g : Gal(L/K), g b = (f g : L) * b) :
    (∃ r : K, r^n = a) ↔
      ∃ c : L, c^n = 1 ∧ ∀ g : Gal(L/K), g c = (f g : L) * c
```

Also, for a valuation subring A of K and q : Kˣ, prove
`(∃ b : Kˣ, A.valuation (q : K) = A.valuation (b : K)^n) ↔
 ∃ b : Kˣ, ∃ u : Aˣ, q = b^n * Units.map A.subtype.toMonoidHom u`.
This recognizes unit representatives modulo n-th powers independently of
finite flatness. It is not yet `IsPeuRamifiee`: continuous descent and the
extension-to-cocycle comparison remain in E below. Dependencies: none of W5.
Consumer: E; preserve the existing cubic API unchanged.

## Foundation programs that are NOT bounded leaves

F (fundamental characters): W5.1 → root/uniformizer independence for q^r−1,
continuity, tame quotient and wild inertia, surjectivity, compatible levels,
finite-residue-field embeddings into an algebraic closure of ZMod p,
Frobenius conjugacy, and ω₁=χ on inertia. Existing `tameCharacter` supplies
level one only; its name does not provide the niveau-two classification.
E (extension classes): W5.2 → continuous H¹ and finite-quotient descent,
upper-triangular representations modulo changes of splitting, Kummer
identification after the appropriate unramified twist, unit subgroup,
peu/très invariance. Define peu using that unit subgroup, never a flat model.
S0 (full recipe): F+E → Serre §2's complete case table, twisting/minimality,
scalar/unramified and exceptional cases, basis/coefficient invariance and
well-definedness of `serreWeight`. Do not define only the weight-two case.
R0 (Raynaud): classification of arbitrary p-primary finite-flat models with
coefficient action, tame inertia exponents bounded by e, e=1 specialization,
and the ordinary extension-class/unit comparison. Existing order-three
rigidity is not this arbitrary-p classification. This is a separate program,
not a 400-line task. Track the ordinary and niveau-two branches separately.

## W5.3 — normalized weight evaluations, BLOCKED on F+E+S0, cap 250

New `FLT/GaloisRepresentation/SerreWeight/Normalization.lean`.
Proposed API below; none of its new symbols exists before the programs finish.
For p prime, p>2, a continuous two-dimensional local representation
`τ : GaloisRep ℚ_[p] (AlgebraicClosure (ZMod p)) V`:

```lean
 theorem serreWeight_ordinary_peu (h : HasOrdinaryInertia τ)
    (he : IsPeuRamifiee τ) : serreWeight p τ = 2
 theorem serreWeight_ordinary_tres (h : HasOrdinaryInertia τ)
    (he : ¬ IsPeuRamifiee τ) : serreWeight p τ = p + 1
 theorem serreWeight_niveauTwo (h : HasNiveauTwoInertia p τ) : serreWeight p τ = 2
```

`HasOrdinaryInertia` means χ above 1, retaining the actual extension;
`HasNiveauTwoInertia` means conjugate to diag(ω₂,ω₂^p) on inertia.
These predicates use representations, not assumed weights. Include explicit
p>2 and rank-two hypotheses in each declaration. Source S §2; evaluate the
independent definition, no finite-flat imports. Consumer: W5.4.

## W5.4 — finite-flat weight adapter, BLOCKED on W5.3+R0, cap 350

New `FLT/GaloisRepresentation/SerreWeight/FiniteFlat.lean`.
For p>2, rank-two `τ : GaloisRep ℚ_[p] (ZMod p) V`, let τbar be its scalar
extension to the algebraic closure, and `χ` the mod-p cyclotomic character:

```lean
 theorem finiteFlat_serreWeight_two
    (hflat : GaloisModule.IsFiniteFlat ℤ_[p] ℚ_[p]
      (AlgebraicClosure ℚ_[p]) τ.Space)
    (hdet : ∀ g, τ.det g = χ g) : serreWeight p τbar = 2
```

R0 must *prove* `(HasOrdinaryInertia τbar ∧ IsPeuRamifiee τbar) ∨
HasNiveauTwoInertia p τbar` from hflat/hdet. W5.4 consumes this disjunction
and W5.3. Sources R and S, applied in K §3.2.2–3.2.3. No classification
hypothesis added to this endpoint, no weight record. Consumer: W5.5.

## W5.5 — hardly-ramified adapter, BLOCKED on W5.4+F, cap 250

New `FLT/GaloisRepresentation/HardlyRamified/ResidualSerreWeightTwo.lean`.
In W4.4's exact HR context with coefficients ZMod p, p≥17:
`theorem residual_serreWeight_eq_two (hp17 : 17 ≤ p)
 (hρ : IsHardlyRamified hpodd hV ρ) : serreWeight p ρ = 2`.
Here global `serreWeight` abbreviates the local/scalar-extension definition,
with invariance under the chosen completion equivalence proved in S0.
Use W4.1 to extract hρ.isFlat, transport the model from the adic completion
to ℚ_[p], compare determinants using F, then apply W5.4. Source K and S.
No claim that these leaves prove `IsHardlyRamified.lifts`.

## Rerunnable evidence and acceptance

```sh
rg -n 'residue_smul_eq|reducedKummerCharacter|tameCharacter' FLT/AbsoluteGaloisGroup/TameCharacter.lean
rg -n 'exists_cubic_kummer_parameter|cubic_kummer_parameter_cube_iff' FLT/GroupScheme/CubicKummerCocycle.lean
rg -n 'exists_unit_factor' FLT/GroupScheme/KummerParameter.lean
rg -n 'isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units' .lake/packages/mathlib/Mathlib/RepresentationTheory/Homological/GroupCohomology/Hilbert90.lean
rg -n 'serreWeight|SerreWeight|fundamentalCharacter|IsPeuRamifiee' FLT .lake/packages/mathlib/Mathlib
```

Anchors at audit: TameCharacter:265,282,410; CubicKummerCocycle:31,54;
KummerParameter:25; Hilbert90:84. Last search has no matches at the parent.
Build foreground `LEAN_NUM_THREADS=2 lake build MODULE`; lint each new module
alone with `LEAN_NUM_THREADS=2 lake exe runLinter MODULE`; `#print axioms`
for all new declarations. Register sorted imports in FLT.lean; run
`grep '^public import' FLT.lean | LC_ALL=C sort -c`. Commit doc, then each
ready leaf locally. Never push. Record verification in untracked notes.
