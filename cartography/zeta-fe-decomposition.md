# Dedekind zeta functional equation — S/M decomposition (hub-lsb1u.6.4)

Target: node **M2** of `cartography/odlyzko-reconciled.md` — the completed Dedekind
zeta `Λ_K(s)` for an arbitrary number field `K`: meromorphic continuation to `ℂ`,
simple poles only at `s = 0, 1`, and `Λ_K(s) = Λ_K(1−s)`. This file breaks that XL
wall into a dependency-ordered tree in which **every node is S or M** — each node is
meant to be provable by one agent in one focused session (S ≈ one lemma/half-file,
M ≈ one tight file).

All Mathlib declaration names below were verified against the FLT repo's pinned
Mathlib (`lake-manifest.json` rev `bc06ce9f…`), by direct grep of
`.lake/packages/mathlib` — not from memory.

## Route choice: Hecke's theta-function proof (not Tate's thesis)

**Chosen route: classical Hecke** — per-ideal-class theta series on the mixed space
`ℝ^{r₁} × ℂ^{r₂}`, lattice Poisson summation, integration over a fundamental domain
for the unit action in the *parameter* space, and Mellin transform fed into
Loeffler's abstract FE engine. Justification: Mathlib's entire existing zeta/L
functional-equation stack (Riemann, Hurwitz, Dirichlet — Loeffler–Stoll, arXiv
2503.00959) is built on exactly this template, and the reusable engine is already
in Mathlib as `WeakFEPair` (`Mathlib.NumberTheory.LSeries.AbstractFuncEq`): feed it
a pair of kernels with a `t ↦ 1/t` transformation law and rapid decay, and it
*returns* meromorphic continuation, the functional equation, and both residues.
Every other ingredient the Hecke route needs is within one or two lemmas of current
Mathlib: multivariate Fourier series on tori (`Mathlib.Analysis.Fourier.
AddCircleMulti`, Loeffler 2023 — visibly laid as groundwork for multidimensional
Poisson), Gaussian Fourier transforms on inner-product spaces
(`fourierIntegral_gaussian_innerProductSpace`), lattice covolume and summability
(`ZLattice.covolume`, `Mathlib.Algebra.Module.ZLattice.Summable`), trace duality and
the different (`FractionalIdeal.dual`, `differentIdeal`), the ideal lattice and its
covolume (`NumberField.mixedEmbedding`,
`volume_fundamentalDomain_fractionalIdealLatticeBasis`), and Roblot's unit-orbit
machinery (`fundamentalCone`, `integerSet`, unit-smul lemmas, `unitLattice`,
`regulator`). By contrast, Tate's thesis needs Schwartz–Bruhat functions, Fourier
analysis / Pontryagin self-duality of `𝔸_K`, adelic Poisson summation
(Riemann–Roch), and local zeta functional equations — none of which exists; the FLT
repo's adelic layer (`FLT/HaarMeasure/*`, Fujisaki) is *measure-theoretic only*, with
no additive characters or adelic Fourier theory, and the adelic route would bottom
out in the **same** lattice Poisson summation anyway (via `K` discrete cocompact in
`𝔸_K`). Hecke decomposes into the S/M tree below; Tate would start with three or
four L-sized pure-infrastructure craters before touching zeta.

**Prior art (web-checked 2026-08, changes the execution but not the tree).**
Loeffler–Stoll (AFM 1, 2025; arXiv 2503.00959) built the ℚ-side of exactly this
route and state no Dedekind plan of their own; Mathlib master still has **no**
lattice Poisson summation, lattice theta, or ζ_K continuation/FE. But three
external effort lines exist and should be audited before any bead is cut:

1. **CBirkbeck/AINTLIB**, `projects/DedekindResidue/CompletedZeta/` — a full
   completed-Dedekind-zeta pipeline (`IdealLattice`, `ThetaLattice`,
   `PoissonLattice`, `PoissonSummation`, `HeckeTheta`, `FEPair`, `GammaStrip`,
   `MellinAgreement`, `Normalisation`, `FunctionalEquation`, `Existence`),
   reportedly sorry-free in the files spot-checked, instantiating `WeakFEPair`.
   Its file layout maps almost one-to-one onto Parts A–G below — independent
   confirmation that this is the right decomposition, and a porting source that
   could turn several M nodes into S-sized porting/refactor beads.
2. **Vilin97/lean-pool**, `LeanPool/Odlyzko/` (copyright "The FLT Project") — a
   Dedekind-zeta/Odlyzko effort targeting this very axiom, with
   `CompletedZeta/FunctionalEquation` *specialized to totally complex fields*.
   Overlap with our chapter is direct; coordinate to avoid duplicate work.
3. **Mathlib in-flight PRs**: #40735/#40736 (Browning: idele class group, Hecke
   characters + L-functions, definitions only, no FE) and #42567 (Roblot:
   prime-ideal zeta summability — feeds the parent map's M1 Euler-product node,
   not this tree).

First action of the first bead: a Zulip/repo audit of (1) and (2) — verify
sorry-freeness, license, and Mathlib-portability; every node below then carries
an implicit "port if sound, prove if not" execution mode. The tree stands either
way: it is the correct S/M partition whether nodes are proved fresh or ported.

Normalizations are fixed once here (this discharges the route-level part of PQ4 of
the reconciled map): Fourier transform `𝓕f(ξ) = ∫ f(x) e^{−2πi⟨x,ξ⟩}`, Mellin
`∫₀^∞ f(t) t^{s} dt/t`, `Gammaℝ s = π^{−s/2} Γ(s/2)`, `Gammaℂ s = 2·(2π)^{−s} Γ(s)`
(Deligne normalization, `Mathlib.Analysis.SpecialFunctions.Gamma.Deligne`), and
`Λ_K(s) = |d_K|^{s/2} · Gammaℝ(s)^{r₁} · Gammaℂ(s)^{r₂} · ζ_K(s)`.

## Dependency tree

Notation: `K` a number field, `n = [K:ℚ]`, `r₁/r₂` real/complex places, `𝔡` the
different ideal, `d_K` the discriminant, `w` = `torsionOrder K`. "Mixed space"
`E_K := mixedSpace K = (ℝ^{r₁}) × (ℂ^{r₂})`, equipped with its `WithLp 2` Euclidean
structure (already set up at `CanonicalEmbedding/Basic.lean:815`). Parameter space
`Y := (0,∞)^{InfinitePlace K}` with local weights `n_v = 1, 2`.

Sizes are S or M only, by design. Each node lists: statement, size, direct
dependencies (node numbers + existing Mathlib decls), one-line proof sketch.

### Part A — Lattice Poisson summation (pure Mathlib, upstreamable as-is)

**A1. Dual lattice.** Define `ZLattice.dual` of a full `ℤ`-lattice `L` in a
finite-dimensional real inner-product space:
`L* = {x | ∀ v ∈ L, ⟪x, v⟫ ∈ ℤ}`; prove `L*` is itself a full `ZLattice`, spanned by
the dual basis of any `ℤ`-basis of `L`, and `(L*)* = L`; `(ℤ^d)* = ℤ^d`.
*Size S.* Deps: none (Mathlib `ZLattice`, `Basis.dualBasis`,
`BilinForm.dualBasis`). Sketch: express membership in coordinates of a `ℤ`-basis;
dual basis = Gram-matrix-inverse combinations.

**A2. Dual covolume.** `ZLattice.covolume L* = (ZLattice.covolume L)⁻¹`.
*Size S.* Deps: A1 (Mathlib `ZLattice.covolume`, `Zspan` fundamental-domain volume,
`Matrix.det` of inverse). Sketch: covolume² = det Gram; Gram matrix of the dual
basis is the inverse Gram matrix.

**A3. Poisson summation on `ℤ^d`.** For `f : 𝓢(ℝ^d, ℂ)` a Schwartz function (state
for `EuclideanSpace ℝ (Fin d)`; a corollary form with explicit
continuity + `rpow`-decay hypotheses on `f` and `𝓕f` mirroring the 1-D
`Real.tsum_eq_tsum_fourier_of_rpow_decay` is optional):
`∑_{m ∈ ℤ^d} f m = ∑_{k ∈ ℤ^d} 𝓕f k`.
*Size M.* Deps: none (Mathlib `UnitAddTorus.hasSum_mFourier_series_of_summable` and
`mFourierCoeff` from `Mathlib.Analysis.Fourier.AddCircleMulti`;
`SchwartzMap.decay`, `Real.fourierIntegral`). Sketch: periodize
`F x = ∑_m f (x + m)`, show `mFourierCoeff F k = 𝓕f k` by unfolding the integral
over the torus against the fundamental cube (the multivariate analogue of
`Real.fourierCoeff_tsum_comp_add`), then evaluate the uniformly convergent Fourier
series at `x = 0`; summability of coefficients from Schwartz decay of `𝓕f`.

**A4. Poisson summation over a lattice.** For a full lattice `L` in a
`d`-dimensional real inner-product space and Schwartz `f`:
`∑_{v ∈ L} f v = (ZLattice.covolume L)⁻¹ · ∑_{ξ ∈ L*} 𝓕f ξ`.
*Size S.* Deps: A1, A2, A3 (Mathlib `MeasureTheory.integral_comp_linearMap` /
Jacobian change of variables, `SchwartzMap.compCLM`). Sketch: write `L = B(ℤ^d)`
for `B ∈ GL_d`, apply A3 to `f ∘ B`; `𝓕(f∘B) = |det B|⁻¹ · (𝓕f) ∘ B⁻ᵀ` and
`B⁻ᵀ(ℤ^d) = L*`, `|det B| = covolume L`.

**A5. Anisotropic Gaussian and its Fourier transform.** For `y ∈ Y` define
`gauss_y : E_K → ℂ`, `gauss_y x = exp(−π ∑_v n_v y_v ‖x_v‖²)` (real places
`‖x_v‖² = x_v²`, complex places `‖x_v‖² = |z_v|²`). Prove: `gauss_y` is a
`SchwartzMap`, and `𝓕(gauss_y) = (∏_v (n_v y_v)^{−n_v/2}) · gauss_{y⁻¹-adjusted}`
(each real factor contributes `y_v^{−1/2}`, each complex factor `(2y_v)^{−1}`, with
the reciprocal parameter in the dual variable; fix the exact constant in the node's
own statement, it is forced by the 1-D computation).
*Size S.* Deps: none (Mathlib `fourierIntegral_gaussian_pi`,
`fourier_gaussian_innerProductSpace'`, product structure of `E_K`). Sketch: the
function is a product over places, so the transform factorizes into 1-D (real
place) and 2-D (complex place, `ℂ ≅ ℝ²`) standard Gaussian transforms.

### Part B — Number-field lattices and trace duality

**B1. Trace pairing vs the mixed-space pairing.** For `α β : K`:
`Trace_{K/ℚ}(α*β) = B(ι α, ι β)` where `ι = mixedEmbedding K` and `B` is the
explicit bilinear form on `E_K`: `∑_{real} x_v y_v + ∑_{complex} 2·Re(z_v w_v)`
(no conjugation — `B` is bilinear, not sesquilinear).
*Size S.* Deps: none (Mathlib `Algebra.trace_eq_sum_embeddings`,
`NumberField.InfinitePlace` embedding/conjugate-pair API). Sketch: group the `n`
complex embeddings into `r₁` real ones and `r₂` conjugate pairs; each pair
contributes `σα·σβ + conj(σα·σβ) = 2Re`.

**B2. Dual of the ideal lattice is the codifferent lattice.** For a nonzero
fractional ideal `I`, the A1-dual of the lattice `ι(I) ⊂ E_K` — taken w.r.t. the
pairing `B` of B1 (relate `B` to the Euclidean inner product via the conjugation
involution `c : E_K ≃ E_K`, which is an isometry fixing `ι(K)`-sums) — equals
`ι((I·𝔡)⁻¹)` up to `c`; consequently for any `c`-symmetric summand (all our
Gaussians), Poisson-dual sums over `ι(I)*` are sums over `ι((I𝔡)⁻¹)`.
*Size M.* Deps: A1, B1 (Mathlib `FractionalIdeal.dual`, `differentIdeal`,
`coeIdeal_differentIdeal`-family in `Mathlib.RingTheory.DedekindDomain.Different`).
Sketch: `x ∈ ι(I)*` iff `Trace(x̃ α) ∈ ℤ` for all `α ∈ I` iff
`x̃ ∈ FractionalIdeal.dual … I = (I·𝔡)⁻¹` (that identity is essentially Mathlib's
`dual` API); the only genuine work is the `ℝ`-linear-density step from `ι(I)`-span
to `E_K` and the conjugation bookkeeping at complex places.

**B3. Covolume of the ideal lattice.** W.r.t. the Euclidean (`WithLp 2`) volume on
`E_K`: `ZLattice.covolume (ι(I)) = 2^{−r₂} · √|d_K| · N(I)`.
*Size S.* Deps: none (Mathlib
`NumberField.mixedEmbedding.volume_fundamentalDomain_fractionalIdealLatticeBasis`,
`ZLattice.covolume_eq_measure_fundamentalDomain`, the measure-comparison lemmas
between the product volume and the Euclidean volume already in
`CanonicalEmbedding/Basic|ConvexBody`). Sketch: cite the existing volume formula
and convert measures; the `2^{−r₂}` is the standard `ℂ ≅ ℝ²` normalization factor.

### Part C — Hecke theta series and its transformation law

**C1. Theta series: definition and convergence.** For nonzero fractional `I` and
`y ∈ Y`, define `θ_I y := ∑_{α ∈ I} gauss_y (ι α)` (note: **full** lattice sum,
including `α = 0`). Prove: absolute convergence, `θ_I y ≥ 1`, continuity in `y`,
and the tail bound `θ_I y − 1 ≤ C_I(y₀) · exp(−π λ min_v y_v)` locally uniformly.
*Size S.* Deps: A5 (Mathlib `Mathlib.Algebra.Module.ZLattice.Summable`
`tsumNormRPowBound`-family, or directly Gaussian-vs-norm comparison). Sketch:
Gaussian dominates any inverse power of the norm; lattice points have norms bounded
below off `0`.

**C2. Theta transformation law.** For nonzero fractional `I` and `y ∈ Y`:
`θ_I (y⁻¹) = (∏_v (n_v y_v)^{n_v/2} · 2^{r₂-adjust}) · (√|d_K| · N I)⁻¹ · θ_{(I𝔡)⁻¹} (y)`
(one clean monomial in `y` times a constant; fix the exact constant from
A5 + B3 inside the node — it must reduce to `y^{1/2}·(√|d| N I)⁻¹·θ'` after the
norm-one restriction in E2).
*Size M.* Deps: A4, A5, B2, B3, C1. Sketch: apply lattice Poisson (A4) to
`f = gauss_{y⁻¹}` and `L = ι(I)`; the transform is a constant times `gauss_y` (A5),
the dual lattice is the codifferent lattice (B2), the covolume is B3; pure
bookkeeping after that.

**C3. Unit rescaling invariance.** Units act on `Y` by
`(u • y)_v = w_v(u)² · y_v` (where `w_v(u) = normAtPlace v (ι u)`); then for every
unit `u` and nonzero fractional `I`: `θ_I (u • y) = θ_I y`.
*Size S.* Deps: C1 (Mathlib `NumberField.mixedEmbedding.normAtPlace` mul lemmas,
`unit_smul` API from `CanonicalEmbedding/FundamentalCone.lean`). Sketch:
reindex the sum by the bijection `α ↦ u⁻¹α` of `I`; `‖ι(u⁻¹α)_v‖² · w_v(u)² =
‖ι(α)_v‖²`.

### Part D — Unit fundamental domain in parameter space

**D1. Polar decomposition of the parameter space.** Define the norm map
`Nm : Y → (0,∞)`, `Nm y = ∏_v y_v^{n_v}`, the norm-one surface
`S := Nm⁻¹ {1}`, and a measure-preserving homeomorphism
`Y ≅ (0,∞) × S`, `y = t^{1/n} • s` (isotropic scaling), carrying the multiplicative
Haar measure `⊗_v dy_v/y_v` to `(dt/t) ⊗ μ_S` for a (choice of) Haar measure `μ_S`
on `S`; `μ_S` is invariant under the multiplicative action of `S` on itself and
under `s ↦ s⁻¹`.
*Size M.* Deps: none (Mathlib `expMap`/`logSpace` machinery in
`CanonicalEmbedding/NormLeOne.lean` (Roblot), pushforward of Haar under the log
iso `Y ≅ ℝ^{r₁+r₂}`, product measure splitting along the linear map
`x ↦ (∑ n_v x_v, x − mean)`). Sketch: everything is transported along `log` to a
linear direct-sum decomposition `ℝ^{r₁+r₂} = ℝ·(1,…,1)-weighted ⊕ (trace-zero
hyperplane)` of Lebesgue measures.

**D2. Fundamental domain for units on the norm-one surface.** The unit action of
C3 restricted to `S` factors through `unitLattice K` (units mod torsion, via
`logEmbedding`); the `exp`-transport of a fundamental parallelepiped
(`Zspan.fundamentalDomain`) of the (doubled) unit lattice is a **bounded**,
measurable `F ⊂ S` with `MeasureTheory.IsAddFundamentalDomain` (transported to the
multiplicative action) and `0 < μ_S F =: V < ∞` (the value of `V` — a
`2`-power times `regulator K` — may be recorded but is *not needed* on the critical
path; only `0 < V < ∞` is).
*Size M.* Deps: D1 (Mathlib `NumberField.Units.unitLattice`,
`unitLattice_rank` (Dirichlet), `Zspan.isAddFundamentalDomain`,
`ZLattice.covolume`, `regulator`). Sketch: full-rank lattice in the trace-zero
hyperplane ⇒ its fundamental parallelepiped is a bounded fundamental domain;
transport along the measure-preserving `exp` of D1.

**D3. Inversion symmetry.** `s ↦ s⁻¹` preserves `S` and `μ_S`, conjugates the unit
action (`u • s ↦ u⁻¹ • s⁻¹`), and hence maps the fundamental domain `F` to another
fundamental domain `F⁻¹` for the *same* action; consequently, for any
action-invariant integrable `φ : S → ℂ`: `∫_{F} φ = ∫_{F⁻¹} φ = ∫_F (φ ∘ (·⁻¹))`
provided `φ` is also inversion-invariant-composable as stated.
*Size S.* Deps: D1, D2 (Mathlib `IsFundamentalDomain` API: two fundamental domains
give equal integrals of invariant functions —
`IsFundamentalDomain.setLIntegral_eq` / `.integral_eq`). Sketch: direct from the
quotient-integral characterization.

### Part E — The one-variable kernel and its functional equation

**E1. Kernel definition, integrability, decay.** Define
`g_I : (0,∞) → ℂ`, `g_I t := ∫_{F} θ_I (t^{1/n} • s) dμ_S s`. Prove: `g_I` is
locally integrable on `(0,∞)` (continuous, in fact), and for every `r`:
`(g_I · − V) =O[atTop] (·^r)` (rapid decay to the constant term `V = μ_S F`).
*Size M.* Deps: C1, D1, D2. Sketch: `θ_I − 1` has a locally-uniform Gaussian tail
(C1); `F` is bounded with `inf_{s∈F̄, v} s_v > 0`, so
`∫_F (θ_I(t^{1/n}s) − 1) ≤ V·C·exp(−c t^{1/n})`; the constant term integrates to
`t`-independent `V`.

**E2. Kernel functional equation.** For every nonzero fractional `I` and `t > 0`:
`g_I (1/t) = (√|d_K| · N I)⁻¹ · t^{1/2} · g_{(I𝔡)⁻¹} t`.
*Size M.* Deps: C2, C3, D1, D3, E1. Sketch: substitute the theta transformation
(C2) pointwise under the integral at parameter `(1/t)^{1/n} • s`; the monomial
`∏ (n_v y_v)^{n_v/2}`-factor evaluates on the norm-one surface to `t^{1/2}` times an
`s`-independent constant (since `∏_v s_v^{n_v} = 1`); the substitution `s ↦ s⁻¹`
maps `F` to `F⁻¹`, and D3 + C3 (theta is unit-invariant in `y`) bring the integral
back to `F`. This node is the heart of the proof; everything in it is a
change-of-variables once C2/C3/D3 exist.

### Part F — Mellin unfolding: identify the kernel with partial zeta (Re s > 1)

**F1. Partial zeta functions.** For an ideal class `A`, define
`ζ(A, s) := ∑_{𝔟 integral, [𝔟] = A} (N 𝔟)^{−s}`; prove absolute convergence and
analyticity on `Re s > 1`, `∑_{A} ζ(A, s) = dedekindZeta K s` there (reindexing the
`LSeries` over `n : ℕ` counting ideals of norm `n`, which is literally the
definition `NumberField.dedekindZeta`), and each `ζ(A,·)` is `O(ζ(Re s))`.
*Size S.* Deps: none (Mathlib `NumberField.dedekindZeta`
(`Mathlib.NumberTheory.NumberField.DedekindZeta`), `LSeries` summability API,
`Ideal.tendsto_norm_le_div_atTop₀` for crude counting, `tsum` sigma-type
reindexing). Sketch: absolutely convergent rearrangement over the fibration
ideals → (norm, ideals of that norm).

**F2a. Archimedean Gamma integrals.** The two 1-D building blocks, in Deligne
normalization: for `c > 0` and `Re s > 0`,
`∫₀^∞ e^{−π y c} y^{s/2} dy/y = Gammaℝ s · c^{−s/2}` (real place) and
`∫₀^∞ e^{−2π y c} y^{s} dy/y = (1/2)·Gammaℂ s · c^{−s} · (2π-factor fixed by the
node)` (complex place; pin the constant against `Gammaℂ_def`).
*Size S.* Deps: none (Mathlib `Complex.Gamma_eq_integral` /
`Real.Gamma_eq_integral`, `mellin` substitution lemmas
(`Mathlib.Analysis.MellinTransform`), `Gammaℝ_def`, `Gammaℂ_def`). Sketch:
substitute `u = π c y` in the Euler integral.

**F2b. Single-point unfolded integral.** For `x : E_K` with all
`normAtPlace v x ≠ 0` and `Re s > 0`:
`∫₀^∞ ∫_Y-unfolded gauss-integrand … = Gammaℝ(s)^{r₁} · Gammaℂ(s)^{r₂-normalized} ·
|mixedEmbedding.norm x|^{−s}` — precisely: the integral of
`t^{s/2} · gauss_{t^{1/n} • y-full-space}` over `(0,∞) × Y`-in-polar-coordinates
factorizes over places into F2a integrals. State it as: `∫_{Y} Nm(y)^{s/2}
exp(−π ∑ n_v y_v ‖x_v‖²) dμ_Y(y) = (Γ-monomial as above) · ∏_v ‖x_v‖^{−n_v s}`.
*Size M.* Deps: D1, F2a. Sketch: `μ_Y` is a product measure and the integrand is a
product over places; Tonelli + F2a per coordinate; then D1 converts the
`(0,∞) × S`-form used in F3b to this full-`Y` form.

**F3a. Unit-orbit ↔ ideal bijection.** For nonzero fractional `I`: the map
`α ↦ (α)·I⁻¹` induces a bijection `(I ∖ {0}) / (𝓞_K)ˣ ≃ {𝔟 integral ideal :
[𝔟] = [I]⁻¹}`, and each orbit, counted with the torsion, has exactly `w` elements
mapping to a given point of a torsion-free section; moreover
`|Norm_{K/ℚ} α| = N((α)I⁻¹) · N(I)`.
*Size S.* Deps: none (Mathlib `ClassGroup`, `Ideal.span_singleton`,
`FractionalIdeal` arithmetic; the pattern exists for `I = 𝓞` in
`fundamentalCone.integerSet` / `idealSetEquivNorm`,
`Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone`). Sketch:
pure ideal arithmetic; two elements generate the same `(α)I⁻¹` iff they differ by
a unit.

**F3b. Mellin of the kernel = completed partial zeta (Re s > 1).** For `Re s > 1`:
`∫₀^∞ (g_I t − V) t^{s/2} dt/t = w⁻¹ · (constant from D1/D2 unfolding) ·
Gammaℝ(s)^{r₁} Gammaℂ(s)^{r₂} · N(I)^{s} · ζ([I]⁻¹, s)`
(fix the exact constant — a `2`-power — inside the node; it cancels in the final
FE and only feeds the optional residue node H1).
*Size M.* Deps: C1, C3, D1, D2, E1, F1, F2b, F3a. Sketch: Tonelli (everything
positive after subtracting the `α = 0` term, which produced `V`); unfold
`∫_{(0,∞)} ∫_F ∑_{α ≠ 0}` to `∑_{orbits} ∫_{(0,∞) × S-full}` using
`IsFundamentalDomain.integral_eq_tsum` for the unit action (D2) and theta's unit
invariance (C3); evaluate each orbit integral by F2b; convert
`∏‖ι(α)_v‖^{n_v} = |Norm α|` and apply F3a.

### Part G — Assembly: continuation and the functional equation

**G1. WeakFEPair packaging.** For each nonzero fractional `I`, the pair
`f = g_I`, `g = g_{(I𝔡)⁻¹}`, `k = 1/2`, `ε = (√|d_K| · N I)⁻¹-normalized`,
`f₀ = g₀ = V` is a `WeakFEPair ℂ` (fields: `hf_int/hg_int` from E1, `h_feq` from
E2 — note E2 applied to `(I𝔡)⁻¹` gives the symmetric law with the reciprocal
constant, matching `WeakFEPair.h_feq'` — decay from E1). Obtain from Mathlib:
`P_I.Λ` meromorphic on `ℂ`, entire away from `{0, 1/2}`, simple poles there with
residues given by `WeakFEPair.Λ_residue_zero/…_k`, and
`P_I.Λ (1/2 − w) = ε · P_I.symm.Λ w`.
*Size S.* Deps: E1, E2 (Mathlib `WeakFEPair`, `WeakFEPair.functional_equation`,
`WeakFEPair.differentiableAt_Λ`, `WeakFEPair.Λ_residue_k`,
`Mathlib.NumberTheory.LSeries.AbstractFuncEq`). Sketch: verify the seven structure
fields; all are direct citations of E1/E2.

**G2. Completed partial zeta.** Define
`Λ(A, s) := |d_K|^{s/2} · Gammaℝ(s)^{r₁} · Gammaℂ(s)^{r₂} · ζ(A, s)` on
`Re s > 1` and prove: `Λ(A, ·)` extends to a meromorphic function on `ℂ` (namely
a constant times `P_I.Λ (s/2)` for any representative `I` with `[I]⁻¹ = A`, by
F3b + uniqueness of analytic continuation), holomorphic away from `{0, 1}`, simple
poles at `0, 1`, and the functional equation
`Λ(A, 1 − s) = Λ(A*, s)` where `A* := ([𝔡] · A)⁻¹`-type involution (fix the exact
involution from E2's `I ↦ (I𝔡)⁻¹` and F3a's `[I] ↦ [I]⁻¹`; note `A ↦ A*` is an
involution of the class group).
*Size S.* Deps: F3b, G1 (Mathlib identity theorem
`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` or `eqOn` API). Sketch:
F3b says the two sides agree on `Re s > 1`; G1 transports continuation, poles and
FE through the reparametrization `s ↦ s/2` (which sends `{0, 1/2}` to `{0, 1}`);
the `N(I)^{s}` and `|d|^{s/2}` monomials are entire and nonvanishing.

**G3. Completed Dedekind zeta and its functional equation.** Define
`completedDedekindZeta K s := ∑_{A : ClassGroup} Λ(A, s)` (a finite sum). Prove:
meromorphic on `ℂ`, holomorphic away from `{0, 1}`, simple poles at `0` and `1`,
equal to `|d_K|^{s/2} Gammaℝ(s)^{r₁} Gammaℂ(s)^{r₂} · dedekindZeta K s` on
`Re s > 1` (via F1), and
**`completedDedekindZeta K s = completedDedekindZeta K (1 − s)`** — reindex the
finite sum along the involution `A ↦ A*` of G2.
*Size S.* Deps: F1, G2. Sketch: finite sums of meromorphic functions; the FE is a
bijective reindexing; simplicity of the poles: each summand has at most simple
poles at `0,1` and the residues (all positive multiples of `V`) cannot cancel.

**G4. Continuation of `dedekindZeta` itself.** Produce
`dedekindZetaExt K : ℂ → ℂ` with: `dedekindZetaExt = dedekindZeta` on `Re s > 1`;
analytic on `ℂ ∖ {1}`; simple pole at `1` (nonzero residue); and the `ζ`-form FE
relating `dedekindZetaExt (1−s)` to `dedekindZetaExt s` with the explicit
`Gammaℝ/Gammaℂ/|d|`-quotient. Division by the Gamma monomial is legitimate:
`(Gammaℝ)⁻¹, (Gammaℂ)⁻¹` are entire (`differentiable_Gammaℝ_inv`,
`differentiable_Gammaℂ_inv`); trivial-zero bookkeeping at nonpositive integers
comes free and should be stated (`ζ_K` vanishes where the Gamma monomial poles
force it — record as a lemma, the Odlyzko chapter's M3 wants it).
*Size S.* Deps: G3 (Mathlib `Gammaℝ_eq_zero_iff`, `Gammaℝ_ne_zero_of_re_pos`,
`Gammaℝ_residue_zero`, Deligne file). Sketch:
`dedekindZetaExt s := completedDedekindZeta K s / (|d|^{s/2} Γ-monomial)`; pole/zero
analysis is pointwise from the Deligne-file lemmas.

**G5. M2 interface freeze (consumer-facing statement pack).** One file exporting
exactly what `cartography/odlyzko-reconciled.md` M2 promises downstream (M3–M7):
`completedDedekindZeta` meromorphic with simple poles exactly `{0,1}`;
`Λ_K(s) = Λ_K(1−s)`; agreement with `NumberField.dedekindZeta` on `Re s > 1`;
`Λ_K` real and positive on `(1, ∞)` (hence real on `ℝ` by the reflection);
nonvanishing of `Λ_K` on `Re s > 1` **stated as depending on** the Euler-product
node M1 of the parent map (cross-reference, not proved here). No new mathematics:
statement curation + the PQ4 normalization freeze.
*Size S.* Deps: G3, G4. Sketch: restatements.

### Optional (off the critical path)

**H1. Residue identification.** Residue of `completedDedekindZeta` at `s = 1`
equals the G1/G2 constants times `V`; matching against Roblot's
`NumberField.dedekindZeta_residue` (`tendsto_sub_one_mul_dedekindZeta_nhdsGT`)
re-proves the analytic class number formula and is a strong end-to-end
consistency check of every constant in A5/B3/C2/D2/F3b — recommended as a
verification bead, not needed by the Odlyzko chapter (which uses only pole
positions and simplicity).
*Size M.* Deps: D2 (value of `V` via `regulator`), F3b, G3.

## Dependency graph (edges point from prerequisite to dependent)

```
A1 ─┬─ A2 ─┐
    │      ├─ A4 ─┐
A3 ─┴──────┘      │
A5 ────────┬──────┼─ C2 ─┐
B1 ─ B2 ───┤      │      │
B3 ────────┴──────┘      │
C1 ─┬─ C3 ───────────────┼───────────┐
    │                    │           │
D1 ─┬─ D2 ─┬─ D3 ────────┼─ E2 ─┐    │
    │      └─ E1 ────────┘      ├─ G1 ─┐
    │           │               │      │
    │           └───────────────┼──────┼─ F3b ─┐
F1 ─┼───────────────────────────┼──────┼───────┤
F2a ┴─ F2b ─────────────────────┼──────┼───────┤
F3a ────────────────────────────┼──────┼───────┘
                                │      └─ G2 ─ G3 ─┬─ G4 ─ G5
                                │                  └─ (H1)
```

Topological order (one valid schedule):
A1, A3, A5, B1, F2a, F3a, F1, D1 → A2, B2, B3, C1, D2 → A4, C3, D3, E1, F2b →
C2 → E2 → G1, F3b → G2 → G3 → G4 → G5 (→ H1).

**Deepest chain (9 nodes):** A1 → B2 → C2 → E2 → G1 → G2 → G3 → G4 → G5
(equivalently A3 → A4 → C2 → …).

## Node count and parallelism

- **24 core nodes: 15 S + 9 M** (plus optional H1, M). No L, no XL.
- Maximal first wave (no dependencies, all provable today): **A1, A3, A5, B1,
  F2a, F3a, F1, D1** — eight independent sessions.
- The three closest to provable-today, in recommended priority order:
  1. **A3** (Poisson on `ℤ^d`) — the single most load-bearing prerequisite;
     `AddCircleMulti` was built for it; upstreamable to Mathlib immediately.
  2. **A1** (dual lattice) — small, self-contained, unlocks the whole B/C column;
     also independently wanted by Mathlib.
  3. **F2a** (Deligne-normalized Gamma integrals) — pure 1-D Euler-integral
     substitutions against `Gammaℝ_def`/`Gammaℂ_def`.
- Everything in Part A (and A-alone) is Mathlib-generic and should be PR'd
  upstream early; Parts B–D are Mathlib-`NumberField`-generic; only E–G are
  FE-specific. Coordinate with Mathlib maintainers (D. Loeffler, X. Roblot,
  M. Stoll) and with the AINTLIB / lean-pool authors (C. Birkbeck; the lean-pool
  Odlyzko effort is FLT-adjacent already) before starting A3/A4 and B2 — prior
  art exists for essentially every node in Parts A–C (see Prior art above), so
  the expected mode for those nodes is *port + upstream*, not prove-from-scratch.

## Risk notes (kept short; each is contained in one node)

- **Constant bookkeeping (A5/B3/C2/F3b):** the `2`-powers from `ℂ ≅ ℝ²` are the
  classical error-magnet. Mitigation: each node fixes its own constant in its
  statement, and H1 provides an end-to-end numerical check against Roblot's
  independently-proved residue.
- **Conjugation twist in B2:** the trace pairing is bilinear, the inner product
  sesquilinear-shaped at complex places; the involution `c` must be carried
  explicitly. Contained in B2's statement.
- **Measure plumbing in D1:** transporting Haar through `exp`/polar coordinates is
  routine but fiddly; Roblot's `expMap`/`NormLeOne` machinery already does the
  hard half for the class-number formula, and D1 should reuse it aggressively.
- **`WeakFEPair` hypothesis mismatch:** the engine wants `f(1/x) = ε x^k g x`
  exactly; E2's constant must be pushed into `ε` (allowed: `ε` need not be
  unimodular) — checked against the structure fields, which permit arbitrary
  nonzero `ε ∈ ℂ`.
