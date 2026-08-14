# Odlyzko M3 — zero theory for Λ_K — S/M decomposition (hub-lsb1u.6.14)

Target: node **M3** of `cartography/odlyzko-reconciled.md` — "strip zeros and
horizontal estimates": the zero-counting / argument-principle machinery the
Weil–Poitou explicit formula (M4–M7) consumes. This file breaks that XL wall into
a dependency-ordered tree in which **every node is S or M**, at the same rigor
standard as `cartography/zeta-fe-decomposition.md` (the M2 tree): named Mathlib
anchors, one-line sketches, dependency order.

Mathlib declaration names below were verified two ways: by direct grep of the FLT
repo's pinned Mathlib (`.lake/packages/mathlib`, manifest rev `bc06ce9f…`) and,
where noted, against the mathlib4 docs website (checked 2026-08). This resolves
the two uncited hidden edges flagged by `cartography/panel/odlyzko-dependency.md`:

- **Borel–Carathéodory (M8/M3 hidden edge): PRESENT in Mathlib.**
  `Complex.borelCaratheodory` and `Complex.borelCaratheodory_zero` in
  `Mathlib.Analysis.Complex.BorelCaratheodory` (in the pinned rev). It is a
  first-class node below (N5) together with its Landau-lemma application (N7).
- **Digamma (M6 hidden edge): PRESENT in Mathlib.** `Complex.digamma`
  (`:= logDeriv Gamma`), `digamma_apply_add_one`, `digamma_one`,
  `digamma_one_half`, `meromorphic_digamma` in
  `Mathlib.Analysis.SpecialFunctions.Gamma.Digamma` (in the pinned rev). The
  strip *bound* on digamma is not in Mathlib and is node N4.
- **Zero-spacing (M3→M4 hidden edge):** first-class node N15 below.

Two further discoveries that shape the whole route (both verified in the pinned
rev and on the docs site): **Jensen's formula and Jensen's zero-counting
inequality are now in Mathlib** (`MeromorphicOn.circleAverage_log_norm`,
`AnalyticOnNhd.sum_divisor_le` in `Mathlib.Analysis.Complex.JensenFormula`,
plus the `MeromorphicOn.divisor` infrastructure in `Mathlib.Analysis.Meromorphic.*`),
and `Mathlib.NumberTheory.LSeries.ZetaZeros` is a ready template for the
discreteness node (N12). `Mathlib.Analysis.Complex.Hadamard` is the **three-lines
theorem**, not Hadamard factorization; no factorization exists in Mathlib.

## Route choice: soft Landau–Backlund local zero theory (no Hadamard product)

**Chosen route: Jensen + Borel–Carathéodory local theory** — the classical
Landau/Backlund method (Titchmarsh §3.9/§9.2, Montgomery–Vaughan Lemma 6.1–6.4,
Iwaniec–Kowalski §5.3), *not* the Hadamard product for `s(s−1)Λ_K`.

Derivation of the minimum: Poitou, *Sur les petits discriminants* (Sém. DPP
1976/77, exp. 6), §2–3, consumes from zero theory exactly:

1. the multiset of nontrivial zeros, confined to `0 ≤ Re ρ ≤ 1`, with the
   symmetries `ρ ↦ 1−ρ`, `ρ ↦ conj ρ` (so the zero sum can be written over
   `Re Φ` and paired);
2. **absolute** convergence of `∑_ρ Φ_F(ρ)` for his test class (the Tartar
   function of M9 is even, compactly supported, Lipschitz with `F′` of bounded
   variation, so `Φ_F(ρ) = O((1+|Im ρ|)⁻²)` — no conditional
   `lim_{T} ∑_{|γ|<T}` machinery is needed if we freeze this class);
3. for the contour proof of the explicit formula (M4–M5): admissible heights
   `T_j → ∞` avoiding zeros by `≫ 1/log T_j`, and the bound
   `|logDeriv ζ_K| ≪ (log T_j)²` on the horizontal segments `−1 ≤ σ ≤ 2`.

Everything above follows from **unit-interval zero counting
`m_K(T) ≪_K log T`** plus a **partial-fraction approximation of
`logDeriv ζ_K` near height `T`** — both of which the Jensen + Borel–Carathéodory
method delivers directly from a polynomial growth bound on `ζ_K`. What is *not*
needed: the Hadamard/Weierstrass product over all zeros, genus-1 theory,
convergence of `∑ 1/ρ`, the Riemann–von Mangoldt asymptotic for `N_K(T)`, any
zero-free region, and any zero-density estimate. Since Mathlib has **no**
Hadamard factorization but **does** now have both engines of the soft route
(Jensen inequality, Borel–Carathéodory), the Hadamard route would add an
L-sized factorization crater for zero gain. One real cost is accepted and made
explicit: log-quality counting needs two-sided Stirling-type Γ-bounds in
vertical strips (absent from Mathlib — only real `Stirling` exists), which we
build in S/M steps from the exact reflection identities plus the three-lines
theorem (N2–N3); these nodes are shared with the parent map's M6.

Normalizations: as frozen in the M2 tree (`Gammaℝ/Gammaℂ` Deligne,
`Λ_K(s) = |d_K|^{s/2}·Gammaℝ(s)^{r₁}·Gammaℂ(s)^{r₂}·ζ_K(s)`); test-transform
`Φ_F(s) := ∫_ℝ F(x) e^{(s−1/2)x} dx` (Poitou/Weil convention; discharges the
M3-side of PQ4).

## Interface node to the M2/FE tree

**N1 is the single import node.** M3 consumes from the M2 tree (G-part) and M1:

- **G5/G3/G4** (M2 tree): `Λ_K` meromorphic on `ℂ`, simple poles exactly
  `{0,1}`; `Λ_K(s) = Λ_K(1−s)`; agreement
  `Λ_K = |d|^{s/2}·Γ-monomial·ζ_K` on `Re s > 1`; continuation
  `dedekindZetaExt`, analytic on `ℂ ∖ {1}`, and the trivial-zero bookkeeping
  lemma of G4 (which that node already earmarks for M3).
- **G1** (M2 tree), *one-lemma extension needed*: the symmetrized incomplete-Mellin
  representation behind `WeakFEPair.Λ` — i.e. a `T`-uniform strip bound for
  `ξ_K := s(s−1)Λ_K` (node N9 below). G5's export list should grow by this one
  S-sized growth lemma; flagged here rather than silently assumed.
- **M1** (parent map): Euler product ⇒ `ζ_K(s) ≠ 0` for `Re s > 1` together with
  the two-sided factor bounds used in N8. (Mathlib anchors:
  `NumberField.dedekindZeta`, `Mathlib.NumberTheory.EulerProduct.Basic/ExpLog`;
  Roblot's in-flight summability PR #42567 feeds M1, not this tree.)

Nothing else crosses the interface: M3 never looks inside theta functions, unit
domains, or class-group sums.

## Dependency tree

Notation: `n = [K:ℚ]`, `s = σ + it`, `ξ_K := s(s−1)Λ_K` (entire),
`ρ` ranges over zeros of `Λ_K` counted with multiplicity ("nontrivial zeros"),
`m_K(T) := #{ρ : |Im ρ − T| ≤ 1}`. Constants `C_K` may depend on `K` (they feed
the explicit formula, whose final inequality is per-field); `log`-savings in `n`
are *not* chased — Poitou needs no uniformity in `K` here.

### Part I — Interface

**N1. FE-interface import.** Statement pack importing exactly the items listed
in "Interface node" above (G5 + G4 + the G1 growth form + M1 nonvanishing); no
new mathematics beyond restating them in the forms used below.
*Size S.* Deps: M2-tree G1, G4, G5; parent M1. Sketch: statement curation; the
only content is the G5 export extension flagged above.

### Part GA — Gamma-factor strip estimates (shared with parent M6)

**N2. Exact modulus identities.** `‖Γ(1+it)‖² = π t / sinh (π t)` and
`‖Γ(1/2+it)‖² = π / cosh (π t)` for `t ≠ 0`.
*Size S.* Deps: none (Mathlib `Complex.Gamma_mul_Gamma_one_sub`
(`Mathlib.Analysis.SpecialFunctions.Gamma.Beta`), `Complex.Gamma_conj`,
`Complex.Gamma_add_one`, `Complex.sin` addition formulas). Sketch: reflection at
`s = it` and `s = 1/2 + it`; `Γ(conj s) = conj (Γ s)` turns the products into
squared moduli.

**N3. Two-sided vertical-strip Γ bounds.** For each strip `a ≤ σ ≤ b` there are
`c₁, c₂, A > 0` with
`c₁ e^{−π|t|/2}(1+|t|)^{−A} ≤ ‖Γ(σ+it)‖ ≤ c₂ e^{−π|t|/2}(1+|t|)^{A}` for
`|t| ≥ 1` (crude polynomial factors — the sharp `|t|^{σ−1/2}` is *not* needed
anywhere in this tree).
*Size M.* Deps: N2 (Mathlib
`Complex.HadamardThreeLines.norm_le_interpStrip_of_mem_verticalClosedStrip₀₁`
(`Mathlib.Analysis.Complex.Hadamard`), `Complex.Gamma_add_one`,
`Complex.Gamma_mul_Gamma_one_sub`). Sketch: normalize `Γ` by an elementary
entire factor of modulus `e^{π|t|/2}`-type, three-lines-interpolate the upper
bound between the two exact lines of N2, translate to `[a,b]` by the recurrence;
the lower bound is the upper bound for `Γ(1−s)` via reflection and
`‖sin π s‖ ≍ e^{π|t|}`.

**N4. Digamma strip bound (discharges the M6 hidden edge).** For `a ≤ σ ≤ b`,
`|t| ≥ 1`: `‖Complex.digamma (σ+it)‖ ≤ C(a,b) · log (2+|t|)`; plus the
Deligne-normalized forms `logDeriv Gammaℝ s = (−Real.log π + digamma (s/2))/2`
and `logDeriv Gammaℂ s = −Real.log (2π) + digamma s`.
*Size M.* Deps: N3 (Mathlib `Complex.digamma`, `Complex.digamma_def`,
`Complex.meromorphic_digamma`, `Complex.digamma_apply_add_one`
(`Mathlib.Analysis.SpecialFunctions.Gamma.Digamma` — present in the pinned rev),
`Complex.borelCaratheodory`, `Gammaℝ_def`/`Gammaℂ_def` (Deligne file)).
Sketch: on the disk `‖s − (σ+it)‖ ≤ 2`, `h := log Γ − (iπ/2)·sign(t)·s` (branch
via N6) has `Re h = log ‖Γ‖ + π|t|/2 ∈ O(log |t|)` two-sidedly by N3;
Borel–Carathéodory bounds `‖h‖`, Cauchy's estimate bounds `h′ = digamma − const`.

### Part BC — Borel–Carathéodory / Landau kernel (discharges the M8 hidden edge)

**N5. Borel–Carathéodory, off-center form.** For `f` analytic on
`ball c R`, `0 < r < R`: `sup_{ball c r} ‖f‖ ≤ (2r/(R−r))·sup_{ball c R} (Re f)
+ ((R+r)/(R−r))·‖f c‖`-type bound.
*Size S.* Deps: none — **the theorem itself is `Complex.borelCaratheodory` /
`Complex.borelCaratheodory_zero` in `Mathlib.Analysis.Complex.BorelCaratheodory`**
(pinned rev; stated on `ball 0 R`). Sketch: translate/rescale the Mathlib
statement; pure API glue.

**N6. Holomorphic logarithm on a disk.** If `f` is analytic and nonvanishing on
`ball c R` then there is an analytic `L` with `exp ∘ L = f`, `Re L = log ‖f‖`,
`L′ = logDeriv f`.
*Size S.* Deps: none (Mathlib `DifferentiableOn.isExactOn_ball` — Morera/
primitives, `Mathlib.Analysis.Complex.HasPrimitives`; `Complex.exp_log`,
`logDeriv` API). Sketch: `L` := primitive of `f′/f` (exists on a disk) plus a
constant; `f·exp(−L)` has zero derivative, hence is constant `1`.

**N7. Landau log-derivative lemma.** Let `f` be analytic on `ball c R` with
`f c ≠ 0` and `‖f‖ ≤ M` on the ball. Then (i) the number of zeros in
`ball c (R/2)` is `≤ C·log (M/‖f c‖)` and (ii) for `s ∈ ball c (R/4)`:
`logDeriv f s = ∑_{ρ ∈ ball c (R/2), f ρ = 0} 1/(s−ρ) + E s` with
`‖E s‖ ≤ C·log (M/‖f c‖) / R`.
*Size M.* Deps: N5, N6 (Mathlib `AnalyticOnNhd.sum_divisor_le` — **Jensen's
inequality, already the counting half (i)** — and
`MeromorphicOn.circleAverage_log_norm`, both in
`Mathlib.Analysis.Complex.JensenFormula`; `MeromorphicOn.divisor`
(`Mathlib.Analysis.Meromorphic.Divisor`)). Sketch: (i) is Mathlib's
`sum_divisor_le` verbatim; for (ii), `g := f / ∏_ρ (· − ρ)` is nonvanishing on a
slightly smaller ball, `Re log g` is bounded there by `O(log (M/‖f c‖))`
(maximum principle + the removed factors' size), N5 bounds `‖log g‖`, Cauchy's
estimate bounds `(log g)′ = E`. This node is the entire "zero-machinery kernel";
everything after it is bookkeeping.

### Part GR — Growth of `ζ_K`

**N8. Right-edge two-sided Euler bounds.** For `σ ≥ 2`:
`ζ(2)^{−n} ≤ ‖ζ_K s‖ ≤ ζ(2)^{n}`.
*Size S.* Deps: N1 (M1 part) (Mathlib `NumberField.dedekindZeta`,
`Mathlib.NumberTheory.EulerProduct.Basic/ExpLog`). Sketch: at most `n` Euler
factors over each rational prime `p`, each factor and its inverse bounded by
`(1 ± p^{−2})^{∓1}`.

**N9. A-priori strip control of `ξ_K`.** On each strip `a ≤ σ ≤ b`:
`‖ξ_K s‖ ≤ C_K(a,b) · (1+‖s‖)²` (uniform in `t`).
*Size S.* Deps: N1 (the G1/G5 growth-form export). Sketch: in the symmetrized
representation `Λ = ∫_1^∞ (g−V)(t)(t^{s/2} + ε t^{(1−s)/2}) dt/t + pole terms`,
bound `|t^{s/2}| ≤ t^{b/2}` and cite E1's decay; the `(1+‖s‖)²` is the
`s(s−1)` prefactor.

**N10. Left-edge polynomial bound.** For `|t| ≥ 1`:
`‖ζ_K (−1+it)‖ ≤ C_K (1+|t|)^{B₀(n)}`.
*Size S.* Deps: N1 (FE), N3, N8. Sketch: `ζ_K(−1+it)` = (Γ-monomial quotient) ·
`ζ_K(2−it)` by the FE; the quotient's exponential factors cancel by the
two-sided N3, leaving a polynomial; `ζ_K(2−it)` is N8.

**N11. Convexity bound on the strip.** For `−1 ≤ σ ≤ 2`, `|t| ≥ 1`:
`‖ζ_K (σ+it)‖ ≤ C_K (1+|t|)^{B(n)}`.
*Size M.* Deps: N3, N8, N9, N10 (Mathlib
`Complex.PhragmenLindelof.vertical_strip`
(`Mathlib.Analysis.Complex.PhragmenLindelof`), or alternatively the Hadamard
three-lines file). Sketch: apply Phragmén–Lindelöf on `−1 < σ < 2` to `ζ_K`
times an elementary polynomial normalizer killing the pole at `1`; the required
sub-double-exponential a-priori growth is N9 divided by N3's lower Γ bound
(`≤ e^{c_K |t|}`, admissible for `vertical_strip`).

### Part Z — Zero theory proper

**N12. Strip confinement, symmetries, discreteness.** All zeros of `Λ_K` lie in
`0 ≤ Re ρ ≤ 1`; the zero multiset is invariant under `ρ ↦ 1−ρ` and
`ρ ↦ conj ρ`; in the open strip they coincide (with multiplicity) with zeros of
`dedekindZetaExt`, and G4's trivial zeros are exactly the zeros outside; the
zero set is closed, discrete, and finite in every compact.
*Size S.* Deps: N1, N8 (Mathlib template: `riemannZetaZeros`,
`isClosed_riemannZetaZeros`, `isDiscrete_riemannZetaZeros`,
`IsCompact.inter_riemannZetaZeros_finite` in
`Mathlib.NumberTheory.LSeries.ZetaZeros` — port the proof pattern;
`Gammaℝ_ne_zero_of_re_pos`, `Complex.Gamma_conj`;
`AnalyticOnNhd.preimage_zero_mem_codiscreteWithin`). Sketch: no zeros in
`Re > 1` (N8 lower bound + nonvanishing Γ-monomial), none in `Re < 0` by the FE;
`conj`-symmetry from real Dirichlet coefficients + identity theorem;
discreteness verbatim as in `ZetaZeros.lean`.

**N13. Local zero counting.** `m_K(T) ≤ C_K · log (2+|T|)` for all `T`.
*Size M.* Deps: N7(i), N8, N11, N12. Sketch: Jensen counting (N7(i)) for
`f = dedekindZetaExt` on `ball (2+iT) 4` against the smaller ball of radius
`√10 < 4`: `log (M/‖f(2+iT)‖) ≤ B(n) log |T| + n log ζ(2)² = O_K(log T)` by
N11/N8; for `|T| ≥ 10` the ball avoids the pole `1` and all G4 trivial zeros;
finitely many small `|T|` absorbed into `C_K` by N12-compactness.

**N14. Convergence weights.** `∑_ρ 1/(1+(T−Im ρ)²) ≤ C_K log (2+|T|)` for every
`T`, and `∑_ρ (1+|Im ρ|)^{−2} < ∞`.
*Size S.* Deps: N13. Sketch: partition ordinates into unit intervals
`[T+k, T+k+1)`, bound each interval's population by N13, sum
`∑_k log(2+|T|+k)/(1+k²)`.

**N15. Zero-spacing / admissible heights (first-class; discharges the M3→M4
hidden edge).** For every `T₀ ≥ 10` there is `T ∈ [T₀, T₀+1]` with
`|Im ρ − T| ≥ c_K / log T₀` for **every** zero `ρ`; hence a strictly increasing
sequence of admissible heights `T_j → ∞`. This is the exact "contour legality"
fact M4's rectangle needs.
*Size S.* Deps: N13. Sketch: pigeonhole — at most `C_K log T₀` ordinates meet
`[T₀, T₀+1]`, so some gap has length `≥ 1/(2 C_K log T₀)`; take its midpoint.

**N16. Partial-fraction expansion of `logDeriv ζ_K`.** For `|t| ≥ 20` and
`−1 ≤ σ ≤ 2`:
`logDeriv (dedekindZetaExt K) (σ+it) = ∑_{|ρ−(2+it)| ≤ 4} 1/((σ+it)−ρ)
+ O_K(log |t|)`.
*Size M.* Deps: N7, N8, N11, N13. Sketch: Landau's lemma (N7) on
`ball (2+it) 16` (pole-free for `|t| ≥ 20`), `log (M/‖f c‖) = O_K(log t)` by
N11/N8; trim the N7 sum from radius `8` to radius `4` by N13 (each discarded
term is `O(1)`, there are `O_K(log t)` of them); `10 ≤ |t| ≤ 20` absorbed into
constants.

**N17. Horizontal-segment bounds at admissible heights.** For `T` admissible
(N15) and `−1 ≤ σ ≤ 2`:
`‖logDeriv (dedekindZetaExt K) (σ ± iT)‖ ≤ C_K (log T)²`, and via N18 the same
bound for `‖logDeriv Λ_K (σ ± iT)‖`. This is the estimate M4/M5 use to kill the
horizontal integrals as `T_j → ∞`.
*Size M.* Deps: N4, N15, N16, N18. Sketch: N16 has `O_K(log T)` summands, each
`≤ log T / c_K` by the N15 spacing; the Γ/digamma correction between `ζ_K` and
`Λ_K` is `O(log T)` by N4.

**N18. `Λ_K` log-derivative decomposition.** Away from poles and zeros:
`logDeriv Λ_K s = (1/2)·Real.log |d_K| + r₁ · logDeriv Gammaℝ s +
r₂ · logDeriv Gammaℂ s + logDeriv (dedekindZetaExt K) s`, with the digamma
forms of N4. (The prime-power Dirichlet series for `−logDeriv ζ_K` on
`Re s > 1` is the parent map's M5/M1 business, not M3's.)
*Size S.* Deps: N1, N4. Sketch: `logDeriv` of a product/`cpow` chain;
`logDeriv_mul`, `Complex.digamma_def`.

**N19. Test-function transform decay.** Freeze the Poitou class `𝓕`: `F` even,
compactly supported, Lipschitz, `F′` of bounded variation (M9's Tartar function
is in `𝓕`). For `F ∈ 𝓕`, `Φ_F(s) := ∫ F(x) e^{(s−1/2)x} dx` is entire and
`‖Φ_F(ρ)‖ ≤ C_F (1+|Im ρ|)^{−2}` uniformly on `0 ≤ Re ρ ≤ 1`. (Freezing `𝓕`
this way is what buys *absolute* convergence and dodges the conditional
symmetric-limit machinery of Weil's general formula — the minimal choice
sufficient for Poitou §2–3.)
*Size M.* Deps: none (Mathlib `intervalIntegral.integral_comp_smul_deriv`-family
for integration by parts, `BoundedVariationOn` / `StieltjesFunction` API,
`Complex.exp` bounds). Sketch: integrate by parts twice (once against Lipschitz
`F`, once against the Stieltjes measure `dF′`); `e^{(s−1/2)x}` is `≤ e^{|x|/2}`
on the closed strip and `x` ranges over a compact set.

**N20. Absolute convergence of the zero sum.** For `F ∈ 𝓕`:
`∑_ρ ‖Φ_F ρ‖ < ∞`, with the tail bound
`∑_{|Im ρ| > T} ‖Φ_F ρ‖ ≤ C_{K,F} (log T)/T`.
*Size S.* Deps: N14, N19. Sketch: combine N19's `(1+|γ|)^{−2}` decay with N14's
unit-interval counting; the tail is `∑_{k ≥ T} (log k)/k²`.

**N21. M3 interface freeze (exports to M4/M5/M7).** One file exporting exactly:
the zero multiset with symmetries and discreteness (N12), `m_K(T) ≪_K log T`
(N13), convergence weights (N14), admissible heights (N15), the partial-fraction
expansion (N16), horizontal bounds (N17), the `Λ` decomposition with digamma
forms (N18), and the frozen class `𝓕` with `Φ`-decay and absolute zero-sum
convergence (N19–N20). Freezes the M3-side of the reconciled map's PQ4.
*Size S.* Deps: N12–N20. Sketch: restatements; no new mathematics.

## Dependency graph (prerequisite → dependent)

```
N1 ──┬────────────────────────┬─ N8 ─┬───────────┐
     │                        │      │           │
N2 ─ N3 ─┬─ N4 ──────────┐    │      │           │
     │   └───────────────┼────┼─ N10 ┤           │
     │        N9 (← N1) ─┼────┴─ N11 ┼─ N13 ─┬─ N14 ─┬─ N20 ─┐
N5 ─┬─ N7 ───────────────┼──────────┬┘       ├─ N15 ─┼─ N17 ─┼─ N21
N6 ─┘                    │          └─ N16 ──┼───────┘       │
N1 ─── N12 ──────────────┼───────────────────┼───────────────┤
N1, N4 ─ N18 ────────────┴───────────────────┘ (→ N17, N21)  │
N19 ─────────────────────────────────────────────────── N20 ─┘
```

Topological order (one valid schedule):
N2, N5, N6, N19, N1 → N3, N7, N8, N9, N12 → N4, N10 → N11 → N13, N18 →
N14, N15, N16 → N17, N20 → N21.

**Deepest chain (8 nodes):** N2 → N3 → N10 → N11 → N13 → N16 → N17 → N21.

## Node count and parallelism

- **21 nodes: 13 S + 8 M.** No L, no XL (matching the M2 tree's discipline; the
  panel's demand that M3's XL be decomposed at M2-standard is hereby met).
- First wave (no deps beyond current Mathlib, provable today): **N2, N5, N6,
  N19** — four independent sessions. N1 needs only M2-tree statements to quote
  and can be drafted in parallel as `sorry`-parametrized hypotheses.
- The three closest to provable-today, in recommended priority order:
  1. **N2** (exact Γ modulus identities) — pure `Gamma_mul_Gamma_one_sub` +
     `Gamma_conj` computation; unlocks the whole GA column and is independently
     wanted by the parent M6.
  2. **N5** (off-center Borel–Carathéodory corollary) — API glue over the
     existing `Complex.borelCaratheodory`; unlocks the BC column (N7) and the
     parent M8's convexity input.
  3. **N19** (test-transform decay for the frozen class `𝓕`) — self-contained
     real/complex integration by parts; also pins the PQ4 test class, which M7,
     M8, M9 all consume.

## Risk notes (each contained in one node)

- **N3 is the only genuinely delicate analysis node** (Stirling-substitute):
  crude polynomial exponents keep it M, and nothing downstream needs sharp
  exponents — resist the temptation to prove `|t|^{σ−1/2}`.
- **N7's zero-removal bookkeeping** (dividing out finitely many zeros and
  bounding the quotient) is the classical fiddly step; Mathlib's
  `sum_divisor_le` + `MeromorphicOn.divisor` API remove most of the pain, and
  the node's radius constants (`R/2`, `R/4`) are fixed in its statement.
- **Pole/trivial-zero exclusion radii** in N13/N16 (`|T| ≥ 10`, `|t| ≥ 20`) are
  fixed in the statements; small heights are finite by N12 and absorbed into
  `C_K` — no hidden uniformity claims.
- **N19's class `𝓕` is a contract**: M9 must check Tartar's function into `𝓕`
  (Lipschitz + `F′` BV — true for `(1−|x|/y)`-type kernels). If M9 ever needs a
  discontinuous `F`, the zero sum becomes conditionally convergent and N20 must
  be redone with symmetric limits — flag at the M7 assembly if so.
