# Odlyzko chapter map — second independent pass (hub-lsb1u.6)

Cartographer B. Produced independently from the repo's `main` sources and the primary
literature only (Poitou 1976/77 read from the Numdam scan; page images, not OCR).
All numerics below were recomputed and checked against the scanned tables.

---

## 1. What exactly is assumed

### The Lean axiom

`FLT/Assumptions/Odlyzko.lean:58-60`:

```lean
axiom Odlyzko_statement (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
  (hdim : finrank ℚ K ≥ 18) : |(discr K : ℝ)| ≥ 8.25 ^ finrank ℚ K
```

i.e. **every totally complex number field of degree n ≥ 18 has root discriminant
rd(K) = |d_K|^{1/n} ≥ 8.25.** The docstring (`Odlyzko.lean:23-27`) cites Poitou,
"Sur les petits discriminants" (Sém. Delange–Pisot–Poitou 18, 1976/77, exp. 6):
"Equation 26 of the paper implies the below bound, and an explicit reference for it is
the table on p17 of the paper (in fact 8.25 can be beefed up to 9.3, but we do not
need this)." GitHub tracking issue: #458 (label `assumption`), which phrases it as:
a totally complex field with rd ≤ 2^{2/3}·3^{3/2} < 8.25 has degree < 18.

### Blueprint invocations (quoted)

- `blueprint/src/chapter/ch04overview.tex:106-108`: "Reducing mod 3 we get a
  representation which is flat at 3 and tame at 2, so must be reducible because of the
  techniques introduced in Fontaine's paper on abelian varieties over $\Z$ (an
  irreducible representation would cut out a number field whose **discriminant violates
  the Odlyzko bounds**)."
- `blueprint/src/chapter/ch03freyreduction.tex:272-274`: "this follows from old
  estimates of Fontaine (ultimately **relying on bounds for root discriminants due to
  Odlyzko and Poitou**), originally developed to prove that there was no nontrivial
  abelian scheme over $\Z$."

### Where it is consumed

Currently **nowhere**: the axiom is imported project-wide (`FLT.lean:5`) but no Lean
proof uses `Odlyzko_statement` yet (grep over `FLT/`). Its designated consumer is
`GaloisRepresentation.IsHardlyRamified.mod_three`
(`FLT/GaloisRepresentation/HardlyRamified/ModThree.lean:27`, currently `sorry`;
blueprint node `hardly_ramified_mod3_reducible`, `ch03freyreduction.tex:219-241`),
the Fontaine-style step: an irreducible hardly ramified mod-3 representation would cut
out a totally complex field, unramified outside {2,3}, tame at 2 with e₂ | 3, flat at
3, hence (tame bound at 2 + Fontaine's different bound at 3)

  rd(K) < 2^{(e₂−1)/e₂} · 3^{1+1/(3−1)} ≤ 2^{2/3} · 3^{3/2} = **8.24838…** < 8.25,

contradicting the axiom once the degree is ≥ 18 and K is totally complex (complex
conjugation acts with eigenvalues {1,−1}, so nontrivially). The degree-≥18 and
totally-complex hypotheses are **consumer-side obligations** (group theory of
irreducible subgroups of GL₂(𝔽₃) with anticyclotomic determinant; small-image cases
must be handled by class-field-theoretic arguments) — they belong to the ModThree
chapter, not this one.

### Weakest sufficient statement

> **(W)** There is no totally complex number field K with [K:ℚ] ≥ 18 and
> |d_K|^{1/[K:ℚ]} ≤ 2^{2/3}·3^{3/2} (= 8.24838…).

The axiom's 8.25 is exactly the cheapest round number above 2^{2/3}·3^{3/2}. Any
constant in the half-open window (8.24838, 9.305672] and any degree threshold in
{16, 17, 18, …} would do (see the table verdict below: Poitou certifies 8.748 already
at n = 16, but only 8.122 at n = 14, so 16 is the true threshold his table supports;
18 gives one row of slack). If the consumer's group theory can guarantee degree ≥ 19,
statement (W) weakens further to something provable by a single closed-form
inequality (node B13 below) with no finite-degree numerics at all.

### Numerical constant verdict (checked against the primary source)

I read Poitou's paper directly (Numdam scan, 18 pp.). Findings:

1. **The table on p. 17 ("6-17"), "Discriminants des corps totalement imaginaires",
   is unconditional** (it is produced by §4, "Minorations explicites **sans**
   hypothèse de Riemann", formulas (13)–(26); the GRH material is §3 and produces no
   table in this paper). Verified entries:
   n = 14: 8.122437; n = 16: **8.748418**; n = 18: **9.305672**; n = 20: 9.805700;
   asymptote γ + log 4π, i.e. rd → 4πe^γ = 22.3816….
   So **rd ≥ 8.25 at n = 18 is attainable GRH-free, with 12.8 % headroom
   (9.3057 vs 8.25)** — and the docstring's "can be beefed up to 9.3" is precisely the
   n = 18 table entry. No mismatch in the assumption itself.
2. **Uniformity over all n ≥ 18 is fine but needs one observation the paper doesn't
   make explicit.** The table optimizes the scaling parameter y per degree; the axiom
   quantifies over every n ≥ 18. Poitou's inequality (26) (p. "6-15"),
   (1/n)log|d| ≥ γ + log 4π + r₁/n − 12π/(5n√y) − L₁(y), is valid for **every** y > 0,
   and for fixed y its right side (r₁ = 0) is increasing in n. So a single evaluation
   at n = 18 with the n = 18-optimal y certifies ≥ 9.3057 simultaneously for all
   n ≥ 18. One test function, one interval-arithmetic computation — no per-degree
   table needed in Lean.
3. **Genuine tightness at exactly n = 18** (headline): Poitou's closed-form
   unconditional inequality (16) (Tartar's function, no finite-n numerics),
   (1/n)log|d| ≥ γ + log 4π − 6.860404·n^{−2/3} (totally complex case), gives
   rd ≥ 8.2432 at n = 18 — **below both 8.25 and 8.24838** — but 8.5399 at n = 19 and
   8.8210 at n = 20. So the cheap closed form misses the requirement at exactly the
   threshold degree by 0.06 %, and clears it from n = 19 on. Consequences: (a) a
   formalization keeping `hdim ≥ 18` must formalize the series refinement
   (19)–(26) (closed form (23) for L(y), truncation (25), stated error
   ~0.55·10⁻⁷y⁴); (b) if the ModThree chapter can prove its field has degree ≥ 19
   (e.g. because the surviving irreducible images force degree ≥ 24 or 48), the
   whole numerical layer collapses to inequality (16). This trade should be decided
   before work starts.

---

## 2. Statement inventory (analytic route: Weil explicit formula, Poitou's write-up)

Poitou's exposé is the right skeleton: it is a self-contained simplified proof of
Weil's explicit formula for Dedekind zeta only, then the unconditional positivity
inequality (8), then Tartar's test function and numerics. Sizes: S < 1 wk, M ≈ 1–3 wk,
L ≈ 1–3 mo, XL > 3 mo (one experienced formalizer). "[unverified]" marks citations or
numbers I could not check against a primary source.

**B1. Completed Dedekind zeta and its functional equation.** Λ_K(s) =
|d|^{s/2} g₁(s)^{r₁} g₂(s)^{r₂} ζ_K(s) (g₁ = π^{−s/2}Γ(s/2), g₂ = (2π)^{−s}Γ(s)) is
meromorphic on ℂ, poles only at 0, 1 (simple), Λ_K(s) = Λ_K(1−s). — **XL**.
[Hecke 1918; Neukirch ANT VII.5; Poitou p. 6-01 uses it as known.] The single
dominant node of the chapter; needs multidimensional theta functions with lattice
Poisson summation (or Tate's thesis).

**B2. Euler product and log-derivative.** −ζ_K′/ζ_K(s) = Σ_{𝔭,m} (log N𝔭)/(N𝔭)^{ms}
for Re s > 1; nonvanishing on Re s > 1. — **S/M**. [standard; Poitou p. 6-02.]

**B3. Zero-counting and horizontal estimates (Landau).** Zeros of ζ_K lie in
0 < Re s < 1; N_K(T) growth; horizontal contour integrals are O(‖Φ‖_{a,T} log T) and
one can choose T at distance ≥ α/log T from all zero ordinates. — **L**.
[Landau, Algebraische Zahlen p. 122, as cited by Poitou Prop. 1 — unverified page;
Lang ANT VIII.] Requires ζ_K′/ζ_K bounds in the strip, i.e. partial-fraction input.

**B4. Rectangle contour identity.** Poitou (1)/(3): Σ_{|γ|<T} Φ(ρ) − Φ(0) − Φ(1) =
(1/2πi)∮ Φ dlog Λ over ∂([−a, 1+a]×[−T, T]); argument-principle bookkeeping for the
meromorphic Λ. — **M** given B1, B3. [Poitou Prop. 1, p. 6-01/02.]

**B5. Prime-side limit.** For F even, BV after exp((½+a)|x|)-twist, with the
mean-value normalization: I_ζ(T) → −2Σ_{𝔭,m}(log N𝔭)(N𝔭)^{−m/2} F(m log N𝔭)
(Fourier reciprocity in Jordan's BV form). — **M**. [Poitou Prop. 2, p. 6-02/03.]

**B6. Archimedean side.** Gauss's integral for digamma (Poitou (5)), the three
Re ψ integral identities on p. 6-04, the two evaluated constants
(γ + 2 log 2 and π/2), and Prop. 3 (Fourier/Plancherel + two lemmas of elementary
Fourier analysis, p. 6-04/06) converting the Γ-factor integrals to
∫₀^∞ (F(0)−F(x))/(2 sh(x/2)) dx etc. — **L**. [Poitou pp. 6-03…6-06.]

**B7. Weil explicit formula for ζ_K.** Assemble B4+B5+B6: formula (6), Théorème
(A. Weil), p. 6-06/07, for even real F with conditions (i)–(iii) (summability and
bounded variation of exp-twists, (F(0)−F(x))/x BV). — **M** given B1–B6 (the glue).

**B8. Unconditional positivity reduction.** Re Φ(σ+it) = ∫F(x) ch((σ−½)x) cos tx dx;
by the maximum principle on the strip, Re Φ ≥ 0 on 0 ≤ Re s ≤ 1 iff the Fourier
transform of f(x) = F(x)·ch(x/2) is ≥ 0 (no GRH). Discarding Σ Φ(ρ) ≥ 0 and the
(nonnegative, since f ≥ 0) prime terms yields inequality (8) = Prop. 5, extended by
Gaussian regularization F·e^{−yx²} to relaxed hypotheses. — **M/L**.
[Poitou §2, pp. 6-07/09.] This is the GRH-free pivot of the whole chapter.

**B9. Tartar's test function.** f(x) = ((3/x³)(sin x − x cos x))², via
f = (9/16)·Fourier(v∗v) with v(t) = (1−t²)₊, so f ≥ 0, f̂ ≥ 0, f(0) = 1; Taylor
coefficients (20): (−1)^k f^{(2k)}(0) = 9·2^{2k+3}/((2k+1)(2k+3)(2k+4)(2k+6)).
— **S/M**. [Poitou pp. 6-13/14; Tartar's optimality claim not needed.]

**B10. Scaled inequality.** Substitute f(x√y) in (8) → formula (13):
(1/n)log|d| ≥ γ + log 4π + r₁/n − ∫₀^∞{1−f(x√y)}h(x)dx − (4/n√y)∫₀^∞f, valid for all
y > 0, with h(x) = 1/sh x + (r₁/n)/(2ch²(x/2)); prime terms already dropped. — **S**.
[Poitou p. 6-11.]

**B11. Numerical engine at n = 18.** Closed form (23) for
L(y) = −3/(20y²) + 33/(10y) + 2 + (3/(80y³)+3/(4y²))log(1+4y) − (3/y+12/5)(1/√y)
arctan 2√y; the r₁ = 0 truncation inequality (25)
L₁(y) ≤ L(y) + ⅓L(y/9) + ⅕L(y/25) + three explicit correction terms; plug a fixed
y ≈ y_opt(18) into (26) and verify by interval arithmetic that the result is
≥ log 8.25 (the paper's optimized value is 9.305672 — verified from the scan; the
Lean proof only needs ≥ 8.25, so a crude y and coarse intervals suffice). Constants
needed to ~6 digits: γ, π, log, arctan, λ(3) = 7ζ(3)/8 [unverified closed form —
recheck; Poitou defines λ(k) = (1−2^{−k})ζ(k)], η(2) = π²/12. — **M**.

**B12. Monotonicity in n and assembly.** For fixed y, RHS of (26) with r₁ = 0 is
increasing in n; hence the B11 evaluation at n = 18 gives |d| ≥ 8.25ⁿ for every
totally complex K with n ≥ 18. Package as `Odlyzko_statement`. — **S**. (My
observation; trivial from the −12π/(5n√y) term.)

**B13. (Alternative to B11+B12 if degree ≥ 19 can be arranged.)** Lemma 5 +
inequality (15)/(16): (1/n)log|d| ≥ γ + log 4π − (3/n^{2/3})(2b·B(f))^{1/3} with
b = 4λ(3), B(Tartar) = 18π²/125, giving the printed constant 6.860404
["l'arrondi est dans le bon sens", Poitou p. 6-13; my recomputation gives 6.8653 —
the printed 6.860404 is a favorable rounding whose provenance I could not fully
reproduce: **use my larger recomputed constant in Lean**, it still yields
rd ≥ 8.5386 at n = 19]. Fails at n = 18 (8.243 < 8.248). — **M**.

Node count: 12 on the critical path (B1–B12), 1 optional (B13).

---

## 3. Dependency edges

Internal (this chapter):
- B4 ← B1, B3; B5 ← B2; B6 ← B1(Γ-factors only);
- B7 ← B4, B5, B6; B8 ← B7; B10 ← B8, B9; B11 ← B10; B12 ← B11; B13 ← B8, B9.
- Final axiom-discharge node ← B12 (or ← B13 + consumer-side degree ≥ 19).

External, incoming (Mathlib / general analysis):
- B1: theta functions with Poisson summation over lattices of rank n; Mellin
  transforms; Γ-function. B3/B4: meromorphic function theory, argument principle,
  strip estimates. B5/B6: Fourier inversion (Jordan/BV form), Plancherel, digamma.
- B8: Phragmén–Lindelöf / maximum principle on a strip.
- B11: verified numerics (interval arithmetic) for γ, π, log, arctan, ζ(3).

External, outgoing (rest of FLT campaign):
- Sole consumer: `IsHardlyRamified.mod_three` (`ModThree.lean:27`, blueprint
  `hardly_ramified_mod3_reducible`), which additionally needs, from *other* chapters:
  Fontaine's different/ramification bound for finite flat 3-group schemes
  (v(𝔡) < e(1 + 1/(p−1))), tame-different formula at 2, GL₂(𝔽₃) subgroup
  classification, and the totally-complex + degree-≥18 bookkeeping. None of that
  belongs to this chapter, but the **constant interface** does: this chapter must
  deliver a constant strictly above 2^{2/3}·3^{3/2} = 8.24838 at whatever degree
  threshold ModThree can guarantee. The pair (8.25, 18) is one valid interface point;
  (8.5386, 19) and (8.748, 16) are others.
- No dependence on any other FLT chapter (leaf node of the campaign DAG).

---

## 4. Mathlib coverage (web-checked against mathlib4 docs, 2026-08)

| Ingredient | Status | Namespace / file |
|---|---|---|
| Number field discriminant | exists | `NumberField.discr`, `Mathlib.NumberTheory.NumberField.Discriminant.*` |
| Totally complex predicate | exists | `NumberField.IsTotallyComplex`, `...InfinitePlace.TotallyRealComplex` (imported by the axiom file) |
| Minkowski bound | exists | `NumberField.abs_discr_ge'`, `abs_discr_ge`, `abs_discr_ge_of_isTotallyComplex`, `Mathlib.NumberTheory.NumberField.Discriminant.Basic` |
| Dedekind zeta (definition) | exists | `NumberField.dedekindZeta`, `Mathlib.NumberTheory.LSeries.DedekindZeta` |
| ζ_K residue at 1 (class number formula) | exists | `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT` (Roblot) |
| ζ_K analytic continuation to ℂ + functional equation (B1) | **absent** | — (FE exists only for Riemann/Hurwitz zeta and `ZMod` Dirichlet L-functions: `completedRiemannZeta_one_sub`, `Mathlib.NumberTheory.LSeries.ZMod`) |
| Euler product for ζ_K (B2) | partial [unverified] | `Mathlib.NumberTheory.EulerProduct.*`; specialization to `dedekindZeta` unclear |
| Argument principle / zero counting (B3, B4) | absent (Cauchy integral formula, `MeromorphicOn` exist; no argument principle found) | `Mathlib.Analysis.Complex.CauchyIntegral`, `Mathlib.Analysis.Meromorphic.*` |
| Fourier inversion (pointwise, integrable case) | exists | `MeasureTheory.Integrable.fourier_inversion`, `Mathlib.Analysis.Fourier.Inversion` |
| Jordan/BV pointwise inversion (B5) | absent | (BV theory exists: `Mathlib.Analysis.BoundedVariation`) |
| Plancherel (B6) | exists [recent; verify exact form] | `Mathlib.Analysis.Fourier.Plancherel`-area |
| Digamma + Gauss integral formula (5) (B6) | absent (Γ, log Γ, deriv Γ exist) | `Mathlib.Analysis.SpecialFunctions.Gamma.*` |
| Max principle on a strip (B8) | exists | `Mathlib.Analysis.SpecialFunctions.PhragmenLindelof` (`PhragmenLindelof.horizontal_strip`) |
| Euler–Mascheroni γ with numeric bounds (B11) | partial (constant exists; published bounds crude, ~1/2 < γ < 2/3; need ~6 digits) | `Real.eulerMascheroniConstant`, `Mathlib.NumberTheory.Harmonic.EulerMascheroni` |
| π, log, arctan verified numerics (B11) | exists / routine | `Real.pi_gt_3141592`, `norm_num` extensions |
| ζ(3), λ(3), η(2) numerics (B11) | absent but routine (alternating/odd series tail bounds) | — |

Coverage summary: the *inequality* layer (B8–B13) sits on solid Mathlib ground; the
*explicit formula* layer (B1–B7) is essentially all missing, with B1 the crater.

---

## 5. Route risks

- **B1 is an XL crater with no Mathlib start.** The functional equation of ζ_K for a
  general number field (Hecke/Tate) is not formalized anywhere in Mathlib; it needs
  rank-n theta functions + lattice Poisson summation (Mathlib has 1-D Jacobi theta
  for the Riemann case only). This single node plausibly exceeds the rest of the
  chapter combined; it is however of high independent value (unlocks PNT-for-
  number-fields, Chebotarev-with-error-terms, etc.), so it may attract outside labor.
- **The n = 18 threshold is numerically critical.** The cheap closed-form (16)
  certifies the needed 8.2484+ only for n ≥ 19 (8.243 at 18 vs 8.540 at 19,
  recomputed). Keeping `hdim ≥ 18` forces formalizing Poitou's series engine
  (23)/(25)/(26) with interval arithmetic; alternatively, negotiate the interface
  with the ModThree chapter up to 19 (or down to 16 with constant 8.748 via the
  table's method — more numerics, weaker group theory). Decide the interface first.
- **No cheaper sufficient bound exists — settled by asymptotics.** Minkowski
  (already in Mathlib, `abs_discr_ge_of_isTotallyComplex`) asymptotes to
  (π/4)e² = 5.8034 < 8.2484 and gives only 4.46 at n = 18, so it fails at *every*
  degree, not just small ones; geometry-of-numbers can never discharge this axiom.
  Elementary Stark-lemma-style bounds (Serre's f = e^{−x²}, Poitou (15) with
  constant 7.1) also fail at n = 18 (rd ≥ 7.96) and scrape 8.257 only at n = 19.
  Any GRH-free proof at these degrees must run through zeta zeros + explicit formula.
  Conversely GRH shortcuts are unusable (can't assume GRH), so there is no "cheap
  conditional first pass" worth building.
- **Fragile paper constants.** Poitou's 6.860404 in (16) is a "favorably rounded"
  constant I could not exactly reproduce (I get 6.8653 from B(f) = 18π²/125,
  b = 4λ(3)); his table values are computed with per-n optimized y and 1970s
  numerics. Mitigation: never import his printed constants — re-derive every bound
  in Lean from (13) with explicitly chosen y and rigorous intervals; the 12.8 %
  headroom (9.31 vs 8.25) absorbs all slack. Mark: table cross-checked only against
  the scan itself and spot-consistency (n = 8 worked example 5.65936 matches);
  independent corroboration via Odlyzko/Diaz y Diaz tables [unverified].
- **Consumer mismatch risk (razor-thin on the other side).** The Fontaine-side upper
  bound 2^{2/3}·3^{3/2} = 8.24838 sits 0.02 % below the axiom's 8.25. Any weakening
  in the ModThree ramification analysis (e.g. a lost tameness at 2, giving
  2^{1}·3^{3/2} = 10.39 > 9.31) breaks the pairing *unrecoverably* — 10.39 exceeds
  even the true n = 18 bound 9.3057, and totally complex unconditional bounds only
  reach 10.39 at n ≥ 24 (table: 10.668). The chapter should therefore export the
  strongest cheap statement (constant 9.3 at 18, per the docstring's own remark),
  not the minimal 8.25, as insurance.

---

*Sources: Poitou, "Sur les petits discriminants", Sém. DPP 18 (1976/77) exp. 6
(Numdam scan, read in full); FLT repo `main` @ 4783867; mathlib4 docs (Aug 2026);
FLT GitHub issue #458.*
