# Cartography: Odlyzko discriminant bounds (hub-lsb1u.6)

P1 first-pass map of what the FLT-on-Lean route needs from Odlyzko-style root-discriminant
bounds, and what it would take to discharge the repo's `Odlyzko` assumption. Cartography
only; no proofs.

Repo state surveyed: `main` at time of writing. Files cited by absolute repo path.

---

## 1. What FLT needs

### 1.1 Blueprint invocations (exact quotes)

`blueprint/src/chapter/ch03freyreduction.tex:272-276`:

> By far the easiest is theorem~\ref{hardly_ramified_3adic_reducible}; this follows
> from old estimates of Fontaine (ultimately relying on bounds for root discriminants due to
> Odlyzko and Poitou), originally developed to prove that there was no
> nontrivial abelian scheme over $\Z.$

`blueprint/src/chapter/ch04overview.tex:106-108`:

> Reducing mod 3 we get a representation which is flat at 3 and tame at 2,
> so must be reducible because
> of the techniques introduced in Fontaine's paper on abelian varieties over $\Z$ (an irreducible
> representation would cut out a number field whose discriminant violates the Odlyzko bounds).

The consuming theorem chain in the blueprint (ch03freyreduction.tex):

- `hardly_ramified_mod3_reducible` (tex line ~215; Lean: `GaloisRepresentation.IsHardlyRamified.mod_three`):
  "Suppose $k$ is a finite field of characteristic 3, and suppose
  $\overline{\rho}:\GQ\to\GL_2(k)$ is hardly ramified. Then $\overline{\rho}$ is an extension
  of the cyclotomic character by the trivial representation." Proof: "Omitted for now. TODO".
  This is where the Fontaine/Odlyzko argument lives.
- It feeds `hardly_ramified_3adic_reducible` (tex:234) → `hardly_ramified_reducible` → `Wiles_Frey_again` (B4).

### 1.2 The repo's Lean assumption (the contract to discharge)

`FLT/Assumptions/Odlyzko.lean:58-59` — the exact axiom:

```lean
axiom Odlyzko_statement (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
  (hdim : finrank ℚ K ≥ 18) : |(discr K : ℝ)| ≥ 8.25 ^ finrank ℚ K
```

i.e. **every totally complex number field of degree ≥ 18 has root discriminant ≥ 8.25.**
Tracking issue: FLT repo #458. Listed in `FLT/Assumptions/README.md:26`.

The docstring (`Odlyzko.lean:20-26`) pins the source and confirms Minkowski is insufficient:

> In the proof of FLT being formalized, we need stronger bounds which do not follow
> from Minkowski's elementary argument. By analysing the behaviour of the zeros
> of the zeta function of K, Odlyzko was able to give such stronger bounds. These bounds
> were improved by Poitou in his 1977 paper "Sur les petits discriminants".
> Equation 26 of the paper implies the below bound, and an explicit reference for
> it is the table on p17 of the paper (in fact 8.25 can be beefed up to 9.3, but
> we do not need this).

Lean consumer status: `Odlyzko_statement` is imported by `FLT.lean:5` but **not yet invoked
anywhere** — the intended consumer `mod_three` (`FLT/GaloisRepresentation/HardlyRamified/ModThree.lean:27-34`)
is a bare `sorry`. So the axiom's exact shape is the current best guess at the interface,
not yet exercised by a proof.

Why 8.25 / degree 18 (inferred, since the consumer proof is unwritten): in Fontaine's
style of argument the field cut out by an irreducible hardly ramified mod-3 representation
is totally complex, ramified only at 2 (tamely, contributing ≤ 2^{2/3} to the root
discriminant) and at 3 (flat, Fontaine's ramification bound contributing ≤ 3^{1+1/(3-1)} = 3^{3/2}),
so its root discriminant is < 2^{2/3}·3^{3/2} ≈ 8.2483 < 8.25. The Odlyzko/Poitou lower
bound then forces degree < 18, and the finitely many small degrees are killed by other
means (group theory / the Minkowski-type bounds already formalized, see §1.3).
**The slack is thin: 8.2483 vs 8.25.**

### 1.3 What is already proved in-repo (Minkowski side)

`FLT/NumberField/DiscriminantBounds.lean` (197 lines, sorry-free) formalizes Minkowski's
root-discriminant lower bound for totally complex fields:

- `rootDiscrBound (n) := (π/4) * (n^2 / (n!)^(2/n))` (line 110), `rootDiscrBound_strictMono` (113),
- threshold lemmas `rootDiscrBound_lt_iff_lt_fourteen` (175: threshold `2^(2/3) * 3^(7/8)` ≈ 4.15
  ⇔ n < 14) and `rootDiscrBound_lt_iff_lt_five` (183: threshold 2.75 ⇔ n < 5),
  packaged as `le_fourteen_of_rootDiscrBound`, `le_five_of_rootDiscrBound`.

The `2^(2/3)·3^(7/8)` threshold is the tame-at-2, *tame*-at-3 Fontaine bound — these lemmas
handle sub-cases of the mod-3 analysis where ramification at 3 is tame, for which Minkowski
suffices. They are not yet consumed anywhere else in the repo either.

### 1.4 Weakest sufficient statement

**Exactly `Odlyzko_statement` as axiomatized: root discriminant ≥ 8.25 for totally complex
fields of every degree ≥ 18, GRH-free.** This is a single uniform-in-degree numerical
consequence — none of the general Odlyzko machinery (optimal constants, GRH variants,
totally real case, low-degree tables) is needed. But because it quantifies over all
degrees ≥ 18 it is *not* a finite check, and:

**Minkowski does NOT suffice.** Minkowski's totally complex bound
`(π/4)·n²/(n!)^{2/n}` tends to `(π/4)e² ≈ 5.803` from below (at n = 18 it gives ≈ 4.46),
so it never reaches 8.25 at any degree. The genuinely analytic (Weil explicit formula /
Poitou) route is unavoidable for the ≥ 8.25 part; Minkowski covers only the auxiliary
small-degree/tame thresholds of §1.3. (Stake in the ground: any plan claiming a
Minkowski-only discharge of #458 is wrong.)

Primary citation: G. Poitou, *Sur les petits discriminants*, Séminaire Delange–Pisot–Poitou
18 (1976/77), exp. 6 — eq. (26) and table p. 17 [numbers unverified against the paper;
verification is node N9]. Background: Odlyzko, *Lower bounds for discriminants of number
fields* I/II; Serre, *Minorations de discriminants* (Œuvres III).

---

## 2. Statement inventory

Nodes to prove `Odlyzko_statement` GRH-free via the Weil–Poitou explicit formula.
Sizes: S < 1 wk, M ≈ 1–4 wk, L ≈ 1–3 mo, XL > 3 mo (single-person, Lean-expert estimates).

| # | Node | Informal statement | Size | Citation / status |
|---|------|--------------------|------|-------------------|
| N1 | `dedekindZeta_basic` | ζ_K as an L-series: Euler product, convergence Re s > 1, nonvanishing there; residue at s = 1. | S | **Already in Mathlib** (`NumberField.dedekindZeta`, class-number formula `tendsto_sub_one_mul_dedekindZeta_nhdsGT`; Loeffler–Stoll, *Formalizing zeta and L-functions in Lean*, AFM 1 (2025)). |
| N2 | `completed_dedekindZeta` | Completed zeta Λ_K(s) = \|d_K\|^{s/2} Γ_ℝ(s)^{r₁} Γ_ℂ(s)^{r₂} ζ_K(s); meromorphic continuation to ℂ with simple poles only at s = 0, 1. | XL | Hecke; Tate's thesis. **Absent from Mathlib** for general K (only ℚ and Dirichlet L-functions have it). Biggest infrastructure node. |
| N3 | `dedekindZeta_functional_equation` | Λ_K(s) = Λ_K(1 − s). | (in N2) | Hecke/Tate; in practice proved together with N2 (Tate's thesis route or Hecke theta route). |
| N4 | `zeros_in_critical_strip` | Nontrivial zeros ρ of ζ_K satisfy 0 ≤ Re ρ ≤ 1; zero-counting: Λ_K is order ≤ 1, Hadamard factorization over its zeros. | XL | Standard (Lang ANT ch. XIII). Needs entire-function/Hadamard theory; **partial at best in Mathlib** (unverified — check `Mathlib.Analysis.SpecialFunctions.Gamma`, Hadamard factorization status). |
| N5 | `logderiv_partial_fraction` | −Λ'_K/Λ_K partial-fraction expansion over zeros (from N4). | M | Standard consequence of Hadamard factorization. |
| N6 | `weil_explicit_formula` | For a suitable even test function F with Mellin/Fourier transform Φ: log\|d_K\| = r₁·(archimedean ℝ-term) + 2r₂·(archimedean ℂ-term) + Σ_ρ Φ(ρ) − Σ_{𝔭,m} (prime-power terms) + (pole terms), Poitou's normalization. | XL | Weil 1952; Poitou 1976/77 §1; also Odlyzko's survey *Bounds for discriminants…* (1990). Absent from Mathlib. |
| N7 | `positive_test_function` | A concrete GRH-free-positivity test function (Poitou uses Tartar's function, F with Φ ≥ 0 on the whole critical strip, i.e. positivity of Re Φ(ρ) without knowing Re ρ = 1/2), so the zero sum can be discarded. | M | Poitou 1976/77 (fonction de Tartar); Odlyzko 1990 §4. Elementary real analysis once stated. |
| N8 | `archimedean_evaluation` | Explicit evaluation/lower-bounding of the archimedean Γ-terms for the chosen test function: digamma estimates, explicit constants as a function of a scaling parameter. | L | Poitou eq. (26). Real one-variable analysis + Γ/ψ facts (Mathlib has Γ, digamma basics — partial). |
| N9 | `numerical_bound_verification` | Recompute from N6–N8: for totally complex K (r₁ = 0), degree n, the optimized inequality gives rd(K) ≥ b(n) with b(n) ≥ 8.25 for all n ≥ 18. **Verify the 8.25/18 pair against Poitou's table p. 17 — currently unverified.** | L | Poitou table p. 17 [unverified numbers]; involves choosing the scaling parameter per n and a monotonicity argument to cover all n ≥ 18 uniformly. |
| N10 | `prime_sum_discard` | Prime-power terms in the explicit formula have the favorable sign for the chosen F and can be dropped. | S | Poitou §2. |
| N11 | `odlyzko_interface` | Assemble N6–N10 into exactly `Odlyzko_statement` (`|discr K| ≥ 8.25 ^ finrank ℚ K` for totally complex, finrank ≥ 18) and delete the axiom. | S | Interface glue; must match `FLT/Assumptions/Odlyzko.lean:58` verbatim. |
| N12 | (parallel, already done) `minkowski_small_degree` | Minkowski thresholds for the tame sub-cases (n < 14, n < 5). | done | `FLT/NumberField/DiscriminantBounds.lean` (sorry-free). |

Critical path: N2/N3 → N4 → N5 → N6 → {N7, N8, N10} → N9 → N11.
Rough total: 2 XL + 1 XL-ish (N4) dominate; this chapter is an analytic-number-theory
project comparable to the Dirichlet-L-function functional equation effort that went into
Mathlib, but for general number fields.

---

## 3. Dependency edges

Internal (this chapter):
- N11 ← N9 ← {N6, N7, N8, N10}; N6 ← N5 ← N4 ← {N2, N3} ← N1.
- N9 ← N8 (constants), N9 ← N7 (sign of zero sum).

Outbound (consumers, other chapters):
- `Odlyzko_statement` → Fontaine-style discriminant argument inside
  `GaloisRepresentation.IsHardlyRamified.mod_three` (`FLT/GaloisRepresentation/HardlyRamified/ModThree.lean`,
  currently `sorry`) → `three_adic` → `hardly_ramified_reducible` → B4 (`FLT.Bosses.B4_proof`,
  blueprint `Wiles_Frey_again`).
- N12 (Minkowski thresholds) → same `mod_three` proof, tame sub-cases.
- The mod_three proof also needs (out of scope here, separate chapters): Fontaine's
  ramification bound for finite flat group schemes (v(𝔡) < 1 + 1/(p−1), Fontaine 1985),
  tame conductor bounds at 2, and finite group theory for small-degree fields.

Inbound (external prerequisites, Mathlib):
- N1 ← Mathlib L-series + Dedekind-domain ideal norm machinery.
- N2/N3 ← either Tate's thesis (adelic; FLT repo already builds adeles — `FLT/DedekindDomain/…`,
  Fujisaki project) or classical Hecke theta functions (multi-dim Poisson summation;
  Mathlib has 1-dim Poisson summation and Jacobi theta — partial).
- N4 ← complex analysis: order of entire functions, Hadamard factorization (status: check).
- N8 ← Mathlib Γ/digamma, `Real.pi` bounds, `Stirling` (all present; FLT repo already
  exercises them in `DiscriminantBounds.lean`).

---

## 4. Mathlib anchors (web-checked 2026-08)

| Topic | Status | Namespace / location |
|---|---|---|
| Discriminant of a number field | **exists** | `NumberField.discr`, `Mathlib.NumberTheory.NumberField.Discriminant.Defs` |
| Minkowski lower discriminant bound | **exists** | `NumberField.abs_discr_ge` (`4/9 * (3π/4)^n ≤ |discr K|`), `NumberField.abs_discr_ge_of_isTotallyComplex`, `Mathlib.NumberTheory.NumberField.Discriminant.Basic` |
| Minkowski bound (convex body) | **exists** | `NumberField.mixedEmbedding.minkowskiBound` |
| Hermite finiteness (bounded discr ⇒ finitely many fields) | **exists** | `NumberField.finite_of_discr_bdd` area (`rank_le_rankOfDiscrBdd`, `minkowskiBound_lt_boundOfDiscBdd`) |
| Dedekind zeta function | **partial** | `NumberField.dedekindZeta` exists; residue at 1 (class number formula) `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT` exists; **functional equation / completed Λ_K: absent** (only ℚ, Dirichlet/Hurwitz cases have it — Loeffler–Stoll AFM 2025 framework) |
| Weil/Guinand explicit formulae | **absent** | no formalization found in Mathlib or major Lean projects |
| Hadamard factorization / order of entire functions | **absent/partial** (unverified — needs a repo-level check; not surfaced by search) | — |
| Root-disc Minkowski thresholds used by FLT | **exists (in FLT repo, not Mathlib)** | `rootDiscrBound*`, `/Users/kas/FLT/FLT/NumberField/DiscriminantBounds.lean` (header notes the strict-mono lemmas are marked "upstream") |

---

## 5. Route risk

- **Minkowski-only does NOT suffice — settled, not open.** Minkowski's totally complex
  bound asymptotes to (π/4)e² ≈ 5.80 < 8.25 (≈ 4.46 at n = 18), and the repo docstring
  says so explicitly. The cheap route exists only for the auxiliary tame thresholds
  (already formalized, N12). Budget for genuine analytic machinery.
- **The functional equation of ζ_K for general number fields (N2/N3) is the single
  largest absent prerequisite** — an XL project on its own (Tate's thesis or Hecke theta).
  Mitigation: the FLT repo already has substantial adelic infrastructure, and the
  Loeffler–Stoll L-series framework is designed to be extended; coordinate with Mathlib
  ANT maintainers before starting, since this is a likely-independently-wanted target.
- **Thin numerical slack, unverified constants.** The argument needs 8.25 against an
  upper bound ≈ 2^{2/3}·3^{3/2} ≈ 8.2483 — margin 0.002. The 8.25/degree-18 pair is
  quoted from Poitou's table p. 17 and has not been verified here (N9); the docstring's
  "8.25 can be beefed up to 9.3" is the safety valve, but the *degree threshold* 18
  interacts with how many small-degree cases the group-theory side must absorb.
  Recompute Poitou eq. 26 early (a P2 numerical task, no Lean needed) before committing
  to the interface.
- **Interface risk: the consumer is a `sorry`.** `mod_three` has no written proof, so the
  axiom's exact shape (totally complex? ≥ vs >? degree 18? discr vs root-discr form) may
  shift once someone drafts the Fontaine argument. Freeze the interface by drafting the
  mod_three blueprint proof (currently "Omitted for now — TODO" in the tex) before
  investing in N9/N11.
- **Schedule shape:** N7/N8/N10 (the "Odlyzko-specific" analysis) are ordinary real
  analysis and can be prototyped against an *assumed* explicit formula (state N6 as a
  hypothesis), decoupling the numerical work from the XL zeta infrastructure. Recommended
  first move for parallelism.
