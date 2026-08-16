# Odlyzko endgame — M8–M12 S/M decomposition (the part no port gives us)

**Author:** fermat (crew-18), 2026-08-16T13:59Z. **Base:** FLT `main` `0db67fd`.

Companion to `zeta-fe-decomposition.md` (M2, 24 nodes) and
`odlyzko-m3-decomposition.md` (M3, 21 nodes). Same mandate, same rigor standard: break
the wall into nodes that are **S or M only**, each provable by one agent in one focused
session, with named Mathlib anchors and one-line sketches.

## 0. Why this document exists now

`odlyzko-reconciled.md` §2.2 lists thirteen chapter nodes M1–M13. Two are decomposed (M2,
M3). Four more — M4, M5, M6, M7 — are the Weil–Poitou explicit-formula machinery, and
`aintlib-substrate.md` §A5–A6 establishes that AINTLIB's `ExplicitFormula/` tree covers
them sorry-free and, critically, **without GRH** (`WeilAssembly`, `PrimeSide`, `GammaSide`,
`ZeroCapture`, `TestFunction` mention `GeneralizedRiemannHypothesis` zero times).

That leaves **M8, M9, M10, M11, M12** — and AINTLIB does *not* cover them, because it walks
to a different destination: Belabas–Friedman's GRH-conditional residue computation, not an
unconditional discriminant lower bound. `odlyzko-reconciled.md` §5 calls M8–M12 "ready-now
nodes" and gives each a one-line description. One line is not a packet. **This document is
the S/M layer for those five**, and after it the entire Odlyzko chapter is decomposed.

The shape of the remaining campaign, stated plainly:

```
M1  small, mostly Mathlib          M2  → AINTLIB port (24 nodes if not)
M3  → AINTLIB partial + 21 nodes   M4-M7 → AINTLIB port, GRH-free
M8-M12 → THIS DOCUMENT, 22 nodes, no port available
```

**M10 is now the campaign's largest single crater** (`odlyzko-reconciled.md` sizes it L;
everything else in M8–M12 is S or M). §4 is therefore the longest section here.

## 1. Standing hypotheses and what is inherited

Every node below is stated **against the explicit formula as a hypothesis**, exactly as
`odlyzko-reconciled.md` §5 recommends. That is what makes them dispatchable before the
port lands, and it is the same device as W3-13 (the N1 interface packet).

Concretely, assume an explicit formula of Weil–Poitou shape

```
log|d_K|  =  n · A_∞(F)  +  Σ_ρ Φ_F(ρ)  +  Σ_{𝔭,m} (prime terms)  +  (pole terms)
```

for `F` in an admissible class. **Use AINTLIB's class, not mine.**
`aintlib-substrate.md` §A10 establishes `𝓕 ⊆ IsAdmissibleTestFn` and that
`IsAdmissibleTestFn` already carries the jump-average convention — so stating M8–M12 over
`IsAdmissibleTestFn` costs nothing and avoids the bridging lemma entirely. Nodes below say
"admissible" and mean that structure.

**Inherited normalization (do not re-derive):** `zeta-fe-decomposition.md`'s PQ4 freeze —
Fourier `𝓕f(ξ) = ∫ f(x) e^{−2πi⟨x,ξ⟩}`, `Gammaℝ s = π^{−s/2} Γ(s/2)`,
`Gammaℂ s = 2(2π)^{−s} Γ(s)`, `Λ_K(s) = |d_K|^{s/2} Gammaℝ(s)^{r₁} Gammaℂ(s)^{r₂} ζ_K(s)`.
AINTLIB's `Normalisation.lean:41` matches this byte-for-byte, so a ported explicit formula
and these nodes speak the same language.

**Target, verbatim from `FLT/Assumptions/Odlyzko.lean:57`:**

```lean
axiom Odlyzko_statement (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
  (hdim : finrank ℚ K ≥ 18) : |(discr K : ℝ)| ≥ 8.25 ^ finrank ℚ K
```

Note `IsTotallyComplex`, i.e. `r₁ = 0`, `r₂ = n/2`. Several nodes below are materially
easier because of it, and each says so where it applies.

## 2. M8 — GRH-free positivity and prime discard (5 nodes: 3 S, 2 M)

The move that makes the whole method unconditional: throw away two entire sides of the
explicit formula because both are nonnegative, leaving an inequality rather than an
identity. The subtlety — and the reason this is not one line — is that discarding the zero
sum **without GRH** needs positivity at zeros anywhere in the critical strip, not just on
the critical line.

**P1. Explicit-formula interface restatement.** *S. Deps: none (hypothesis-parametrized).*
One file restating the assumed formula in the exact form M8–M11 consume: `r₁ = 0`
specialization, pole terms at `s = 0, 1` made explicit, signs fixed. No mathematics; this
is the M7→M8 seam and it exists so that a port swap changes one file.
Anchor: match `WeilAssembly.lean:3128` `weil_explicit_formula_auxF`'s shape so the eventual
port is a citation, not a translation.

**P2. Prime side is nonnegative.** *S. Deps: P1, `F ≥ 0`.*
`Σ_{𝔭} Σ_{m≥1} (log N𝔭) · N𝔭^{−m/2} · F(m log N𝔭) ≥ 0` whenever `F ≥ 0` pointwise.
Sketch: termwise; `log N𝔭 > 0` since `N𝔭 ≥ 2`, and `N𝔭^{−m/2} > 0`. The only real content
is summability, which comes from admissibility's exponential-weight condition.
Mathlib: `tsum_nonneg`, `Finset.sum_nonneg`, `Ideal.absNorm` positivity.

**P3. Zero side is nonnegative on the critical line.** *S. Deps: `F̂ ≥ 0`.*
For `ρ = 1/2 + iγ` with `γ` real, `Φ_F(ρ) = F̂(γ) ≥ 0`. Immediate once M9 supplies `F̂ ≥ 0`.
This is the easy half and is *not* where GRH would have been used.

**P4. Zero side is nonnegative off the critical line — the GRH-free step.** *M. Deps: P3.*
For `ρ = β + iγ` with `β ≠ 1/2`, `Φ_F(ρ)` is not literally `F̂` of a real number. Pair `ρ`
with the functional-equation partner `1 − ρ̄` (both are zeros, by `Λ_K(s) = Λ_K(1−s)` plus
`Λ_K(s̄) = conj Λ_K(s)`), and show the **pair contributes nonnegatively**. For an
`F` that is even with `F̂ ≥ 0`, the pair sum is
`∫ F(x) · 2 cosh((β − 1/2)x) · cos(γx) dx`-shaped; positivity comes from the Tartar
maximum-principle argument — `odlyzko-reconciled.md` M8 calls this "Tartar/maximum-principle
positivity on the full critical strip".
*This is the one genuinely delicate node in M8. State it with `0 ≤ β ≤ 1` as an explicit
hypothesis (the zeros are in the strip by M3/N12) and do not attempt a sharper region.*

**P5. The discard inequality.** *M. Deps: P1, P2, P4.*
`log|d_K| ≥ n · A_∞(F) − (pole terms)`, with the pole contribution written explicitly in
terms of `F̂(±i/2)`-type values. This is the inequality every later node consumes.
Sketch: drop P2 and P4 from the identity of P1; rearrange.

**Contract, stated so a worker does not silently break it:** P4 must not be weakened to
"assume RH/GRH". If it turns out to need a hypothesis beyond `0 ≤ β ≤ 1` and `F̂ ≥ 0`,
**escalate** — a GRH-conditional P4 turns the whole chapter conditional and would silently
convert the campaign's unconditional target into AINTLIB's conditional one.

## 3. M9 — the Tartar function and the scaling inequality (6 nodes: 4 S, 2 M)

The choice of `F` that makes M8's two positivity hypotheses true simultaneously. `F ≥ 0`
and `F̂ ≥ 0` pull against each other — that is the whole difficulty of the method.

**Q1. Autocorrelation gives free Fourier positivity.** *S. Deps: none.*
For `g` real, even, compactly supported and `L²`, set `F = g ⋆ g̃` where `g̃(x) = g(−x)`.
Then `F̂ = |ĝ|² ≥ 0` identically. Also `F` is even, compactly supported (support doubles),
and continuous.
Mathlib: `Convolution` API, `Real.fourierIntegral` convolution theorem,
`MeasureTheory.convolution_comm`.
*This node is the reason the construction is tractable at all — Fourier positivity is a
theorem about the shape of the construction, not a computation.*

**Q2. Admissibility of the autocorrelation.** *S. Deps: Q1.*
`F = g ⋆ g̃` satisfies `IsAdmissibleTestFn`: even (Q1); the exponentially-weighted BV and
integrability conditions from compact support plus `g` Lipschitz; the difference-quotient
BV condition from `F` Lipschitz near `0`; `jump_avg` trivially, `F` being continuous.
Anchor: `ExplicitFormula/TestFunction.lean` `boundedVariationOn_of_deriv_integrable` and
`boundedVariationOn_Ici_of_piecewise_deriv` are exactly the two workhorses this needs — a
port makes Q2 nearly free.

**Q3. Tartar's `g` and `F ≥ 0`.** *M. Deps: Q1.*
Fix the specific `g` of Poitou §on Tartar's function; prove `F = g ⋆ g̃ ≥ 0` pointwise.
For an autocorrelation this is *not* automatic (autocorrelation gives `F̂ ≥ 0`, not
`F ≥ 0`), so this is where the specific choice earns its keep.
**PQ1 blocks the exact form of `g`:** `odlyzko-reconciled.md` §4 records that the Poitou
page images could not be fetched from Numdam, so the printed definition is currently
second-hand. *Do not let a worker guess `g`.* Either resolve PQ1 first, or state Q3 over an
abstract `g` with the two properties as hypotheses and defer the instantiation to Q3′.

**Q3′. Instantiate `g` (gated on PQ1).** *S. Deps: Q3, PQ1 resolved.*
Substitute the concrete Tartar `g` and discharge Q3's hypotheses. Split out from Q3 so that
the analytic content is not blocked on a library fetch.

**Q4. The scaling family.** *S. Deps: Q1.*
`F_y(x) := F(x/y)` for `y > 0`; then `F̂_y(t) = y · F̂(yt)`, positivity is preserved by
both, and admissibility is preserved. Sketch: change of variables.
Mathlib: `Real.fourierIntegral_comp_mul`-family / `MeasureTheory.integral_comp_smul`.

**Q5. Poitou (13) — the scaled inequality.** *M. Deps: P5, Q2, Q4.*
Feed `F_y` into P5 and collect: `log|d_K| ≥ n · A_∞(F_y) − B(F_y)`, then divide by `n` to
get a lower bound on the **root discriminant** `|d_K|^{1/n}`, in the form Poitou's (13)
states it. Specialize `r₁ = 0` here (the target is `IsTotallyComplex`), which collapses the
archimedean side to a single `Gammaℂ`-type term and isolates the quantity
`odlyzko-reconciled.md` calls `L₁(y)`.
**Output contract:** a single real-valued function `L₁ : ℝ>0 → ℝ` and the theorem
`n ≥ 1 → 0 < y → log |d_K| / n ≥ L₁(y) − (pole correction)/n`. Everything after M9 is about
evaluating `L₁` at one well-chosen `y`.

## 4. M10 — the numerical engine (7 nodes: 3 S, 4 M) — the crater

`odlyzko-reconciled.md` sizes M10 as **L** and it is the only L left in the chapter. The
job: turn `L₁(y)` — a closed form built from `γ`, `π`, `log`, `arctan` and a slowly
convergent series (Poitou (19)–(26)) — into a *certified* rational lower bound at a fixed
`y` and `n = 18`, at least `log 8.25 ≈ 2.1102`.

### What Mathlib gives us, verified at the pin `bc06ce9f` this session

| need | status |
|---|---|
| Euler–Mascheroni `γ` with two-sided bounds | **present** — `Mathlib/NumberTheory/Harmonic/EulerMascheroni.lean`: `eulerMascheroniConstant`, `one_half_lt_eulerMascheroniConstant`, `eulerMascheroniConstant_lt` |
| `e`, `log 2` to 9 digits | **present** — `Mathlib/Analysis/Complex/ExponentialBounds.lean`: `exp_one_lt_d9`, `exp_one_gt_d9`, `log_two_gt_d9`, `log_two_lt_d9` |
| `π` bounds | **present** — `Mathlib/Analysis/Real/Pi/Bounds.lean` (`pi_gt_three` and the bound machinery) |
| `arctan` order API | **present** — `Mathlib/Analysis/SpecialFunctions/Trigonometric/Arctan.lean`: `arctan_le`, `arctan_lt`, `arctan_pos` |
| digamma | **present** — `Analysis/SpecialFunctions/Gamma/Digamma.lean`: `digamma_one`, `digamma_apply_add_one` |
| **rational interval arithmetic** | **ABSENT.** The 90 `Interval` files in Mathlib are order-theoretic intervals, not a numeric IA engine. |

That last row is the finding that shapes M10: **the constants exist with certified bounds;
the machine for combining them does not.** So R1 below is real infrastructure work, and it
is also the most reusable thing in this document.

`log 3` was *not* located at the pin (AINTLIB uses a `Real.log_three_gt_d9`; it may live
elsewhere or be newer than `bc06ce9f`). **Verify before relying on it** — if absent, it is a
one-lemma addition in the R2 style.

**R1. Rational interval arithmetic layer.** *M. Deps: none.*
`structure RatIvl := (lo hi : ℚ) (le : lo ≤ hi)`, a coercion to `Set ℝ`, and sound
`add/sub/mul/div/pow/neg` with the soundness lemmas `x ∈ I → y ∈ J → x + y ∈ I + J` etc.
Division requires `0 ∉ J`. That is the whole node — deliberately minimal, no fancy
representation, `norm_num` discharges the rational arithmetic.
*Upstreamable and independently wanted; open the Mathlib PR.*

**R2. Certified evaluators for the transcendentals.** *M. Deps: R1.*
`RatIvl`-valued, soundness-proved enclosures for `γ`, `π`, `log q` and `arctan q` at
rational `q`, at a tunable precision. `γ` and `π` and `log 2` come straight from the table
above; general `log q` and `arctan q` need a certified truncated series with an explicit
tail bound (`atanh` series for `log`, the standard alternating series for `arctan` — the
alternating case gives the error bound for free).
Mathlib: `Real.add_pow_le_pow_mul_pow_of_sq_le_sq`-style is *not* what is wanted; use
`Real.abs_log_sub_add_sum_range_le` if present, otherwise prove the tail bound directly.

**R3. The Poitou series as Lean definitions.** *S. Deps: none.*
Transcribe (19)–(26) as `Real`-valued definitions with no numerics attached, so that R4/R5
have something to talk about and the transcription can be reviewed independently of the
error analysis. **Gated on PQ1** in the same way as Q3 — the equation numbers come from a
second-hand reading. Transcribe from a fetched artifact, never from the summary.

**R4. Truncation and tail bounds.** *M. Deps: R3.*
For each series in R3, an explicit `N`-term truncation with a proved remainder bound.
Sketch: these are the standard comparisons (geometric or `∫ x^{-2}`-type); the point is that
the bound is *proved*, not asserted, so R5 can be arithmetic rather than analysis.

**R5. Certified evaluation of `L₁(y₀)` at the chosen `y₀`.** *M. Deps: Q5, R1, R2, R4.*
Compose: a `RatIvl` enclosure of `L₁(y₀)` whose `lo` is a rational the `norm_num`
kernel can compare against `log 8.25`. `odlyzko-reconciled.md` records `9.305672` from the
optimizing scan — **treat that number as an input to be re-derived, not a fact**; PQ1 flags
the printed decimals as uncertified, and §4 PQ5 says explicitly to use the larger
recomputed error until every digit is independently checked.
**Choose `y₀` conservatively.** The scan's optimum maximizes the bound, but any `y₀` that
clears `log 8.25` with margin is sufficient and a non-optimal `y₀` with a fatter margin is
*cheaper to certify*. Pick margin over sharpness.

**R6. The `n = 18` comparison.** *S. Deps: R5.*
`L₁(y₀) − (pole correction)/18 ≥ log 8.25`, by `norm_num` on rationals given R5's enclosure.
Should be a handful of lines if R1–R5 did their jobs; if it is not, the error budget in R4
was too tight.

**R7. Escape hatch — record the margin.** *S. Deps: R6.*
Report the actual proved margin `L₁(y₀) − log 8.25`. If it is thin, that is the signal to
revisit `y₀` or tighten R4 **before** M11 depends on it. Cheap insurance against discovering
at M11 that the chain is 10⁻⁴ short.

## 5. M11 — uniformity in `n` (3 nodes: 2 S, 1 M)

M10 gives one degree. The axiom quantifies over all `n ≥ 18`.

**S1. Fixed-`y` monotonicity in `n`.** *M. Deps: Q5.*
At fixed `y₀`, the bound `L₁(y₀) − C/n` is nondecreasing in `n` — the pole correction is
the only `n`-dependence and it enters as `C/n` with `C > 0`. Sketch: `C/n` is decreasing.
*If the `n`-dependence is not of that shape once Q5 is concrete, this node changes
character and should be re-sized; flag rather than force.*

**S2. All `n ≥ 18`.** *S. Deps: S1, R6.*
`∀ n ≥ 18, log|d_K|/n ≥ log 8.25`, from S1 and the `n = 18` base case.

**S3. Exponential form.** *S. Deps: S2.*
`|(discr K : ℝ)| ≥ 8.25 ^ finrank ℚ K`, i.e. exponentiate and clear the division.
Mathlib: `Real.exp_le_exp`, `Real.rpow_natCast`, `Real.log_le_iff_le_exp`. Watch the
`rpow`-versus-`pow` distinction — the axiom's `8.25 ^ finrank ℚ K` is a natural power of a
real, so land on `Monoid.npow` and not `rpow`, or add the bridging `rpow_natCast` rewrite.

## 6. M12 — interface and axiom deletion (2 nodes, both S)

**T1. Statement freeze and consumer corollary.** *S. Deps: none — do this first, today.*
A file stating a theorem with **exactly** the `Odlyzko_statement` signature, proved from
S3 as a hypothesis, plus the contradiction-form corollary the ModThree consumer will want.
Dispatchable immediately as a Flash statement packet — it is the M8–M12 analogue of W3-13,
and having it early means every node above knows precisely what it is aiming at.

**T2. Delete the axiom.** *S. Deps: T1, S3, and M1–M7 all discharged.*
Replace `axiom Odlyzko_statement` with the theorem. **Acceptance is special and must be
written into the packet:** the sorry-oracle does not move (an `axiom` is not a `sorry`), so
the gate for this packet is
`#print axioms` on the consumer no longer listing `Odlyzko_statement`, plus
`scripts/sorry_count.py` unchanged at `[0,0]`, plus gate clause 5's "no new axiom" trivially
satisfied. A packet that only checks the sorry count would pass this vacuously — the same
class of hole as `oracle-recount.md` §8.

## 7. Node count, parallelism, and what to cut now

**22 nodes: 12 S, 9 M, 1 gated (Q3′).** No L, no XL — the mandate is met, and M10's L
dissolves into R1–R7.

**Dispatchable today, with no port and no PQ1** — six nodes, because they are either
hypothesis-parametrized or pure infrastructure:

```
P1  explicit-formula interface restatement     S
Q1  autocorrelation ⇒ F̂ = |ĝ|² ≥ 0             S
R1  rational interval arithmetic layer         M   ← also upstreamable to Mathlib
R2  certified transcendental evaluators        M   ← depends only on R1
T1  Odlyzko_statement interface freeze         S   ← do this first
P2  prime-side nonnegativity                   S   (needs P1 only)
```

**Recommended first three: T1, R1, Q1.** T1 because every other node aims at it; R1 because
it is the longest pole in M10 and is independently useful; Q1 because it is the structural
insight the whole `F` construction rests on and it is small.

**Blocked on PQ1 (the Poitou artifact):** Q3′ and R3, and therefore R4–R7 downstream. **This
makes PQ1 the highest-value non-Lean action in the chapter** — someone needs to fetch and
commit a page image of Poitou p. 17 and the surrounding equations. It is a library errand,
not a proof, and it currently gates the entire numerical column. Raised previously as PQ1
in `odlyzko-reconciled.md` §4 and still open.

**Deepest chain (7):** Q1 → Q3 → Q5 → R5 → R6 → S2 → S3.

## 8. What is not verified here

- **No Lean was run.** crew-18 has no toolchain. Sizes are judgements, the Mathlib anchors
  in §4 were verified by fetching each file at rev `bc06ce9f` and grepping, and everything
  else is a reading.
- **The mathematics of M8–M11 is inherited**, from `odlyzko-reconciled.md` and `odlyzko.md`,
  which in turn read Poitou second-hand. The decomposition is only as sound as that
  reading, and PQ1 is the open item that would confirm it. Two places where I would expect
  a surprise if PQ1 resolves against us: the exact form of Tartar's `g` (Q3), and whether
  the `n`-dependence in S1 really is a clean `C/n` (it is stated as such but not shown).
- **P4 is the node I would bet on being harder than M**, and it is the one that must not
  be allowed to acquire a GRH hypothesis. If it does, escalate — do not proceed.
- **AINTLIB coverage of M4–M7 is signature-level**, per `aintlib-substrate.md` §A9, and is
  itself gated on AINTLIB-0′. If that build check comes back red, M4–M7 return to the
  campaign's own workload and this document's §1 hypothesis has to be discharged by hand.
