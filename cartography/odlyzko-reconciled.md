# Odlyzko chapter — reconciled map (hub-lsb1u.6)

Reconciliation of the two independent passes:

- **P1** = `cartography/odlyzko:cartography/odlyzko.md` (the first pass).
- **P2** = `cartography/odlyzko-b:cartography-b/odlyzko.md` (the independent
  Numdam/page-image pass).

Repo facts below were checked against the local `main` snapshot.  The requested
`git fetch origin` could not refresh the remote refs in this environment (DNS for
`github.com` is unavailable), so the two local branch commits are the snapshots
used here.

## 1. Agreement matrix

The following is the high-confidence common ground.  The key point is that the
Lean contract, rather than a convenient contradiction reformulation, is the
interface that must eventually be discharged.

| Item | Agreement (precise statement) | Evidence |
|---|---|---|
| A1. Weakest stable Lean statement | The weakest sufficient **repo-facing** statement is the axiom, verbatim: `axiom Odlyzko_statement (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K] (hdim : finrank ℚ K ≥ 18) : |(discr K : ℝ)| ≥ 8.25 ^ finrank ℚ K`. Equivalently, every totally complex number field of degree `n ≥ 18` has root discriminant at least `8.25` (GRH-free). | P1 §1.2/§1.4; P2 §1.1/§1.3; `FLT/Assumptions/Odlyzko.lean:58-60`. |
| A2. Minkowski is insufficient | For totally complex fields the formalized Minkowski bound is `(π/4) n²/(n!)^(2/n)`. It is about `4.46041` at `n = 18` and tends to `(π/4)e² = 5.80335…`, strictly below `8.25` for every degree. It can discharge only the already-formalized tame/small-degree side lemmas, not `Odlyzko_statement`. | P1 §1.3/§5; P2 §5; `FLT/NumberField/DiscriminantBounds.lean`. |
| A3. Dominant absent prerequisite | The dominant missing analytic prerequisite is the **general Dedekind-zeta functional-equation package**: completed `Λ_K(s)` (with meromorphic continuation and simple poles at `0,1`) and `Λ_K(s)=Λ_K(1-s)` for an arbitrary number field. This is absent from Mathlib/repo (apart from special cases such as `ℚ`/Dirichlet L-functions); it is the XL crater before the explicit formula. | P1 N2/N3 and §4/§5; P2 B1 and §4/§5. |
| A4. Consumer location | The intended consumer is `GaloisRepresentation.IsHardlyRamified.mod_three` (`FLT/GaloisRepresentation/HardlyRamified/ModThree.lean:27`), corresponding to blueprint `hardly_ramified_mod3_reducible`; the theorem is currently `sorry`, and no grep hit invokes `Odlyzko_statement`. | Direct source check; both passes. |
| A5. Source role | The docstring explicitly says Minkowski does not give the needed stronger bound, cites Poitou eq. (26) and the p. 17 table, and notes that `8.25` can be strengthened to about `9.3`. | `FLT/Assumptions/Odlyzko.lean:12-27`; both passes. |

The contradiction form

> no totally complex `K` with `finrank ℚ K ≥ 18` and
> `rd(K) ≤ 2^(2/3)·3^(3/2)`

is a useful consumer lemma, but it is derived from (and does not replace) the
verbatim axiom contract above.  In particular, it must not silently change the
degree threshold or the `discr`/real-power formulation.

## 2. Divergences resolved

### 2.1 Numerical tightness: two different meanings of “slack”

P1’s “razor-thin” warning is correct at the **consumer interface**.  Recomputing
the Fontaine-side upper bound gives

```
U = 2^(2/3) * 3^(3/2) = 8.248377821991616…
8.25 - U = 0.001622178008384…  (0.01967% of U).
```

Thus a proof that exported only `rd ≥ 8.25` has a very small margin over the
ramification estimate.  This is a real interface risk, not a numerical error.

P2’s “12.8% headroom” refers to a different comparison: the **unconditional
Poitou table value** at degree 18 is `9.305672`, so

```
9.305672 / 8.25 - 1 = 12.7960%.
```

The p. 17 table headed “Discriminants des corps totalement imaginaires” is the
no-GRH table in §4 of Poitou’s *Sur les petits discriminants* (Numdam item
`SDPP_1976-1977__18_1_A6_0`), not the GRH section.  P2 read the page images and
reports the checked rows `n=14: 8.122437`, `n=16: 8.748418`, `n=18:
9.305672`, `n=20: 9.805700`; those entries agree with the docstring’s “about
9.3” remark.  The local environment cannot resolve `www.numdam.org`, so a fresh
HTTP download was not possible here; the table digits are therefore retained as
P2’s primary-scan transcription and are marked for one reproducible artifact in
the panel questions below.

The two claims are compatible.  What matters for formalization is that Poitou’s
**closed-form inequality (16)** is not enough at the axiom’s exact threshold.  In
the totally complex case, using the printed constant `6.860404`,

```
rd ≥ exp(γ + log(4π) - 6.860404 n^(-2/3))
n=18: 8.2431901746…   (below 8.25 and below U)
n=19: 8.5399037380…   (above both)
n=20: 8.8210405402…
```

Using P2’s more conservative recomputation `6.8653` lowers these to about
`8.23732`, `8.53403`, and `8.81518`, respectively; the verdict is unchanged.
Consequently:

1. retaining `hdim ≥ 18` forces the finite-series refinement (Poitou (19)–(26),
   including the `L₁(y)` truncation/error control) and an interval-certified
   evaluation at `n=18`;
2. the fixed-`y` right side of (26) is increasing in `n` when `r₁=0` (the only
   `n`-dependent correction is `-12π/(5n√y)`), so one certified `n=18` choice
   proves the whole `n ≥ 18` range; and
3. the table’s `9.305672` therefore supplies ample proof slack **after** the
   series engine is formalized.  It does not make the closed-form shortcut valid
   at `n=18`.

This resolves the apparent disagreement: P1 diagnosed the thin `8.25` versus
Fontaine upper-bound interface; P2 identified the generous optimized-table margin
and the separate degree-19 closed-form shortcut.

### 2.2 One merged inventory (12 core nodes + 1 optional node)

P1’s N1–N11 and P2’s B1–B12 are the same analytic path at different granularity:
P1 splits the completed zeta/functional equation and the explicit-formula pieces,
while P2 exposes the contour, prime, archimedean, and positivity sublemmas.  The
merged path below has twelve indispensable nodes.  P1’s N12 (Minkowski tame
thresholds) is recorded as an already-complete auxiliary, not a critical-path
node.  P2’s B13 is retained as optional node M13.

Difficulty scale: `S < M < L < XL < XL+`.  Confidence is confidence in the
statement/placement, not a claim that the proof is already available.

| # | Merged node (P1/P2 mapping) | Deliverable | Size | Confidence |
|---:|---|---|---|---|
| M1 | Basic Dedekind-zeta package (N1 / B2) | Euler product, absolute convergence and nonvanishing for `Re s>1`, logarithmic derivative, and the residue input needed by the explicit formula. | S–M | high for definitions; medium for the specialized Euler-product API |
| M2 | Completed zeta and FE (N2+N3 / B1) | `Λ_K(s)` with continuation, poles at `0,1`, and `Λ_K(s)=Λ_K(1-s)` for general `K`. | XL | high (statement); low (availability) |
| M3 | Strip zeros and horizontal estimates (N4 / B3) | Zeros in `0<Re s<1`, zero counting, and the horizontal-contour estimates needed to choose admissible heights. | XL | medium |
| M4 | Rectangle/argument-principle identity (part of N6 / B4) | Poitou’s contour identity relating the zero sum, pole terms, and the boundary integral. | M | medium |
| M5 | Prime-side limit (part of N6 / B5) | Limit of the vertical integral to the prime-power sum with Poitou’s normalization and sign. | M | medium |
| M6 | Archimedean Γ/digamma side (N8 / B6) | Evaluate/bound the real and complex Γ-factor integrals, including the digamma identities. | L | medium |
| M7 | Weil–Poitou explicit formula (N6 / B7) | Assemble M4–M6 into the Dedekind-zeta explicit formula under the stated test-function hypotheses. | M once M2–M6 exist | high (assembly statement) |
| M8 | GRH-free positivity and prime discard (N7+N10 / B8) | Tartar/maximum-principle positivity on the full critical strip; discard the nonnegative zero/prime contributions without GRH. | M–L | high (mathematical role); medium (Lean proof) |
| M9 | Tartar function and scaling inequality (N7+N8 / B9+B10) | Define `f`, prove `f≥0` and `f̂≥0`, derive Poitou (13), and isolate `L₁(y)` for `r₁=0`. | M | high |
| M10 | Full numerical series engine (N9 / B11) | Formalize Poitou (19)–(26), truncation/error bounds, and interval-certified constants; evaluate a fixed `y` at `n=18` to at least `log 8.25` (the scan’s optimized value is `9.305672`). | L | medium–high (formula); medium (digits until artifact) |
| M11 | Uniformity and axiom assembly (N9+N11 / B12) | Prove fixed-`y` monotonicity in `n`, obtain the bound for every `n≥18`, and convert it to `|(discr K : ℝ)| ≥ 8.25^n`. | S | high conditional on M10 |
| M12 | Interface/package node (N11 / final B12) | State the theorem with exactly the `Odlyzko_statement` type, replace the axiom only after M1–M11, and expose the consumer lemma in the required real-power form. | S | high |
| M13 (optional) | Degree-19 closed-form shortcut (P2 B13) | If the consumer proves `n≥19`, use (16) alone (with a conservatively rederived constant) instead of M10. It is not a valid replacement while the contract remains `n≥18`. | M | high for the numerical verdict; conditional on consumer degree |

Auxiliary already done: `FLT/NumberField/DiscriminantBounds.lean` proves the
Minkowski strict-monotonicity and tame thresholds (P1 N12).  It remains useful to
the ModThree proof but does not shorten M2–M12.

### 2.3 Dependencies

```
M1 → M2 → M3 → M4 ┐
             M5 ───┼→ M7 → M8 → M9 → M10 → M11 → M12
             M6 ───┘                         ↑
M13 is an alternative to M10+M11 only when the consumer supplies n ≥ 19.
```

The diagram is schematic: M6 also uses the Γ portion of M2, and M8/M9 use the
test-function hypotheses from M7.  No node claims that the general FE is already
present in Mathlib.

## 3. P2 interface question: may the degree bound become 19?

**Current Lean answer: no constraint is encoded, so the change is source-compatible
today but not yet justified for the intended proof.**

`FLT/Assumptions/Odlyzko.lean` hard-codes `hdim : finrank ℚ K ≥ 18`.  In contrast,
`FLT/GaloisRepresentation/HardlyRamified/ModThree.lean` has the signature

```lean
theorem mod_three ... (hV : Module.rank k V = 2)
  (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
  ∃ (π : V →ₗ[k] k) (_ : Function.Surjective π), ...
```

There is no number field `K`, no discriminant, and no degree premise in that
theorem; `Odlyzko_statement` is not referenced anywhere because the proof is still
`sorry`.  The blueprint theorem `hardly_ramified_mod3_reducible` likewise states
only “finite field of characteristic 3 + hardly ramified ⇒ extension of cyclotomic
by trivial”; its proof is explicitly “Omitted for now. TODO”.  The surrounding
blueprint paragraphs mention an irreducible representation cutting out a totally
complex field and violating Odlyzko bounds, but they do not assert degree 18, let
alone degree 19.

Therefore raising the axiom threshold to 19 is admissible only **conditionally**:
the ModThree/Fontaine development would first have to prove that every irreducible
case it sends to Odlyzko has `[K:ℚ] ≥ 19` (and remains totally complex).  No such
consumer lemma is present in the repo or blueprint.  Without it, changing 18→19
would be an unjustified weakening and could strand a genuine degree-18 case.  The
recommended interface is to retain 18, formalize M10, and treat M13 as a panel-
approved optimization if a degree-19 lemma is later supplied.

## 4. Panel questions

1. **PQ1 — Numdam reproducibility and constants.** Obtain and check a committed
   page-image/PDF artifact for Poitou p. 17, record the optimizing `y` at `n=18`,
   and rederive the `L₁` truncation/error intervals.  The table transcription is
   internally consistent and matches the docstring, but the current environment
   could not fetch Numdam.
2. **PQ2 — Degree-19 consumer lemma.** Can the ModThree/Fontaine argument prove
   degree at least 19 for every irreducible cut-out field, or only the documented
   threshold 18?  This decides M13 versus M10 and must be answered before changing
   the axiom interface.
3. **PQ3 — FE route.** Tate’s thesis/adelic Poisson summation or a Hecke-theta
   construction: which route best reuses the repo’s existing adelic infrastructure,
   and what should be upstreamed to Mathlib first?
4. **PQ4 — Explicit-formula API.** Freeze the hypotheses on `F`, Fourier/Mellin
   normalization, BV limits, and the sign convention so M4–M8 are not re-proved
   under incompatible normalizations.
5. **PQ5 — Numerical Lean strategy.** Decide on interval-arithmetic support for
   `γ`, `π`, `log`, `arctan`, `ζ(3)`/`λ(3)`, and the conservative constant (use the
   larger recomputed error until every printed Poitou decimal is independently
   certified).

## 5. Ready-now nodes

> **DECOMPOSED, 2026-08-16T13:59Z — see `odlyzko-endgame-decomposition.md`.** The five
> nodes below are now broken into **22 S/M leaves** (12 S, 9 M, 1 gated), which retires
> M10's L. Six are dispatchable today with no port and no PQ1: P1, Q1, R1, R2, T1, P2.
> The section below is kept as the statement of intent; the decomposition supersedes it as
> the thing to dispatch from. Note also that M4–M7 are now believed covered sorry-free and
> GRH-free by AINTLIB (`aintlib-substrate.md` §A5–A6), gated on AINTLIB-0′.

These can be cut as work beads without a decision on the FE route or on the degree
threshold:

- **M8:** formalize the strip-positivity/prime-discard lemma under an explicit-formula
  hypothesis.
- **M9:** formalize Tartar’s function, its Fourier positivity, and the scaled
  inequality (13).
- **M10:** build a standalone numerical notebook/prototype for (19)–(26), with
  conservative interval bounds and the `n=18` target.
- **M11:** prove the fixed-`y` monotonicity and the all-`n≥18` assembly as a small,
  independently testable real-analysis module.
- **M12 (statement freeze only):** add a compatibility lemma exposing the exact
  `Odlyzko_statement` type and its contradiction-form consumer corollary; do not
  delete the axiom until M10–M11 are certified.

The auxiliary Minkowski thresholds are already ready and sorry-free; they should be
reused by ModThree for its tame subcases, but they do not discharge Odlyzko.

