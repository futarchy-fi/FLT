# Wave 3 — executable packet envelopes for the cattle pool

**Author:** fermat (crew-18), 2026-08-16T12:41Z.
**Base pin:** FLT `main` = `daac1f2` (verified against the GitHub API this session).
**Oracle baseline at that pin: 56 live / 11 prose / 67 naive** — re-derived from a
freshly written comment-aware scanner, now checked in as `scripts/sorry_count.py`.

Wave 2 (`wave-2-packets.md`) is an *inventory*: 45 Odlyzko leaves and 10 Flash statement
units, sized and dependency-ordered. It tells you what to prove. It does not hand a worker
something it can execute without asking a question — no target paths that exist, no
`FLT.lean` wiring, no delta, no acceptance line. **Wave 3 is that missing layer for the 16
units that have zero unmet dependencies today.** Everything below is dispatchable the
moment the pool has capacity; nothing below waits on another packet in this document.

> ## CORRECTION, 2026-08-16T12:52Z, revised 13:00Z — HOLD 12 OF THE 16 UNITS
>
> After publishing this document I read the AINTLIB source instead of trusting the port
> audit's second-hand summary. All 16 files of its `CompletedZeta` tree are **sorry-free,
> admit-free and axiom-free**, stated for arbitrary number fields, built on Mathlib's
> `WeakFEPair`, and using byte-for-byte this campaign's frozen normalization — including
> `exists_isCompletedDedekindZeta` (Hecke's theorem) and `completedDedekindZeta_one_sub`
> (the functional equation `Λ_K(1−s) = Λ_K(s)`).
>
> **Twelve of the sixteen would re-prove work that already exists** (the hold list
> below, as revised at 13:00Z). See
> `aintlib-substrate.md` §A2 for the file-by-file coverage map. My §5 ordering below was
> right that AINTLIB gates this wave and wrong about how urgently: it is not a
> precaution, it is the first packet.
>
> **Dispatch now:** W3-00 (build closure), W3-10 (F1 partial zeta), W3-14 and W3-15 (CBC
> Flash units, unrelated to zeta).
> **Hold:** W3-01…W3-09, W3-11, W3-12 and W3-13, pending **AINTLIB-0′**
> (`aintlib-substrate.md` §A3) — a bump-first build check that runs on today's worker image
> without the multi-toolchain elan the infra queue is still holding.
>
> **UPDATED 13:00Z (addendum 2).** My first pass grepped only AINTLIB's `CompletedZeta/`
> directory. The project has two more: `ExplicitFormula/` (10 files, 713 KB) and a root
> (9 files, 321 KB). **All 35 files are live-sorry-free and axiom-free** — the 2 raw grep
> hits are prose in docstrings, which `scripts/sorry_count.py` reads correctly and `grep`
> does not. `ExplicitFormula/` is the Weil explicit formula (M4–M7) and it is **not**
> GRH-conditional: `WeilAssembly`, `PrimeSide`, `GammaSide`, `ZeroCapture` and
> `TestFunction` mention GRH zero times; it is quarantined to `GRHZeros.lean` and the root.
> Two swaps follow: **W3-12 (N19) moves to HOLD** — it is `ExplicitFormula/TestFunction.lean`
> (`IsAdmissibleTestFn`) and I called it uncovered on the strength of a too-narrow grep —
> and **W3-10 (F1) is RELEASED**, since no partial-zeta Dirichlet object exists in any of
> the 35 files. What AINTLIB does *not* have is the Odlyzko endgame: its root theorem is
> Belabas–Friedman **under GRH**, not the unconditional `|discr K| ≥ 8.25^n`. See §A5–A9.
>
> **UPDATED 13:30Z (addendum 3).** The two coverage claims §A9 flagged as signature-level
> are now checked. Both hold, both leave a small bridge. (a) `IsAdmissibleTestFn` is
> Belabas–Friedman's class, **not** my N19 `𝓕` — it is *broader*, `𝓕 ⊆ IsAdmissibleTestFn`,
> and it carries `jump_avg`, which **retires the N19 conditional-convergence risk note
> outright** rather than merely avoiding it. (b) `GammaStrip`'s bounds are windowed to
> `[-1/2, 3/2]` plus an upward recurrence extension, not N3's general `[a,b]`; but their
> shape (linear in `‖z‖`) is stronger than N3's crude `(1+|t|)^A`, so nothing downstream
> loses. Two **post-port** S-sized residuals follow — a `𝓕 → IsAdmissibleTestFn` inclusion
> (or restate over the broader class and skip it), and a general-strip wrapper that drops
> N3 from M to S. Neither is dispatchable now; both are bridges onto code not yet in FLT.
> Cut them when AINTLIB-2 lands. See §A10–A12.
>
> The one thing not verified: AINTLIB has no Lean build CI, so sorry-free by grep is not
> the same as compiles. AINTLIB-0′ is precisely that experiment. If it comes back red, the
> twelve held units release immediately and nothing is lost but the hold.

Two things changed since wave 2 was written and both change what a packet must contain:

1. **The baseline moved to 56 live / 67 naive** (PR #8 closed four holes). Every delta
   below is relative and so unaffected, but a packet still carrying the constant `71`, or
   even `60`, false-fails. Read the constant off `oracle-recount.md` §0, never off a packet.
2. **`lake build` does not compile every file the oracle counts** —
   `oracle-recount.md` §8. `lakefile.toml` makes the default target the import closure of
   `FLT.lean`, and `FLT.lean` is a hand-maintained list. `FLT/MazurW.lean` and
   `FLT/PoitouTate.lean` are outside it today. **Every packet in this wave creates new
   files, so every packet in this wave is exposed to it**, and gate clause 8 exists to
   close it. Dispatch **W3-00 first** — it is five minutes of work and it tells us whether
   the C1 calibration file has ever been type-checked.

---

## 1. Packet contract v2 (applies to every envelope in this document)

The wave-2 contract, plus clause 8 and a corrected clause 2.

**Acceptance gate**

1. **Acceptance runs in the isolated `flt-acceptance` harness — a raw `lake build` in the
   reviewed worktree is not acceptance evidence.** (C2 lesson, 2026-08-16.) A worktree-local
   build can go green off the worker's own build state, so it is not reproducible from the
   reviewed tree alone. The isolated runner must exit 0. **This composes with clause 8 and
   does not replace it:** an isolated runner that does not also assert build closure just
   reproduces the same vacuity in a cleaner container — a new file nothing imports compiles
   green by not being compiled at all.
2. `scripts/sorry_count.py --json` reports `live == 56 + declared_delta`, with
   `declared_delta` inside the packet's budget, **and** `prose == 11`. The live count, not
   the naive one — the naive count is 67 and includes 11 prose occurrences that no packet
   in this wave may touch.
3. `git diff` against the base is confined to the declared `write_paths`.
4. For negative deltas, the target theorem *statement* is byte-identical to base; only
   removed lines may be `sorry` lines. Rejects proving-by-weakening.
5. No new `axiom` keyword anywhere in the diff. (`FLT/Assumptions/*` is off limits to this
   wave entirely.)
6. No modification of any line matching `sorry`/`admit` that is not the declared target.
   `scripts/sorry_count.py --prose` prints the 11 lines this protects.
7. New files carry the repo module idiom: Apache-2.0 header block, `module`,
   `public import …` lines, `@[expose] public section`, a `/-! # … -/` module docstring
   with a `## Main definitions` / `## Main results` section. Copy the shape of
   `FLT/Mathlib/Algebra/Algebra/Bilinear.lean`.
8. **(new) Build closure.** Every `.lean` file in `write_paths` must be reachable from
   `FLT.lean` by `public import` after the diff. For a packet that creates a file, the diff
   **must** add the alphabetized `public import` line to `FLT.lean` — that line is part of
   `write_paths` and is not optional. Verify with `scripts/sorry_count.py --closure`, which
   exits 1 if any module under `FLT/` is orphaned. A packet that skips this gets a green
   `lake build` that never compiled its own file.

**Two standing instructions to the worker**

- **Statements below are targets, not transcriptions.** Each envelope gives the intended
  mathematical content and the Mathlib declarations to build on. Adapt the exact Lean
  syntax to the pinned Mathlib (`bc06ce9f`); do not weaken the content to make it compile.
  If the honest statement needs a hypothesis not listed, add it and say so in the receipt.
- **Port before you prove.** For every Part-A/B node, prior art exists (AINTLIB's
  `projects/DedekindResidue/CompletedZeta/`, Vilin97/lean-pool's `LeanPool/Odlyzko/`).
  Check `aintlib-substrate.md` first. Porting a sound proof is the expected mode and is
  worth more than a fresh one, because it is upstreamable.

**Mathlib anchors are verified, not remembered.** Every Mathlib file cited below was
fetched from `leanprover-community/mathlib4` at the pinned rev `bc06ce9f` this session and
grepped for the declaration named. Confirmed present: `Complex.borelCaratheodory` and
`borelCaratheodory_zero` (`Analysis/Complex/BorelCaratheodory.lean:86,109`), `WeakFEPair`
with its 11 fields (`NumberTheory/LSeries/AbstractFuncEq.lean:80`), `Complex.digamma` /
`digamma_apply_add_one` / `meromorphic_digamma`
(`Analysis/SpecialFunctions/Gamma/Digamma.lean`), `mFourierCoeff` and the
`hasSum_mFourier…` family (`Analysis/Fourier/AddCircleMulti.lean`),
`NumberField.dedekindZeta` (`NumberTheory/NumberField/DedekindZeta.lean`),
`AnalyticOnNhd.sum_divisor_le` and `MeromorphicOn.circleAverage_log_norm`
(`Analysis/Complex/JensenFormula.lean`), `Gammaℝ_def` / `Gammaℂ_def` /
`differentiable_Gammaℝ_inv` (`Analysis/SpecialFunctions/Gamma/Deligne.lean`).
Confirmed **absent from Mathlib**: `Mathlib/Algebra/Module/ZLattice/Dual.lean` does not
exist at the pin, and neither `ZLattice/Basic.lean` nor `ZLattice/Covolume.lean` mentions a
dual lattice. I originally concluded from this that A1 was genuinely new work. **That
conclusion was wrong** — absent from Mathlib is not absent from the world. AINTLIB's
`CompletedZeta/DualLattice.lean` has it, sorry-free (`dualZLattice`, `mem_dualZLattice`,
`dualZLattice_eq_span`, `covolume_dualZLattice_mul` — the last of which is node A2 as
well). The Mathlib check told me it was upstreamable, not that it was unproved.

---

## 2. Standing ready set, revalidated at `daac1f2`

| Packet | Verdict at `daac1f2` | Evidence |
|---|---|---|
| hub-oig35.3 (A14 Pontryagin) | **READY — dispatch, but re-declare the constant** | Hole live at `FLT/Patching/Utils/CompactHausdorffRings.lean:42`, `theorem Group.subsingleton_of_pow_prime_eq_one`, statement byte-identical to the wave-2 check. Delta `[-1,-1]` ⇒ acceptance is **live 55 / naive 66**. A packet still carrying 70 or 71 false-fails. Prose occurrence at line 89 of the same file — gate clause 6 binds. File is in the build closure (imported via `FLT/Patching/…`), so clause 8 is satisfied already. |
| hub-oig35.20 v2 | **DONE** | Merged as `b0fbbec` (PR #8, 11:40:11Z). Delta `[-4,-4]` honoured; the v2 route from `oig35-20-refinement.md` §4 was used verbatim. |
| hub-oig35.18 (C1) | **MERGED, but its calibration value is in question** | Merged as `8ea4f0a` (PR #7, 11:08:35Z). It changed only the witness curve in `FLT/MazurW.lean` — which is outside the build closure (`oracle-recount.md` §8). Its `lake build` plausibly never compiled the file it edited. **W3-00 settles this.** |
| hub-oig35.10 (`loc_cst`) | **STALE — do not requeue; close PR #6** | Confirmed at byte level this session, not inherited: PR #6's entire diff is `FLT/GlobalLanglandsConjectures/GLzero.lean` +2/−2, replacing `sorry` (and a `-- aesop -- used to work` comment) with `intro x` / `simpa using isOpen_univ` at `loc_cst`. Those two lines are **already on main verbatim** at `GLzero.lean:66–69`. The PR is a no-op against current main, so sorry-count acceptance is impossible for it and merging it gains nothing. It is still open with a green check. Close it. |
| hub-oig35.5 / .8 / .9 / .11 / .12 / .16 | **STILL UNVERIFIABLE FROM THIS POD** | Target holes recorded only in beads metadata. The Secret Manager grant landed this morning and the bridge now authenticates me, but it rejects every command I send (`command_rejected`, including an empty argv) — see `outbox/BLOCKERS.md`. The complete live-hole inventory is `oracle-recount.md` §2–3, so each of the six is a one-line check the moment a command scope is granted. **Do not dispatch them unverified.** |

---

## 3. Dispatch board

16 units, no unmet dependencies among them, no shared write paths. All 16 can run
concurrently; at the charter's 3–6 concurrency this is roughly a full day of pool time.

| ID | Node | Tier | Size | Creates | Δ |
|---|---|---|---|---|---|
| **W3-00** | Build-closure repair | Flash | XS | `FLT.lean` only | `[0,0]` |
| W3-01 | A3 Poisson summation on `ℤ^d` | Pro | M | `FLT/Mathlib/Analysis/Fourier/PoissonSummationMulti.lean` | `[0,0]` |
| W3-02 | A1 Dual lattice | Pro | S | `FLT/Mathlib/Algebra/Module/ZLattice/Dual.lean` | `[0,0]` |
| W3-03 | F2a Deligne Gamma integrals | Pro | S | `FLT/Mathlib/Analysis/SpecialFunctions/Gamma/DeligneIntegrals.lean` | `[0,0]` |
| W3-04 | N2 Gamma modulus identities | Pro | S | `FLT/Mathlib/Analysis/SpecialFunctions/Gamma/ModulusIdentities.lean` | `[0,0]` |
| W3-05 | N5 Borel–Carathéodory off-center | Pro | S | `FLT/Mathlib/Analysis/Complex/BorelCaratheodoryOffCenter.lean` | `[0,0]` |
| W3-06 | N6 Holomorphic logarithm on a disk | Pro | S | `FLT/Mathlib/Analysis/Complex/HolomorphicLog.lean` | `[0,0]` |
| W3-07 | A5 Anisotropic Gaussian on the mixed space | Pro | S | `FLT/NumberField/Zeta/Gaussian.lean` | `[0,0]` |
| W3-08 | B1 Trace pairing vs mixed-space pairing | Pro | S | `FLT/NumberField/Zeta/TracePairing.lean` | `[0,0]` |
| W3-09 | F3a Unit-orbit ↔ ideal bijection | Pro | S | `FLT/NumberField/Zeta/OrbitIdeal.lean` | `[0,0]` |
| W3-10 | F1 Partial zeta functions | Pro | S | `FLT/NumberField/Zeta/Partial.lean` | `[0,0]` |
| W3-11 | D1 Polar decomposition of parameter space | Pro | M | `FLT/NumberField/Zeta/Domain.lean` | `[0,0]` |
| W3-12 | N19 Test-function transform decay | Pro | M | `FLT/Odlyzko/TestFunctions.lean` | `[0,0]` |
| W3-13 | N1 M2→M3 interface statement pack | Flash | S | `FLT/Odlyzko/Interface.lean` | `[+6,+9]` |
| W3-14 | CBC-S8 Chebotarev comparison lemma | Flash | S | `FLT/CyclicBaseChange/Chebotarev.lean` | `[+1,+2]` |
| W3-15 | CBC-S2 Norm on Satake data | Flash | S | `FLT/CyclicBaseChange/Satake.lean` | `[+2,+3]` |

**Δ is the declared `sorry`/`admit` budget.** Every Pro unit is `[0,0]`: a new file with
complete proofs adds no holes and closes none. That makes the count gate a *tripwire* for
these packets rather than a measurement — if a Pro packet reports anything other than 0,
the worker left a `sorry` in and the packet is not done. Flash units carry a positive
budget because scaffolding holes is the deliverable.

**MAZ-W and the rest of the wave-2 Mazur Flash tier are deliberately held back.** They
target `FLT/MazurW.lean`, which is orphaned; scaffolding more statements into a file the
build never reads would compound the §8 problem. Requeue them after W3-00 reports.

---

## 4. Envelopes

Each block is the complete packet. `write_paths` is exhaustive: a diff touching anything
else fails clause 3.

### W3-00 — Build-closure repair *(dispatch first)*

- **Tier/size:** Flash / XS. **Δ `[0,0]`.** **write_paths:** `FLT.lean`.
- **Task:** add exactly two lines to `FLT.lean`, in alphabetical position among the
  existing `public import` block:
  ```
  public import FLT.MazurW
  public import FLT.PoitouTate
  ```
- **Why:** those two modules are the only files under `FLT/` outside the default build
  target's import closure. They hold 3 of the 56 live sorries, so the oracle counts them,
  but `lake build` does not compile them (`oracle-recount.md` §8).
- **Acceptance, and this is the point of the packet:** report the `lake build` result
  **whether or not it is green**. This is a diagnostic packet.
  - **Green** ⇒ the two files compile, the closure is repaired, and C1's calibration
    evidence stands. Merge.
  - **Red** ⇒ the packet has done its job: it has found errors in code that four merged
    packets were accepted against. **Do not fix them in this packet.** Report the full
    error list, revert the two lines, and cut a repair packet per failing declaration.
- **Note for the reviewer:** `FLT/MazurW.lean` is the C1 file and `FLT/PoitouTate.lean` is
  a chapter-node file; a red result here is *expected to be informative*, not embarrassing.
  Nothing has type-checked either file since it was written.

### W3-01 — A3, Poisson summation on `ℤ^d`

- **Tier/size:** Pro / M. **Δ `[0,0]`.**
- **write_paths:** `FLT/Mathlib/Analysis/Fourier/PoissonSummationMulti.lean`, `FLT.lean`.
- **Target:** for `f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ`,
  `∑' m : Fin d → ℤ, f m = ∑' k : Fin d → ℤ, 𝓕f k`, with both sums over the standard
  lattice and `𝓕` the Fourier transform normalized `𝓕f ξ = ∫ f x * exp(−2πi⟪x,ξ⟫)`.
  A corollary form with explicit continuity + `rpow`-decay hypotheses, mirroring the 1-D
  `Real.tsum_eq_tsum_fourier_of_rpow_decay`, is optional and welcome.
- **Mathlib anchors:** `Mathlib.Analysis.Fourier.AddCircleMulti` (`mFourierCoeff`, the
  `hasSum_mFourier…` family — verified present at the pin), `SchwartzMap.decay`,
  `Real.fourierIntegral`, and the 1-D `Real.fourierCoeff_tsum_comp_add` as the shape to
  imitate.
- **Sketch:** periodize `F x = ∑_m f (x + m)`; show `mFourierCoeff F k = 𝓕f k` by unfolding
  the torus integral against the fundamental cube; evaluate the uniformly convergent
  Fourier series at `x = 0`. Summability of the coefficients comes from Schwartz decay of
  `𝓕f`.
- **Why first:** the single most load-bearing prerequisite in the M2 tree, and
  `AddCircleMulti` was visibly built as groundwork for exactly this. **Upstreamable to
  Mathlib as-is** — open the Mathlib PR in the same session and record its number in the
  receipt.

### W3-02 — A1, dual lattice

- **Tier/size:** Pro / S. **Δ `[0,0]`.**
- **write_paths:** `FLT/Mathlib/Algebra/Module/ZLattice/Dual.lean`, `FLT.lean`.
- **Target:** for a full `ℤ`-lattice `L` in a finite-dimensional real inner-product space,
  define `ZLattice.dual L = {x | ∀ v ∈ L, ⟪x, v⟫ ∈ ℤ}`; prove it is itself a full
  `ZLattice`, that it is spanned by the dual basis of any `ℤ`-basis of `L`, that
  `dual (dual L) = L`, and `dual (ℤ^d) = ℤ^d`.
- **Mathlib anchors:** `ZLattice` (`Algebra/Module/ZLattice/Basic.lean`), `Basis.dualBasis`,
  `BilinForm.dualBasis`. **Verified absent at the pin:** there is no
  `Algebra/Module/ZLattice/Dual.lean` and no mention of a dual in `Basic` or `Covolume`.
  This is new work; the path above mirrors where it belongs upstream.
- **Sketch:** express membership in coordinates of a `ℤ`-basis; the dual basis is the
  Gram-matrix-inverse combination.
- **Unlocks:** the entire B/C column (A2, A4, B2). Also independently wanted by Mathlib —
  upstream it.

### W3-03 — F2a, Deligne-normalized Gamma integrals

- **Tier/size:** Pro / S. **Δ `[0,0]`.**
- **write_paths:**
  `FLT/Mathlib/Analysis/SpecialFunctions/Gamma/DeligneIntegrals.lean`, `FLT.lean`.
- **Target:** the two one-dimensional building blocks, for `c > 0` and `Re s > 0`:
  `∫₀^∞ exp(−π y c) · y^{s/2} dy/y = Gammaℝ s · c^{−s/2}` (real place), and the complex-place
  analogue `∫₀^∞ exp(−2π y c) · y^{s} dy/y = (1/2) · Gammaℂ s · c^{−s}` up to the `2π` factor
  — **pin the exact constant against `Gammaℂ_def` inside the node and state it explicitly.**
- **Mathlib anchors:** `Gammaℝ_def`, `Gammaℂ_def` (verified present in
  `Analysis/SpecialFunctions/Gamma/Deligne.lean`), `Complex.Gamma_eq_integral`,
  `Mathlib.Analysis.MellinTransform` substitution lemmas.
- **Sketch:** substitute `u = π c y` in the Euler integral. Pure 1-D calculus.
- **Constant discipline:** the `2`-powers from `ℂ ≅ ℝ²` are the classical error magnet of
  this whole tree (`zeta-fe-decomposition.md` risk note 1). This node is where the
  convention is *fixed*; every later node cites it. Write the constant into the statement,
  not into a comment.

### W3-04 — N2, exact Gamma modulus identities

- **Tier/size:** Pro / S. **Δ `[0,0]`.**
- **write_paths:**
  `FLT/Mathlib/Analysis/SpecialFunctions/Gamma/ModulusIdentities.lean`, `FLT.lean`.
- **Target:** for real `t ≠ 0`, `‖Γ(1 + it)‖² = π t / sinh (π t)` and
  `‖Γ(1/2 + it)‖² = π / cosh (π t)`.
- **Mathlib anchors:** `Complex.Gamma_mul_Gamma_one_sub`
  (`Analysis/SpecialFunctions/Gamma/Beta.lean`), `Complex.Gamma_conj`,
  `Complex.Gamma_add_one`, the `Complex.sin` addition formulas.
- **Sketch:** apply the reflection formula at `s = it` and at `s = 1/2 + it`;
  `Γ(conj s) = conj (Γ s)` turns each product into a squared modulus; convert
  `sin(π i t)` to `sinh` and `cos` to `cosh`.
- **Critical-path note:** N2 is the root of the M3 tree's deepest chain
  (N2 → N3 → N10 → N11 → N13 → N16 → N17 → N21, eight nodes). **If it is not in the first
  batch, the M3 tree becomes the campaign's long pole.** Dispatch it with W3-01.

### W3-05 — N5, Borel–Carathéodory in off-center form

- **Tier/size:** Pro / S. **Δ `[0,0]`.**
- **write_paths:** `FLT/Mathlib/Analysis/Complex/BorelCaratheodoryOffCenter.lean`,
  `FLT.lean`.
- **Target:** for `f` differentiable on `ball c R` and `0 < r < R`,
  `sup_{ball c r} ‖f‖ ≤ (2r/(R−r)) · sup_{ball c R} (Re f) + ((R+r)/(R−r)) · ‖f c‖`.
- **Mathlib anchor, verified verbatim at the pin** —
  `Mathlib/Analysis/Complex/BorelCaratheodory.lean:109`:
  ```lean
  public theorem borelCaratheodory (hM : 0 < M) (hf : DifferentiableOn ℂ f (ball 0 R))
      (hf₁ : Set.MapsTo f (ball 0 R) {z | z.re ≤ M}) (hR : 0 < R) (hz : z ∈ ball 0 R) …
  ```
  with `borelCaratheodory_zero` at line 86 giving `‖f z‖ ≤ 2*M*‖z‖/(R − ‖z‖)` under
  `f 0 = 0`.
- **Sketch:** translate `z ↦ z − c` and rescale. **This is API glue, not a theorem** — the
  mathematics is already in Mathlib. If it takes more than a short session, the packet has
  gone wrong; escalate rather than pushing on.
- **Note:** Mathlib's hypothesis is `MapsTo f (ball 0 R) {z | z.re ≤ M}`, i.e. a bound on
  `Re f` rather than a supremum. Consuming nodes (N4, N7) want the `sup Re` phrasing;
  supply both forms so callers do not each re-derive the conversion.

### W3-06 — N6, holomorphic logarithm on a disk

- **Tier/size:** Pro / S. **Δ `[0,0]`.**
- **write_paths:** `FLT/Mathlib/Analysis/Complex/HolomorphicLog.lean`, `FLT.lean`.
- **Target:** if `f` is analytic and nonvanishing on `ball c R`, there is an analytic `L` on
  that ball with `exp ∘ L = f`, `Re L = log ‖f‖`, and `deriv L = logDeriv f`.
- **Mathlib anchors:** `DifferentiableOn.isExactOn_ball` (primitives on a disk,
  `Analysis/Complex/HasPrimitives.lean`), `Complex.exp_log`, the `logDeriv` API.
- **Sketch:** let `L` be a primitive of `f′/f` on the ball, adjusted by a constant so that
  `exp (L c) = f c`; then `f · exp(−L)` has zero derivative on a connected set, hence is
  constantly `1`.
- **Pairs with:** W3-05. N5 + N6 together are the whole "zero-machinery kernel" prerequisite
  (N7). Dispatch them to the same worker if the pool allows — they share no files, so this
  is a scheduling preference, not a dependency.

### W3-07 — A5, anisotropic Gaussian on the mixed space and its Fourier transform

- **Tier/size:** Pro / S. **Δ `[0,0]`.**
- **write_paths:** `FLT/NumberField/Zeta/Gaussian.lean`, `FLT.lean`.
- **Target:** for a number field `K` with mixed space `E_K = mixedSpace K` and a parameter
  `y ∈ (0,∞)^{InfinitePlace K}`, define
  `gauss y x = exp(−π ∑_v n_v y_v ‖x_v‖²)` (`n_v ∈ {1,2}` the local degree). Prove `gauss y`
  is a `SchwartzMap`, and compute `𝓕 (gauss y)` as an explicit constant
  `∏_v (n_v y_v)^{−n_v/2}` times the Gaussian at the reciprocal parameter. **Fix the exact
  constant in the statement** — it is forced by the 1-D computation, and it is the one that
  propagates into C2 and F3b.
- **Mathlib anchors:** `fourierIntegral_gaussian_pi`,
  `fourier_gaussian_innerProductSpace'`, `NumberField.mixedEmbedding.mixedSpace` and its
  `WithLp 2` Euclidean structure (set up at `CanonicalEmbedding/Basic.lean:815`).
- **Sketch:** the function is a product over places, so the transform factorizes into 1-D
  transforms at real places and 2-D (`ℂ ≅ ℝ²`) transforms at complex places.
- **Constant discipline:** as W3-03. The `2^{r₂}` bookkeeping here is checked end-to-end
  much later by the optional H1 residue node against Roblot's independently proved
  `dedekindZeta_residue`; until then it is unverified, so state it precisely.

### W3-08 — B1, trace pairing vs the mixed-space pairing

- **Tier/size:** Pro / S. **Δ `[0,0]`.**
- **write_paths:** `FLT/NumberField/Zeta/TracePairing.lean`, `FLT.lean`.
- **Target:** for `α β : K`, `Trace_{K/ℚ}(α·β) = B(ι α, ι β)` where `ι = mixedEmbedding K`
  and `B` is the explicit **bilinear** (not sesquilinear) form on `E_K`,
  `B(x,y) = ∑_{v real} x_v y_v + ∑_{v complex} 2 · Re (z_v w_v)`.
- **Mathlib anchors:** `Algebra.trace_eq_sum_embeddings`, the
  `NumberField.InfinitePlace` embedding / conjugate-pair API.
- **Sketch:** group the `n` complex embeddings into `r₁` real ones and `r₂` conjugate pairs;
  each pair contributes `σα·σβ + conj(σα·σβ) = 2 Re(σα·σβ)`.
- **Trap, stated so the worker does not fall in it:** the trace pairing is bilinear while
  the inner product is sesquilinear-shaped at complex places. There is **no conjugation** in
  `B`. Carrying this distinction explicitly is the whole content of the node, and B2
  downstream depends on it being right.

### W3-09 — F3a, unit-orbit ↔ ideal bijection

- **Tier/size:** Pro / S. **Δ `[0,0]`.**
- **write_paths:** `FLT/NumberField/Zeta/OrbitIdeal.lean`, `FLT.lean`.
- **Target:** for a nonzero fractional ideal `I`, the map `α ↦ (α)·I⁻¹` induces a bijection
  `(I ∖ {0}) / 𝓞ˣ ≃ {𝔟 integral : [𝔟] = [I]⁻¹}`; each orbit meets a torsion-free section in
  exactly `w = torsionOrder K` elements; and `|Norm_{K/ℚ} α| = N((α)I⁻¹) · N I`.
- **Mathlib anchors:** `ClassGroup`, `Ideal.span_singleton`, `FractionalIdeal` arithmetic.
  The `I = 𝓞` special case already exists as `fundamentalCone.integerSet` /
  `idealSetEquivNorm` in `NumberTheory/NumberField/CanonicalEmbedding/FundamentalCone.lean`
  — **read that file first; this node is largely its generalization.**
- **Sketch:** pure ideal arithmetic. Two elements generate the same `(α)I⁻¹` exactly when
  they differ by a unit.

### W3-10 — F1, partial zeta functions

- **Tier/size:** Pro / S. **Δ `[0,0]`.**
- **write_paths:** `FLT/NumberField/Zeta/Partial.lean`, `FLT.lean`.
- **Target:** for an ideal class `A`, define `ζ(A, s) = ∑_{𝔟 integral, [𝔟] = A} (N 𝔟)^{−s}`;
  prove absolute convergence and analyticity on `Re s > 1`, that
  `∑_{A : ClassGroup 𝓞} ζ(A, s) = dedekindZeta K s` there, and the crude bound
  `ζ(A, s) = O(ζ(Re s))`.
- **Mathlib anchors:** `NumberField.dedekindZeta` (verified present in
  `NumberTheory/NumberField/DedekindZeta.lean`), the `LSeries` summability API,
  `Ideal.tendsto_norm_le_div_atTop₀` for crude counting, `tsum` sigma-type reindexing.
- **Sketch:** absolutely convergent rearrangement over the fibration
  `ideals → (norm n, ideals of norm n)`; the class-group sum is finite, so the splitting is
  a finite regrouping of an absolutely convergent series.

### W3-11 — D1, polar decomposition of the parameter space

- **Tier/size:** Pro / M. **Δ `[0,0]`.**
- **write_paths:** `FLT/NumberField/Zeta/Domain.lean`, `FLT.lean`.
- **Target:** with `Y = (0,∞)^{InfinitePlace K}` and `Nm y = ∏_v y_v^{n_v}`, define the
  norm-one surface `S = Nm⁻¹ {1}` and construct a measure-preserving homeomorphism
  `Y ≅ (0,∞) × S`, `y = t^{1/n} • s`, carrying the multiplicative Haar measure
  `⊗_v dy_v/y_v` to `(dt/t) ⊗ μ_S`; `μ_S` is invariant under the multiplicative action of
  `S` on itself and under `s ↦ s⁻¹`.
- **Mathlib anchors:** the `expMap` / `logSpace` machinery in
  `NumberTheory/NumberField/CanonicalEmbedding/NormLeOne.lean` (Roblot), Haar pushforward
  along the log iso `Y ≅ ℝ^{r₁+r₂}`, product-measure splitting along
  `x ↦ (∑ n_v x_v, x − mean)`.
- **Sketch:** transport everything along `log` to a linear direct-sum decomposition of
  `ℝ^{r₁+r₂}` into the weighted diagonal and the trace-zero hyperplane; both summands carry
  Lebesgue measure and the splitting is measure-preserving.
- **Risk, contained here:** measure plumbing through `exp`/polar coordinates is routine but
  fiddly. Roblot's `NormLeOne` machinery already does the hard half for the class-number
  formula — **reuse it aggressively rather than rebuilding it.** If this node starts to
  look L-sized, that is the signal that it was rebuilt instead of reused; stop and say so.

### W3-12 — N19, test-function transform decay

- **Tier/size:** Pro / M. **Δ `[0,0]`.**
- **write_paths:** `FLT/Odlyzko/TestFunctions.lean`, `FLT.lean`.
- **Target:** freeze the Poitou test class `𝓕` — `F` even, compactly supported, Lipschitz,
  with `F′` of bounded variation — and prove that for `F ∈ 𝓕`,
  `Φ_F(s) = ∫ F(x) exp((s − 1/2) x) dx` is entire with
  `‖Φ_F(ρ)‖ ≤ C_F (1 + |Im ρ|)^{−2}` uniformly on the closed strip `0 ≤ Re ρ ≤ 1`.
- **Mathlib anchors:** the `intervalIntegral.integral_comp_smul_deriv` family for
  integration by parts, `BoundedVariationOn` / `StieltjesFunction`, `Complex.exp` bounds.
- **Sketch:** integrate by parts twice — once against Lipschitz `F`, once against the
  Stieltjes measure `dF′`. On the closed strip `‖exp((s−1/2)x)‖ ≤ exp(|x|/2)`, and `x`
  ranges over a compact set.
- **Contract a worker must not silently break:** `𝓕` is consumed by M7/M8/M9. Freezing it
  this way is what buys *absolute* convergence in N20 and dodges Weil's conditional
  symmetric-limit machinery. **If a downstream node later needs a discontinuous `F`, N20
  must be redone with symmetric limits — escalate at M7 assembly rather than quietly
  widening `𝓕` here.** Widening the class in this file is the single most expensive silent
  mistake available in the M3 tree.

### W3-13 — N1, M2→M3 interface statement pack

- **Tier/size:** Flash / S. **Δ `[+6,+9]`.**
- **write_paths:** `FLT/Odlyzko/Interface.lean`, `FLT.lean`.
- **Target:** a statement-only file declaring, as `sorry`-carrying theorems, exactly the M2
  facts the M3 tree consumes: `completedDedekindZeta` meromorphic with simple poles exactly
  at `{0,1}`; `Λ_K(s) = Λ_K(1−s)`; agreement with `NumberField.dedekindZeta` on `Re s > 1`;
  `Λ_K` real and positive on `(1,∞)`; and nonvanishing on `Re s > 1` **stated as a
  hypothesis parameter**, since it belongs to the parent map's Euler-product node M1, not
  here.
- **No new mathematics.** This is statement curation, which is exactly why it is Flash: the
  gate is mechanical (compiles, delta in budget, paths confined).
- **Why it is dispatchable now despite depending on G1/G4/G5:** the deliverable is the
  *interface*, parametrized over the M2 results as hypotheses. It can and should be written
  before M2 is proved — that is what lets the M3 tree start in parallel with the M2 tree.
  When G5 lands, this file's sorries are discharged by citation, one line each.
- **Reviewer instruction:** check the *statements*, hard. A wrong statement here propagates
  into the entire M3 tree and is discovered only at assembly. The normalization to match is
  `Λ_K(s) = |d_K|^{s/2} · Gammaℝ(s)^{r₁} · Gammaℂ(s)^{r₂} · ζ_K(s)`, fixed in
  `zeta-fe-decomposition.md`.

### W3-14 — CBC-S8, Chebotarev comparison lemma

- **Tier/size:** Flash / S. **Δ `[+1,+2]`.**
- **write_paths:** `FLT/CyclicBaseChange/Chebotarev.lean`, `FLT.lean`.
- **Target:** state that two continuous representations `ρ, ρ'` of a global Galois group,
  agreeing on characteristic polynomials of Frobenius outside a finite set of places, are
  isomorphic (semisimplified). Statement only, with the finite exceptional set and the
  semisimplicity hypothesis explicit.
- **Highest-leverage single Flash unit in wave 2 or 3:** three separate hubs consume this
  wrapper (`cbc-reconciled.md`, `ret-middle-decomposition.md` node T3, and the
  Galois-representations chapter). Dispatch it early even though it is small.
- **Anchor:** the shared-wrapper role is recorded in `ret-middle-decomposition.md` (T3);
  match that statement's shape so the three consumers can cite one declaration.

### W3-15 — CBC-S2, norm on Satake data

- **Tier/size:** Flash / S. **Δ `[+2,+3]`.**
- **write_paths:** `FLT/CyclicBaseChange/Satake.lean`, `FLT.lean`.
- **Target:** a stub `SatakeParam` structure and the norm map on Satake data used by the
  base-change comparison, with its defining property stated as a `sorry`-carrying lemma.
- **Source:** `cbc-reconciled.md` §7, "ready-now statement candidates". Pure algebra against
  the stub; deliberately independent of S3/S4, which are blocked on the Hecke-action half of
  S1 (`HeckeOperators/Concrete.lean`, only partially built).

---

## 5. Ordering

Nothing here blocks anything else here, so the only real constraints are these four:

1. **W3-00 goes first, alone.** It is minutes of work and it decides whether C1 counts as
   calibration evidence. Do not batch it — a red result must be attributable to those two
   import lines and nothing else.
2. **Run AINTLIB-0 (the build gate in `aintlib-substrate.md`) before dispatching zeta-tree
   work beyond this wave.** A green AINTLIB-0 turns roughly 22 of the 24 M2 nodes into a
   port instead of a proof. The 16 units here are safe to start regardless — they are the
   nodes a port would have to be reconciled against anyway — but committing the pool to the
   dependent nodes before the port answer is known would be waste.
3. **W3-04 (N2) must be in the first batch.** It is the root of the M3 tree's eight-node
   critical path; every hour it waits is an hour on the campaign's long pole.
4. **W3-01 and W3-02 should open Mathlib PRs.** Both are Mathlib-generic and independently
   wanted upstream. Coordinate with the maintainers named in
   `zeta-fe-decomposition.md` (D. Loeffler, X. Roblot, M. Stoll) and with C. Birkbeck
   before starting, per the standing coordination requirement.

~~Suggested first batch at 6-way concurrency, after W3-00 reports: W3-01, W3-02, W3-03,
W3-04, W3-05, W3-14.~~ **Withdrawn 12:52Z — five of those six are covered sorry-free by
AINTLIB** (see the correction at the top of this file and `aintlib-substrate.md` §A2).

**Corrected first batch:** `W3-00` → then **AINTLIB-0′** (`aintlib-substrate.md` §A3) as
the single highest-priority packet in the campaign, with `W3-14`, `W3-15` and `W3-12`
running alongside it since none of the three touches the zeta tree. Everything else waits
on AINTLIB-0′'s verdict. That is three concurrent units rather than six, which is the
correct trade: the pool is not short of capacity, it is one build-check away from knowing
whether twelve of its queued units are necessary at all.

Constraint 2 above understated this. It said to run the AINTLIB gate "before dispatching
zeta-tree work beyond this wave". The gate belongs *before this wave*, and the reason
constraint 2 was too weak is that it was written from the port audit's summary rather than
from the source.

## 6. What is *not* verified in this document

Stated plainly so nobody treats it as more solid than it is.

- **No Lean was run.** crew-18 has no toolchain by design. Every claim here is textual:
  line numbers, statements, counts, import graphs, and files fetched from the pinned Mathlib
  rev. Nothing below "it compiles" is asserted, and the `[0,0]` deltas are budgets, not
  measurements.
- **The §8 build-closure finding is a reading of `lakefile.toml` plus a complete grep**, not
  an observed build. W3-00 is the experiment that settles it. If Lake's bare-name glob
  semantics differ from that reading, W3-00 goes green trivially and costs nothing.
- **Six standing ready-set packets (hub-oig35.5/.8/.9/.11/.12/.16) remain unverified.**
  Their targets live only in beads metadata and the bridge still rejects every command from
  this pod. They are excluded from this wave on purpose.
- **The Mathlib anchors are verified to exist**, by fetching each file at rev `bc06ce9f` and
  grepping for the declaration. That they exist does not mean the proof sketches close —
  the sketches are inherited from `zeta-fe-decomposition.md` and
  `odlyzko-m3-decomposition.md` and carry those documents' confidence, not more.
