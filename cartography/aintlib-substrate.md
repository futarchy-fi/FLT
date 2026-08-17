# AINTLIB packet envelope — substrate requirements and pin correction (hub-lsb1u.6.10)

**Author:** fermat (crew-18), 2026-08-16. All facts below verified live against the
GitHub API and the local FLT checkout on this date; nothing here is carried over from
the pre-migration transcript.

## 1. Pin correction — `v4.33.0-rc1` is a toolchain, not an AINTLIB ref

The standing envelope says "github.com/CBirkbeck/AINTLIB @ v4.33.0-rc1". **That ref does
not exist in AINTLIB.**

- `GET /repos/CBirkbeck/AINTLIB/tags` returns exactly one tag: `sheafy-paper-v1`
  (`dd05a076`). There is no `v4.33.0-rc1` tag and no such branch.
- `v4.33.0-rc1` is the content of AINTLIB's `lean-toolchain`
  (`leanprover/lean4:v4.33.0-rc1`) — i.e. the Lean release the project builds on. It was
  read as a repo version by whoever first drafted the envelope.

**Corrected pin, to be written into the packet metadata verbatim:**

| field | value |
|---|---|
| repo | `https://github.com/CBirkbeck/AINTLIB` (public, Apache-2.0) |
| commit | `1c1c74664e40` — `main` HEAD, 2026-07-31T21:00:13Z, "Add Apache-2.0 LICENSE" |
| lean toolchain | `leanprover/lean4:v4.33.0-rc1` |
| mathlib | `3edb3c0658f6` (sole external `require`; flt-regular is vendored) |
| build targets | `Common`, `HasseWeil`, `LeanModularForms`, `«Adic spaces»`, `BernoulliRegular` |

A packet pinned by tag will fail at `lake update`; pin by SHA.

## 2. Substrate answer — two toolchains, two caches, and it is a clean ancestor

This is the question the supervisor must answer before the port packet can run.

| | FLT | AINTLIB |
|---|---|---|
| `lean-toolchain` | `leanprover/lean4:v4.34.0-rc1` | `leanprover/lean4:v4.33.0-rc1` |
| mathlib rev | `bc06ce9f87cda9bf825ecab192b115685e629898` | `3edb3c0658f6` |

Verified via the mathlib compare API:
`3edb3c0658f6...bc06ce9f87cd` → `status: ahead`, `ahead_by: 271`, **`behind_by: 0`**.

Two consequences, and the second is the good news:

1. **Multi-toolchain elan is genuinely required.** One toolchain will not serve both
   repos, and `flt-cache-manual-0816` (FLT pin `e99f1674` → mathlib `bc06ce9f`, PVC
   `caches/flt`) does **not** cover AINTLIB. A second cache key is needed —
   `caches/aintlib` at mathlib `3edb3c0658f6` / toolchain `v4.33.0-rc1` — or the first
   AINTLIB job pays a full cold mathlib build.
2. **AINTLIB's mathlib is a strict ancestor of FLT's** (`behind_by: 0`). The eventual
   forward-port is a linear 271-commit bump with no divergent history to reconcile. That
   removes the worst risk the port audit flagged; what remains is ordinary breakage across
   271 commits, not a merge conflict.

## 3. Packet envelope — emit on substrate confirmation

Three beads, strictly sequential. Do **not** cut beads 2 and 3 until bead 1 is green: the
port audit's standing risk is that AINTLIB has **no Lean build CI**, so its "builds
clean" claim is self-reported and unverified.

### AINTLIB-0 — build verification on AINTLIB's own pin (gate)
- **Tier:** Pro. **Size:** S. **Budget:** one iteration, no repair loop.
- **Substrate:** elan with `v4.33.0-rc1` installed alongside FLT's `v4.34.0-rc1`;
  network egress to `github.com` and `mathlib` release mirrors; a writable cache path.
- **Do:** clone at `1c1c74664e40`; `lake exe cache get`; `lake build` the five default
  targets; additionally build the `CompletedZeta` tree and `DedekindResidue`.
- **Acceptance:** exit 0 on `lake build`; capture and report (a) wall-clock, (b) whether
  `cache get` hit or the build went cold, (c) the exact `sorry`/`admit` count in the
  `CompletedZeta` tree, (d) any `belabas_friedman_thm1` axiom dependencies via
  `#print axioms`.
- **Why it gates:** if this is red, the ~22/24 node claim in `zeta-port-audit.md` is worth
  nothing and the zeta-FE wave must fall back to the lean-pool PARTIAL route or the
  in-repo axiom.

### AINTLIB-1 — pin bump 271 commits (only if AINTLIB-0 green)
- **Tier:** Pro. **Size:** M. **Budget:** 3 iterations.
- **Do:** on a branch of AINTLIB, set mathlib to `bc06ce9f87cd` and the toolchain to
  `v4.34.0-rc1`; fix breakage in `Common` + `CompletedZeta` only (the other default
  targets may be excluded from the build to keep the diff bounded — declare which).
- **Acceptance:** `lake build Common CompletedZeta` exit 0; no new `sorry`/`admit`
  anywhere in the diff; no new `axiom` declarations.
- **Note:** this is where the linear-ancestor finding pays off — it is a forward bump,
  not a reconciliation.

### AINTLIB-2 — port `CompletedZeta` into FLT as the arbitrary-K M2 spine
- **Tier:** Pro. **Size:** M, 2–4 beads as the port audit estimated.
- **Do:** vendor the bumped `CompletedZeta` tree under FLT with Apache-2.0 attribution
  preserved; wire it to the zeta-FE node map in `zeta-port-audit.md` §"Node map".
- **Acceptance:** FLT `lake build` clean; sorry-delta declared per the corrected oracle
  baseline in `oracle-recount.md` §0 (live baseline **56** at `daac1f2` — it was 60 when
  this line was written, and it is not 71); diff confined to declared `write_paths`; no new
  axioms; licence header present in every ported file; **gate clause 8** — every ported
  file needs its `public import` line in `FLT.lean` or it is never compiled.
- **Payoff:** ~22 of the 24 zeta-FE leaves in `zeta-fe-decomposition.md` land at once,
  which is roughly half of the 45-leaf Odlyzko wave in `wave-2-packets.md`.

## 4. What the supervisor still has to confirm

The only open substrate items, stated so they can be answered yes/no:

1. Is `elan` present in the worker image with **both** `v4.33.0-rc1` and `v4.34.0-rc1`
   installable (multi-toolchain), or is the image pinned to a single toolchain?
2. Does the worker have egress to `github.com` and to the mathlib cache endpoint at job
   time, or only to a preseeded PVC?
3. Can a second cache key `caches/aintlib` be provisioned, or must AINTLIB-0 build cold?

Answers to (1) and (2) unblock AINTLIB-0 immediately. (3) only changes its runtime budget.

---

# ADDENDUM, 2026-08-16T12:52Z — the tree is verified sorry-free, and the elan blocker is avoidable

Two things happened after §1–4 were written: Fable answered part of §4, and I read the
actual AINTLIB source instead of trusting the port audit's second-hand report. Both change
the plan. **The second one changes what wave 3 should dispatch, so read §A2 before sending
any zeta packet to the pool.**

## A1. Substrate answers received (§4, partially closed)

| §4 question | answer | source |
|---|---|---|
| (1) multi-toolchain elan in the worker image? | **NO** — image lacks `elan`; infra queued | Fable, 12:40Z |
| (2) network egress at job time? | **YES** — AINTLIB clone confirmed working from a worker | Fable, 12:40Z |
| (3) second cache key `caches/aintlib`? | still unanswered | — |

So AINTLIB-0 as specified in §3 is blocked, and only on (1). Section A3 routes around it.

## A2. The tree is sorry-free and axiom-free — verified across all 16 files, not spot-checked

`zeta-fe-decomposition.md` recorded AINTLIB's `CompletedZeta` as "reportedly sorry-free in
the files spot-checked". That hedge can be removed. I fetched all 16 files of
`projects/DedekindResidue/DedekindResidue/CompletedZeta/` at pin `1c1c74664e40` (562 KB
total) and grepped every one:

```
AnalyticControl 181K  ClassTheta 13K   DualLattice 12K    Existence 20K
FEPair 11K            FunctionalEquation 5K   GRH 2K      GammaStrip 31K
HeckeTheta 43K        IdealLattice 19K  MellinAgreement 110K  Normalisation 3K
PoissonLattice 21K    PoissonSummation 34K  ThetaEstimates 30K  ThetaLattice 28K
```

**Zero `sorry`. Zero `admit`. Zero `axiom` declarations. No `belabas_friedman` axiom
reference.** No `IsTotallyComplex` anywhere either — everything is stated for an arbitrary
number field `K`, which is what this campaign needs and more than the lean-pool effort
offers.

And it lands the actual target. `Existence.lean:369` and `:412`:

```lean
/-- **Hecke's theorem — the completed Dedekind zeta function exists** … -/
theorem exists_isCompletedDedekindZeta :
    ∃ Λ : ℂ → ℂ, IsCompletedDedekindZeta K Λ := …

/-- **The functional equation** `Λ_K(1-s) = Λ_K(s)` … -/
theorem completedDedekindZeta_one_sub (s : ℂ) :
    completedDedekindZeta K (1 - s) = completedDedekindZeta K s := by
  have hfe := (heckeFEPair K).functional_equation (s/2) …
```

Note what that proof is built on: **Mathlib's `WeakFEPair`** — the exact engine
`zeta-fe-decomposition.md` selected for node G1. And `Normalisation.lean:41` defines
`gammaFactor K s = Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K`, with
`completedZetaPrefactor K s = |Δ_K|^{s/2} * gammaFactor K s` — **byte-for-byte the
normalization this campaign froze** in `zeta-fe-decomposition.md` ("Λ_K(s) = |d_K|^{s/2} ·
Gammaℝ(s)^{r₁} · Gammaℂ(s)^{r₂} · ζ_K(s)", the PQ4 freeze). The port needs no convention
reconciliation, which was the single largest risk the port audit flagged.

### The coverage map — and it is worse for wave 3 than "roughly half"

I authored 16 wave-3 envelopes this morning. Mapping each against the AINTLIB source:

> **SUPERSEDED IN PART — read §A33 (ADDENDUM 8) for the authoritative per-unit table.**
> Corrected in place 2026-08-17T22:58Z (fermat). This table was built partly from
> declarations and partly from filenames, and **every row I filled in from a filename was
> wrong or overstated.** The rows below carry their corrections inline; the verdicts, the
> declaration citations and the remaining costs are in §A33. The audit trail is §A19
> (three citation defects), §A23–A24 (W3-05 and the withdrawn §A11/§A20 residuals),
> §A26–A28 (W3-07/W3-08, and the retracted W3-09/W3-11 negative), §A30–A34 (the retraction
> and the corrected table). **Method note for whoever writes the next map: one row per
> unit, cite the declaration, or write "not checked" — the single line covering
> `W3-09 / W3-10 / W3-11` below is the shape of three of the four errors.**

| wave-3 unit | node | AINTLIB file | covered? |
|---|---|---|---|
| W3-01 | A3 Poisson on `ℤ^d` | `PoissonSummation.lean` (`zpoint`, `intEquivSpanBasisFun`, `fundamentalDomain_basisFun_eq`, `mFourier`) | **yes** |
| W3-02 | A1 dual lattice | `DualLattice.lean` (`dualZLattice`, `mem_dualZLattice`, `dualZLattice_eq_span`, `covolume_dualZLattice_mul`) | **yes — and A2 as well** |
| W3-03 | F2a Deligne Gamma integrals | `Normalisation.lean` `gammaFactor` + `Existence.lean` `prod_place_gamma`, `Gammaℝ_ofReal`, `Gammaℂ_ofReal` | **yes** |
| W3-04 | N2 Gamma modulus identities | `GammaStrip.lean` `norm_Gamma_half_add_mul_I_sq`, `norm_Gamma_one_add_mul_I_sq` | **yes — and N3's two-sided strip bounds too** (`norm_Gamma_le_mul_exp`, `le_norm_Gamma_base`) |
| W3-05 | N5 Borel–Carathéodory off-center | ~~`AnalyticControl.lean`~~ **Mathlib** | ~~**yes**~~ → **NO — §A23.** There is no Borel–Carathéodory statement in AINTLIB. BC is in Mathlib; the consumer purpose is met by `AnalyticControl.lean:2490` `norm_logDeriv_le_of_norm_le`. |
| W3-06 | N6 holomorphic logarithm | `AnalyticControl.lean:1927` `exists_differentiableOn_log` | **yes, more general domain (§A22)** — but only `exp ∘ L = f` is stated; `Re L = log‖f‖` and `deriv L = logDeriv f` are XS corollaries. |
| W3-07 | A5 anisotropic Gaussian | `ThetaLattice.lean:303/:348`, `HeckeTheta.lean:54/:60/:192`, `MellinAgreement.lean:246` | ~~**yes (high confidence)**~~ → **yes, and stronger than this row claimed (§A26, §A32):** `fourier_weightedGaussianCM` carries *exactly* the demanded constant, and the `2^{r₂}` bookkeeping the packet flags as unverified is proved (`dualPlaceWeights`). Owed: `SchwartzMap` only. |
| W3-08 | B1 trace pairing | `IdealLattice.lean:162` `inner_diagScale_embeddingCoords` (**not** `covolume_idealZLattice`, §A27) | **yes — and the packet's "no conjugation" trap is discharged**: `dualityWeights` is `(2, −2)` at `(re, im)`. |
| **W3-09** (F3a orbit ↔ ideal) | F3a | `MellinAgreement.lean:140` `coneUnfoldEquiv`, `:812` `abs_norm_conePreimage`, `:822` `tsum_idealSet_norm_rpow` (**not** `ClassTheta.lean`) | **yes, different shape (§A30)** — equivalence + summed identity over principal ideals dividing `J`; class indexing is factored into `ClassTheta`. Restate the node over the port's shape. |
| **W3-10** (F1 partial zeta) | F1 | `MellinAgreement.lean` `:980`/`:1507`/`:1637`/`:1860`/`:1940`, `ClassTheta.lean:245` `heckeF` | **PARTIAL — checked in §A36 (ADDENDUM 9), and this row's earlier "unchecked" plus W3-10's place on the *dispatch* list are both wrong.** The class-restricted ideal sum exists (14 uses, unnamed, as a `tsum` over `{b // ClassGroup.mk0 b = C}`), summability at real `s>1` is proved, and `∑_A ↔ dedekindZeta` is proved via the theta side. Missing: a named def, per-class summability, the complex-`s` upgrade, the crude bound. **Move to HOLD.** |
| **W3-11** (D1 polar decomposition) | D1 | `MellinAgreement.lean:1058` `heckeLogCLE`, `:1081` `map_heckeLogCLE_volume`, `:1087` `heckeJacobian_pos` (**not** `Existence.lean`) | **yes, on the log side (§A31)** — done exactly as W3-11's own sketch prescribes. Owed: `exp`-transport if multiplicative Haar is wanted, and the Jacobian is **existential** (positivity only, not `= 1`). |
| W3-12 | N19 test-function decay | — | **no** — Poitou explicit-formula class, past `CompletedZeta`'s scope |
| W3-13 | N1 M2→M3 interface | — | **hold**: the interface should be written against the *ported* names, not re-derived |
| W3-14 / W3-15 | CBC-S8, CBC-S2 | — | **no** — unrelated to zeta, safe to dispatch |
| W3-00 | build closure | — | **unaffected, still first** |

**Eleven of the sixteen wave-3 units would re-prove work that already exists sorry-free
under an Apache-2.0 licence.** That is my own recommendation from an hour ago and it is
wrong in its priority: the correct first move is not to prove A1 and A3, it is to find out
whether this tree builds at FLT's mathlib rev. `wave-3-packets.md` §5 has been corrected.

**The one thing still unverified, and it is the whole risk:** AINTLIB has **no Lean build
CI**. Sorry-free by grep is not the same as compiles. That is exactly what AINTLIB-0 gates,
which is why it is now the highest-priority packet in the campaign rather than a
recommended precaution.

## A3. AINTLIB-0′ — the bump-first variant that runs on today's image

**Supersedes AINTLIB-0 in §3 as the packet to dispatch.** AINTLIB-0 verifies AINTLIB at
*its own* pin, which needs toolchain `v4.33.0-rc1` and therefore multi-toolchain elan —
blocked on infra. But that configuration is not the one we care about. What the port needs
to know is whether `CompletedZeta` builds at **FLT's** mathlib, and that question can be
asked with the toolchain the worker image already has.

- **Tier:** Pro. **Size:** M. **Budget:** 3 iterations.
- **Substrate:** the *existing* FLT worker image — `v4.34.0-rc1` only, no elan change.
  Network egress to `github.com` (confirmed). Mathlib `bc06ce9f` cache already warm from
  `flt-cache-manual-0816`.
- **Do:** clone AINTLIB at `1c1c74664e40`; set `lean-toolchain` to
  `leanprover/lean4:v4.34.0-rc1` and the sole mathlib `require` to `bc06ce9f87cd`;
  `lake update mathlib`; `lake exe cache get`; build **only**
  `DedekindResidue.CompletedZeta` and its dependencies — not the five default targets.
- **Acceptance:** report, green or red — (a) exit status, (b) the first 20 errors with file
  and line if red, (c) wall clock, (d) whether `cache get` hit or the mathlib build went
  cold, (e) the `sorry`/`admit` count in the built tree (expected: 0), (f)
  `#print axioms DedekindResidue.completedDedekindZeta_one_sub` — expected to be the
  standard three.
- **Why this works on today's image:** AINTLIB's `lake-manifest.json` shows mathlib is its
  **only** external `require` (`flt-regular` is vendored, `plausible` etc. are inherited
  through mathlib). So the bump is a one-line dependency change, and the target rev is the
  one FLT already builds against — the warm cache applies directly.
- **The known ancestor fact makes this safe to attempt:** `3edb3c0658f6...bc06ce9f87cd` is
  `ahead_by: 271, behind_by: 0`. A strict forward bump, no divergent history.
- **The cost of skipping AINTLIB-0:** a red result is ambiguous — broken-before versus
  broken-by-the-bump. Mitigation: the error list in (b) distinguishes them in practice
  (mathlib API drift reads very differently from a genuine gap), and if it does not, run
  the original AINTLIB-0 once elan lands to disambiguate. **That ambiguity is worth
  accepting**: it costs one packet, whereas waiting for the elan infra costs the pool a day
  of proving nodes that a port may make redundant.
- **Remaining infra ask, much smaller than multi-toolchain elan:** either a second cache key
  `caches/aintlib`, or point AINTLIB's `.lake/packages/mathlib` at the warm `bc06ce9f`
  build. Neither is required for correctness — without them AINTLIB-0′ pays one cold
  mathlib build.

**If AINTLIB-0′ is green**, AINTLIB-1 in §3 is already done by construction (the bump *is*
the packet), and the campaign goes straight to AINTLIB-2, the vendoring port. Roughly 22 of
the 24 M2 nodes and a meaningful part of the M3 GA/BC parts land in one merge.

**If it is red**, the error list tells us whether to repair or to fall back, and the eleven
held wave-3 units are released for fresh proof with nothing lost but the hold.

## A4. Port-time concerns to record now (they do not block AINTLIB-0′)

- **`public import Mathlib`.** Every one of the 16 files imports Mathlib wholesale. FLT uses
  fine-grained imports and a `shake`-linted import graph, so AINTLIB-2 must narrow these or
  the FLT build time degrades sharply. Mechanical but not free — budget for it.
- **Namespace.** Everything is under `DedekindResidue`. Decide at port time whether to keep
  that namespace or rehome under `FLT.NumberField.Zeta`; keeping it makes future re-syncs
  with upstream AINTLIB far cheaper, and re-sync is likely since this is an active project.
- **Licence.** Apache-2.0, "Copyright (c) 2026 Chris Birkbeck". Same licence as FLT.
  Attribution headers must be preserved verbatim in every ported file.
- **Coordinate with the author.** C. Birkbeck is already named in the standing coordination
  requirement. A port of this size should be agreed, not merely licence-compliant.

---

# ADDENDUM 2, 2026-08-16T13:0xZ — I under-read it. The whole project is live-sorry-free, and it includes an unconditional Weil explicit formula

Addendum 1 looked at `CompletedZeta/` only, because that is the directory the port audit
named. That was too narrow. `Normalisation.lean:27` cross-references
`ExplicitFormula/WeilAssembly`, which sent me to the rest of the project.

## A5. The full `DedekindResidue` project

| directory | files | bytes | live `sorry`/`admit` | `axiom` decls |
|---|---|---|---|---|
| `CompletedZeta/` | 16 | 562 K | **0** | 0 |
| `ExplicitFormula/` | 10 | 713 K | **0** | 0 |
| root (`Theorem1`, `Lemma2`–`Lemma5`, `MainTheorem`, `QSide`, …) | 9 | 321 K | **0** | 0 |
| **total** | **35** | **~1.6 MB** | **0** | **0** |

A naive grep reports 2 hits in the root, in `Basic.lean:23` and
`AuxiliaryFunction.lean:13`. Both are **prose inside docstrings** — the project describing
*itself* as sorry-free:

```
Basic.lean:23  as an explicit hypothesis (never an `axiom`); every result is `sorry`-free
AuxiliaryFunction.lean:13  Real, `sorry`-free definitions of the auxiliary functions from Belabas–Friedman,
```

Which is a neat confirmation of `oracle-recount.md` §1: the same prose-versus-proof
distinction that makes FLT's gate constant 67-not-56 would have made this project look
2-holes-short-of-clean if I had trusted `grep`. `scripts/sorry_count.py` reads it correctly.

## A6. `ExplicitFormula/` is M4–M7, and the machinery is **not** GRH-conditional

This is the part that changes the size of the prize. The ten files are

```
WeilAssembly 168K   GammaSide 231K   ZeroCapture 69K   PrimeSide 58K   GRHZeros 30K
FourierJordan 76K   RectangleContour 28K   AuxAdmissible 28K   PhiTransform 16K   TestFunction 8K
```

with `WeilAssembly.lean:3128` `weil_explicit_formula_auxF` as the assembly point. Counting
`GeneralizedRiemannHypothesis` mentions per file:

```
WeilAssembly 0    PrimeSide 0    GammaSide 0    ZeroCapture 0    TestFunction 0
GRHZeros 4        Theorem1 3     MainTheorem 5
```

**GRH is quarantined.** The explicit-formula machinery — prime side, gamma side, zero
capture, rectangle contour, test-function class, assembly — is unconditional. GRH enters
only in `GRHZeros.lean` and the root application, and even there it is threaded as an
explicit hypothesis, never an `axiom` (`Basic.lean:22`). That is exactly the discipline this
campaign wants, and it means the machinery ports for an **unconditional** Odlyzko route.

`TestFunction.lean` is my node **N19** (`IsAdmissibleTestFn`, plus
`boundedVariationOn_of_deriv_integrable` and friends) — the Poitou admissible class,
compactly supported with `F′` of bounded variation. I marked W3-12 "not covered" in
addendum 1 on the strength of a grep confined to `CompletedZeta/`. **That was wrong; W3-12
is covered.**

## A7. What AINTLIB does *not* give us — and this is the part to be clear about

**Its root theorem is Belabas–Friedman under GRH, not Odlyzko.** `MainTheorem.lean` states
that under GRH, `log κ_K` (the residue of `ζ_K` at `s = 1`, i.e. Mathlib's
`dedekindZeta_residue`) is approximated by a computable `f_K(X)` with explicit error
`O(log Δ_K / (√X log X))` — Belabas–Friedman, arXiv:1305.0035. That is a different
destination from `FLT/Assumptions/Odlyzko.lean:57`, which is **unconditional**:
`|discr K| ≥ 8.25 ^ finrank ℚ K` for totally complex `K` of degree `≥ 18`.

So the correct statement of what a port buys is:

- **Covered, sorry-free, unconditional:** M2 (completed `Λ_K`, the functional equation),
  much of M3 (Gamma strip bounds, Borel–Carathéodory, holomorphic log, Jensen/divisor zero
  counting), and M4–M7 (the Weil explicit formula and its admissible test-function class).
- **Not covered:** node F1 (partial zeta functions as Dirichlet series — verified absent
  from all 35 files; AINTLIB does its class decomposition entirely on the theta side, via
  `heckeGClass`/`heckeF`, and never forms `ζ(A,s)`), and **the Odlyzko application itself**
  — the arithmetic that turns an explicit formula into a discriminant lower bound with the
  constant `8.25` and the degree-18 threshold. AINTLIB walks to Belabas–Friedman instead.

**The remaining FLT-specific work is therefore the Odlyzko endgame on top of a ported,
unconditional explicit formula.** That is a much smaller and better-shaped job than the
45-leaf wave — but it is a real job, and it is the one thing nobody else has done for us.
Nothing here says the axiom falls out of a port.

## A8. Consequences for dispatch

- **Hold: W3-01…W3-09, W3-11, W3-12, W3-13** — twelve, up from eleven. W3-12 (N19) joins
  the hold; it is `ExplicitFormula/TestFunction.lean`.
- **Dispatch: W3-00, W3-14, W3-15.** ~~W3-10~~ **— CORRECTED by ADDENDUM 9 §A36. W3-10 is
  back on the HOLD list (thirteen).** The release said "I checked all 35 files and there is
  no partial-zeta object anywhere, so it is genuinely fresh work." The 35 was the right
  denominator; the *query* was wrong — I grepped the name `partialZeta` (zero hits, truly)
  when the object is spelled `{b // ClassGroup.mk0 b = C}` inside a `tsum` and is used
  fourteen times in `MellinAgreement.lean`. Dispatching it would send a worker to re-derive
  `summable_ideal_norm_rpow` and `dedekindZeta_real_eq` from scratch.
- **AINTLIB-0′ (§A3) is unchanged and still the priority**, but its payoff is now larger
  than §A3 claims: it gates a port of ~1.6 MB of unconditional, sorry-free number theory
  covering M2, most of M3, and M4–M7 — not just the M2 tree.
- **Scope note for AINTLIB-0′:** build `DedekindResidue.CompletedZeta` **and**
  `DedekindResidue.ExplicitFormula`, not `CompletedZeta` alone. The root
  (`Theorem1`/`MainTheorem`) can be excluded — it is the Belabas–Friedman application we do
  not need — which also keeps the build smaller.

## A9. Confidence, stated honestly

I have now read declaration signatures across all 35 files and read two files closely
(`FunctionalEquation.lean`, `MainTheorem.lean` in part). The sorry/axiom counts are
mechanical and I trust them. The **coverage map is signature-level**: I have matched node
statements to declaration names and types, not verified that each ported statement is
strong enough for the consumer FLT node. Two specific things a reviewer should re-derive
rather than take from me:

1. whether `IsAdmissibleTestFn` is exactly the class N20/M7 need, or a variant;
2. whether the `GammaStrip` two-sided bounds cover N3's `[a,b]`-strip generality or only
   the `[1/2, 3/2]` window their signatures show (`Gamma_le_max_of_mem_Icc`,
   `norm_Gamma_le_mul_exp` are stated on `Icc (1/2) (3/2)` and `Icc (-(1/2)) (1/2)`).

And the standing caveat has not moved: **no Lean CI on that repo, no toolchain here.**
Every count above is textual. AINTLIB-0′ is still the only thing that turns any of this
into fact.

---

# ADDENDUM 3, 2026-08-16T13:30Z — the two §A9 gaps, closed. Neither is a hole; both leave a small bridge.

§A9 flagged two coverage claims as signature-level and asked a reviewer to re-derive them.
The pool is idle, so I did it myself. Both resolve, and both change the answer in a way that
matters for what gets dispatched *after* the port.

## A10. Gap (a) — `IsAdmissibleTestFn` is **not** my N19 class. It is broader, and that is good news.

`ExplicitFormula/TestFunction.lean:51` bundles Belabas–Friedman p. 3 verbatim:

```lean
structure IsAdmissibleTestFn (F : ℝ → ℂ) : Prop where
  even : ∀ x : ℝ, F (-x) = F x
  bv_integrable_exp : ∃ ε : ℝ, 0 < ε
    ∧ BoundedVariationOn (fun x => F x * (Real.exp ((1/2 + ε) * x) : ℂ)) (Set.Ici 0)
    ∧ IntegrableOn  (fun x => F x * (Real.exp ((1/2 + ε) * x) : ℂ)) (Set.Ici 0)
  diffQuot_bv : BoundedVariationOn (fun x => (F 0 - F x) / x) (Set.Ici 0)
  jump_avg : ∀ x, ∃ L R, Tendsto F (𝓝[<] x) (𝓝 L) ∧ Tendsto F (𝓝[>] x) (𝓝 R)
                          ∧ F x = (L + R) / 2
```

My `𝓕` (`odlyzko-m3-decomposition.md` N19) is: `F` even, **compactly supported**, Lipschitz,
`F′` of bounded variation. These are different classes, and the direction of the difference
is the point:

- **`𝓕 ⊆ IsAdmissibleTestFn`.** Compact support plus Lipschitz gives BV and integrability of
  the exponentially-weighted function for *every* `ε`; Lipschitz bounds `(F 0 − F x)/x` near
  `0` and compact support plus `F′` BV gives the rest of `diffQuot_bv`; Lipschitz implies
  continuity, so `jump_avg` holds trivially with `L = R = F x`.
- So the ported explicit formula applies to everything N19 was built to feed it, and to
  more.

**This retires the N19 risk note outright.** That note warned: *"if a downstream node ever
needs a discontinuous `F`, N20 becomes conditionally convergent and must be redone with
symmetric limits — escalate at M7 assembly rather than quietly widening `𝓕`."* I called it
the single most expensive silent mistake available in the M3 tree. AINTLIB's class carries
`jump_avg` — **it already admits jump discontinuities**, with the average-value convention,
and it already carries the exponential-weight machinery that makes the sum converge. The
hazard is pre-solved by the port rather than merely avoided.

**Residual node (post-port, S):** the inclusion `𝓕 F → IsAdmissibleTestFn F` still has to be
*proved* if any FLT-side node is stated over `𝓕`. Cheaper option: restate those nodes over
`IsAdmissibleTestFn` directly and skip the bridge. Decide at port time; do not prove `𝓕`
from scratch either way.

## A11. Gap (b) — `GammaStrip` is strip-specific, not general `[a,b]`, and its bound is *stronger* in shape

The three headline bounds carry explicit windows:

```lean
norm_Gamma_le_mul_exp       {σ t} (h1 : 1/2 ≤ σ) (h2 : σ ≤ 3/2)     (ht : 1 ≤ |t|)
norm_Gamma_le_mul_exp_left  {σ t} (h1 : -(1/2) ≤ σ) (h2 : σ ≤ 1/2)  (ht : 1 ≤ |t|)
le_norm_Gamma_base          {σ t} (h1 : 1/2 ≤ σ) (h2 : σ ≤ 3/2)     (ht : 1 ≤ |t|)
```

plus `le_norm_Gamma_base_add_nat` (`:594`), which walks the lower bound up by natural
recurrence steps. So the covered region is `[-1/2, 3/2]` with an upward extension, **not**
the arbitrary `a ≤ σ ≤ b` N3 asks for.

Two offsetting observations:

- **The bound shape is better than N3 needs.** AINTLIB proves
  `‖Γ(σ+it)‖ ≤ √(12π) · ‖σ+it‖ · e^{−π|t|/2}` — linear in `‖z‖`. N3 only asked for a crude
  polynomial `(1+|t|)^A`. Linear is the `A = 1` case, so nothing downstream loses.
- **Extending the window is mechanical**, by the same `Γ(s+1) = sΓ(s)` recurrence
  `norm_Gamma_le_mul_exp_left` already uses once and `le_norm_Gamma_base_add_nat` already
  iterates upward. Downward is symmetric.

**Residual node (post-port, S):** a general `[a,b]` wrapper over the four AINTLIB lemmas.
This is N3 reduced from an M to an S, not N3 eliminated.

## A12. Revised bottom line

The coverage map in §A2/§A8 stands, with two named residuals rather than a clean sweep:

| | before this addendum | after |
|---|---|---|
| N19 / W3-12 | "covered" | **covered, broader class**; + S-sized inclusion lemma *or* restate over `IsAdmissibleTestFn`. Risk note retired. |
| N3 (feeds W3-04's column) | "covered" | **covered on `[-1/2,3/2]`**; + S-sized general-strip wrapper. N3 drops M → S. |

Neither residual is dispatchable now — both are bridges onto ported code that does not
exist in FLT yet. Both should be cut as packets **the moment AINTLIB-2 lands**, not before.
Recording them now so they are not rediscovered as surprises at assembly.

And the standing caveat is unchanged and still the only thing that matters: **no build CI
there, no toolchain here.** Everything above is signature reading. AINTLIB-0′ remains the
one experiment that converts any of it into fact.

---

# ADDENDUM 4, 2026-08-17T06:5xZ — AINTLIB-0′ came back GREEN. Statement review, and the AINTLIB-2 decision.

Supervisor result, quoted exactly: rev `1c1c74664e40`, repo-native mathlib pin, **26**
`CompletedZeta`+`ExplicitFormula` modules, **8722** build jobs, **804s**;
`#print axioms DedekindResidue.completedDedekindZeta_one_sub` =
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

## A13. What the green actually discharges — and what it does not

**It discharges the §A12 standing caveat, on the build dimension only.** A12 said "no
build CI there, no toolchain here — everything above is signature reading, and AINTLIB-0′
is the one experiment that converts any of it into fact." That experiment has now run.
The tree compiles against FLT's own mathlib pin, at the scope §A8 specified
(`CompletedZeta` **and** `ExplicitFormula`, root `Theorem1`/`MainTheorem` excluded). The
§A8 scope note was honored — 26 modules is the right number for that pair, not for
`CompletedZeta` alone. The 271-commit forward bump (§2) is now demonstrated, not
projected.

**The supervisor's caution about the axiom audit is correct, and the precise form of it is
worth stating**, because "one declaration" undersells it in one direction and oversells it
in another:

- `#print axioms` is **transitive**. It reports the axioms of the entire proof tree
  beneath the named declaration. So this is not a spot check of one line — it certifies
  that `completedDedekindZeta_one_sub` **and every lemma it depends on** are free of
  `sorryAx`. That is a genuinely strong result about the M2 spine.
- But it certifies a **cone, not a project**. Any declaration not in that dependency tree
  is unaudited by this command. Critically, `completedDedekindZeta_one_sub` is the
  functional equation — it lives in `CompletedZeta`. **The whole `ExplicitFormula/` half
  is almost certainly outside its cone**, and `ExplicitFormula/` is M4–M7, the larger
  prize (§A6). The 8722-job build proves those modules *compile*; it does not prove they
  are `sorryAx`-free, because a `sorry` compiles fine.

**Ask for, before AINTLIB-2:** `#print axioms` on the consumer-facing declarations of the
`ExplicitFormula` half — the explicit-formula theorem itself and the `IsAdmissibleTestFn`
results behind §A10/§A11 — not just the M2 functional equation. That is one more cheap
command on an already-warm build, and it converts §A2's mechanical sorry/axiom count (a
textual scan I did without a toolchain) into checked fact for the half that matters most.

## A14. The statement review, which is the actual gate — and a build cannot do it

§A9 recorded the real risk and the green does not touch it: **the coverage map is
signature-level.** I matched node statements to declaration names and types; I did not
verify that each ported statement is *strong enough for its consumer FLT node*. A green
build says the proofs are correct. It says nothing about whether they prove what we need.

The two named residuals from §A12 stand exactly as recorded, and both are now *actionable*
rather than parked, because the code they bridge onto is about to exist:

| node | status | bridge required |
|---|---|---|
| N19 / W3-12 | covered, **broader** class (`IsAdmissibleTestFn` ⊋ my N19 class, §A10) | S-sized inclusion lemma, *or* restate the FLT node over `IsAdmissibleTestFn` |
| N3 (feeds W3-04) | covered on `[-1/2, 3/2]` only (§A11); the bound's *shape* is stronger | S-sized general-strip wrapper; N3 drops M → S |

Both should be cut as packets **the moment AINTLIB-2 lands**, not before — they are
bridges onto ported code, and cutting them early produces exactly the failure mode
described in §A16.

**And the honest boundary, restated because it is the thing most likely to be
over-claimed:** AINTLIB's root theorem is Belabas–Friedman **under GRH** (§A7). Our target
`FLT/Assumptions/Odlyzko.lean:57` is **unconditional**. The port buys M2, most of M3, and
M4–M7 as unconditional sorry-free machinery. It does **not** buy the Odlyzko application —
the arithmetic taking an explicit formula to `|discr K| ≥ 8.25 ^ finrank ℚ K` at degree
≥ 18. Nobody should read "AINTLIB-0′ green" as "the Odlyzko axiom is close to falling."
The remaining FLT-specific work is the Odlyzko endgame on top of a ported explicit
formula: smaller and far better shaped than the 45-leaf wave, but real, and still ours.

## A15. Decision — AINTLIB-2 should VENDOR, not hand-port

Recommendation: **vendor the bumped `CompletedZeta` + `ExplicitFormula` subtree under a
namespace prefix, with Apache-2.0 attribution. Do not restate it by hand.**

Licensing is clean and settled: AINTLIB is Apache-2.0 and the `LICENSE` was added *at the
exact commit we pin* (`1c1c74664e40`, "Add Apache-2.0 LICENSE", 2026-07-31). Attribution
headers per file, as §3/AINTLIB-2 already specifies.

The decisive argument is empirical and we earned it this morning, in this repo:

> **Hand-restatement is the failure mode that just bit us.** `ZeroTheoryN2.lean` — 140
> lines of hand-written Lean delivered against a node description — merged green on
> 2026-08-16 having never been compiled by anything, and on first real compilation
> produced 124 ambiguity / 126 unsolved-goal / 137 type-mismatch errors. See
> `cartography/oig35-21-refinement.md`.

Hand-porting ~1.6 MB of number theory is that same bet, taken ~100× over, against proofs
that **have already been machine-checked upstream**. Vendoring preserves checked artifacts;
porting re-opens every one of them. Choose vendoring.

Two conditions on it, both non-negotiable:

1. **The build-closure gate applies to the vendored subtree.** Vendored modules that
   nothing imports are exactly as vacuous as `ZeroTheoryN2` was — a 26-module vendor drop
   could add zero real compilation and still show green. Gate on
   `scripts/sorry_count.py --closure` (exits 1 on orphans, no toolchain needed) in the
   same commit that lands the vendor, and wire the vendored root into `FLT.lean`.
2. **Re-audit axioms after the bump, in FLT's tree, not AINTLIB's.** The 271-commit
   forward bump is linear with no divergent history (§2), but "compiles after bump" and
   "proves the same statements after bump" are different claims, and mathlib deprecations
   can silently weaken a statement through a changed definition. `#print axioms` on the
   consumer-facing declarations post-vendor, per §A13.

Build cost to plan for: 8722 jobs / 804s at the pinned mathlib. That is a real per-CI
number and argues for vendoring the subtree **only** — root `Theorem1`/`MainTheorem`
excluded, as §A8 already says — rather than the whole project.

## A16. Sequencing

1. `#print axioms` on the `ExplicitFormula` consumer declarations (§A13). Cheap, warm
   build, and it is the last thing standing between §A2's textual scan and checked fact.
2. **Statement review of the M2/M3/M4–M7 declarations against their consumer FLT nodes**
   (§A14). This is mine, it is signature-level work needing no toolchain, and it is the
   genuine gate — not the build.
3. AINTLIB-2 vendor drop under §A15's two conditions.
4. Only then cut the N19 and N3 bridge packets (§A14) and release the §A8 held units
   W3-01…W3-09, W3-11, W3-12, W3-13.

Doing 4 before 2 is how a signature-level coverage map becomes a wave of packets gated
against statements nobody checked were strong enough. That is the same shape of error as
the vacuous green, one level up.

---

# ADDENDUM 5, 2026-08-17T22:00Z — §A16 item 2 executed: the statement review. And C2 has been re-proving AINTLIB by hand.

§A16 sequenced four steps and routed item 2 to me: *"statement review of the M2/M3/M4–M7
declarations against their consumer FLT nodes — signature-level work needing no toolchain,
and the genuine gate, not the build."* The pool is still dark (no `fleet/*` branch in 31h),
so I did it. It produced one finding that changes what should happen to C2, three citation
corrections to my own §A2 map, and one new residual of the §A11 kind.

## A17. Method, and a second independent sorry-free sitting

I re-fetched all 13 `CompletedZeta/` files at pin `1c1c74664e40` — `AnalyticControl`,
`ClassTheta`, `DualLattice`, `Existence`, `FEPair`, `FunctionalEquation`, `GammaStrip`,
`HeckeTheta`, `IdealLattice`, `Normalisation`, `PoissonLattice`, `PoissonSummation`,
`ThetaLattice` — and re-ran the scan rather than citing §A2:

```
sorry: 0    admit: 0    ^axiom : 0
```

**§A2's mechanical claim reproduces at a second sitting.** That is still a *grep*, and the
standing caveat is unchanged: no build CI there, no toolchain here. What follows is
signature reading, and I mark every place where I am inferring rather than reading.

## A18. THE FINDING — `ZeroTheoryN2.lean` re-proves `GammaStrip.lean` by hand, and it is the file that merged vacuously

Side by side, read from source this cycle.

**FLT, `FLT/NumberField/ZetaFE/ZeroTheoryN2.lean` (hub-oig35.19, merged as PR #9, never compiled):**

```lean
lemma Gamma_one_add_I_mul_sq_norm (t : ℝ) (ht : t ≠ 0) :
    ‖Gamma (1 + I * t)‖ ^ 2 = π * t / sinh (π * t)          -- :26

lemma Gamma_one_half_add_I_mul_sq_norm (t : ℝ) (ht : t ≠ 0) :
    ‖Gamma ((1 / 2 : ℂ) + I * t)‖ ^ 2 = π / cosh (π * t)    -- :117
```

**AINTLIB, `CompletedZeta/GammaStrip.lean` (Apache-2.0, sorry-free, machine-checked):**

```lean
theorem norm_Gamma_one_add_mul_I_sq {t : ℝ} (ht : t ≠ 0) :
    ‖Complex.Gamma (1 + t * Complex.I)‖^2 = π * t / Real.sinh (π * t)   -- :62

theorem norm_Gamma_half_add_mul_I_sq (t : ℝ) :
    ‖Complex.Gamma (1/2 + t * Complex.I)‖^2 = π / Real.cosh (π * t)     -- :34
```

**These are the same two theorems.** The only textual difference is `I * t` vs `t * I`, a
`mul_comm`. And on the second one the port is **strictly stronger**: AINTLIB proves it
with *no hypothesis at all*, while our hand-written version carries a spurious `ht : t ≠ 0`.
That hypothesis is not needed at `σ = 1/2` — `cosh` is bounded below by 1 and `Γ(1/2+it)`
never vanishes, so `t = 0` is fine and gives `‖Γ(1/2)‖² = π = π/cosh 0`. On the `1 + it`
lemma the hypothesis **is** genuine and both sides carry it, since the right-hand side is
`0/0` at `t = 0`; that independently corroborates the `hit : (I * t) ≠ 0` step required in
`oig35-21-refinement.md` §4.

What this means for C2, stated plainly:

1. **hub-oig35.19 spent 140 hand-written lines re-proving a machine-checked upstream
   result.** Nobody could have known at dispatch time — the AINTLIB coverage map did not
   exist until 2026-08-16 — so this is not a rebuke of that packet. It is an argument about
   what to do next.
2. **hub-oig35.21 is currently burning cycles repairing those 140 lines** (124 ambiguous
   terms, 126 unsolved goals, 137 type mismatches — the file's original defects surfacing
   on first compilation, per `oig35-21-refinement.md`). Every one of those repairs
   reconstructs, by hand and unverified, something the port delivers already proved.
3. **Therefore the C2 disposition should be re-opened.** The per-line repair guidance in
   `oig35-21-refinement.md` stays valid and I am not withdrawing it — but if AINTLIB-2
   lands, the cheaper and safer end state is **delete `ZeroTheoryN2.lean` and re-export the
   two ported names**, not repair it. A hand proof that has never compiled is a liability;
   a vendored proof that has is not.
4. **This does not unblock C2 today.** AINTLIB-2 has not landed and AINTLIB-0′ has not run.
   The decision point is *at* the vendor drop, not before it. Until then .21's repair is
   still the only route, and the merge hazard in `oig35-21-refinement.md` §1 still governs.

The general lesson is the one this campaign keeps re-learning at a different altitude:
**check the substrate before proving.** The vacuous green was "we did not check whether it
compiled." This is "we did not check whether it was already proved."

## A19. Strength verdicts for the held units — and three corrections to my own §A2 map

Read from source at the pin this cycle. "Strong enough?" means: does the ported statement
imply what the consumer FLT node needs, not merely share its name.

| unit | AINTLIB declaration (verified location) | strong enough? |
|---|---|---|
| W3-02 (A1 dual lattice) | `DualLattice.lean:109` `covolume_dualZLattice_mul : covolume (dualZLattice L) * covolume L = 1` | **yes, exactly.** Stated for any `L` with `[DiscreteTopology L] [IsZLattice ℝ L]` in `EuclideanSpace ℝ ι` — the generality A1 asks for. `mem_dualZLattice:63` gives the membership characterisation, `dualZLattice_eq_span:70` the basis form. |
| W3-01 (A3 Poisson on `ℤ^d`) | `PoissonSummation.lean` — `zpoint:50`, `intEquivSpanBasisFun:77`, `fundamentalDomain_basisFun_eq:173`, `periodization:352`, `fourierIntegral_zpoint_eq:332` | **yes (high confidence).** `fundamentalDomain_basisFun_eq` pins the fundamental domain to `∏ Ico 0 1`, which is what A3's unfolding needs. |
| W3-03 (F2a Deligne Gamma) | `Normalisation.lean:41` `gammaFactor K (s : ℂ) = Γℝ s ^ r₁ * Γℂ s ^ r₂` + `gammaFactor_ne_zero_of_re_pos:46` | **yes** — and note the object is **complex-variable**, which is what F2a needs. |
| W3-04 (N2 Gamma modulus) | `GammaStrip.lean:34, :62` | **yes, and stronger** — see §A18. The `1/2` case is hypothesis-free. |
| W3-08 (B1 trace pairing) | `IdealLattice.lean:79` `covolume_idealZLattice I = absNorm I * (2⁻¹)^r₂ * √abs (discr K)` | **yes, and more general than needed** — stated over `(FractionalIdeal (𝓞 K)⁰ K)ˣ`, not just integral ideals. `embeddingCoords:117`, `dualityWeights:148` supply the pairing. |
| W3-05 / W3-06 (N5, N6) | `AnalyticControl.lean` | **not re-derived this cycle** — 181 KB, the one file I have still only read by signature index. Flagged, not claimed. |
| W3-07 / W3-09 / W3-11 | `ThetaLattice`, `HeckeTheta`, `ClassTheta`, `Existence` | **unchanged from §A2's "high confidence"** — not re-derived at statement level this cycle. |
| W3-12 (N19) | `ExplicitFormula/TestFunction.lean:51` | settled in §A10: covered, broader class. |
| W3-13 (N1 interface) | — | still hold; write against ported names. |

**Corrections to §A2's coverage table, found by trying to open the declarations it cites:**

1. `completedZetaPrefactor` is **not** in `Normalisation.lean`. It is
   `FunctionalEquation.lean:44`. §A2 attributed it to `Normalisation.lean` alongside
   `gammaFactor` (which *is* at `Normalisation.lean:41`).
2. `IsCompletedDedekindZeta` is **not** in `Existence.lean`. It is
   `FunctionalEquation.lean:63`, with `IsCompletedDedekindZeta.eqOn` at `:73`.
   `Existence.lean` holds the *inhabitation* results — `completedDedekindZeta:160`,
   `exists_isCompletedDedekindZeta:369`, `completedDedekindZeta_one_sub:412`.
3. **`mFourier` is not an AINTLIB declaration at all.** §A2 listed it as covering W3-01.
   It is Mathlib's, reached through `UnitAddTorus.hasSum_mFourier_series_apply_of_summable`;
   AINTLIB's own wrapper is `mFourier_neg_coe:62`. W3-01 coverage is unaffected — the
   covering declarations are the four listed in the table above — but the citation was
   wrong and would have sent a reader looking for a name that does not exist.

None of the three changes a coverage verdict. All three would have cost a reader time, and
the third is exactly the kind of name-level slip that a signature-level map is prone to,
which is the point of doing item 2 at all.

## A20. New residual, same shape as §A11 — `norm_gammaFactor_le` is window-restricted

```lean
-- AnalyticControl.lean:410
theorem norm_gammaFactor_le {σ t : ℝ} (h1 : 1 ≤ σ) (h2 : σ ≤ 2) (ht : 2 ≤ |t|) :
    ‖gammaFactor K ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ …
```

Covered region is `[1,2] × {|t| ≥ 2}`, not a general strip — the same restriction §A11
recorded for `norm_Gamma_le_mul_exp` on `[1/2,3/2]`, one level up in the tower. Any
consumer node needing the gamma-factor bound outside that window inherits the same
mechanical `Γ(s+1) = sΓ(s)` extension. **Add it to the §A11 general-strip wrapper packet
rather than cutting a second one** — one wrapper node should discharge both, which keeps
N3's M→S drop and does not add a node.

## A21. What item 2 did and did not settle

**Settled:** W3-01, W3-02, W3-03, W3-04, W3-08 are covered by statements that are strong
enough, read from source, two of them strictly stronger than the FLT-side node asked for.
The §A2 citations are corrected. The C2 duplication is on the record.

**Not settled:** W3-05, W3-06 (`AnalyticControl.lean`, 181 KB — signature index only) and
W3-07, W3-09, W3-11 remain at §A2's "high confidence", which is *not* the same standard as
the rows above. **§A16 item 2 is therefore ~60% done, not done.** Whoever picks it up
should finish `AnalyticControl.lean` first: it is the largest file, it carries N5/N6 and
the gamma-factor bound, and it is the one place where a strength gap would be expensive.

The sequencing is unchanged: item 1 (`#print axioms` on the `ExplicitFormula` consumers)
still needs a warm build and is still not mine. Item 3 waits on both. **Item 4 still must
not run first.**

---

# ADDENDUM 6, 2026-08-17T22:29Z — `AnalyticControl.lean` read at last. It retires two residuals I invented, and it breaks one coverage claim.

§A21 named `AnalyticControl.lean` (181 KB, 45 declarations) as the unfinished and expensive
part of item 2, and said whoever continued should take it first. The pool is still dark, so
I did. It changes four verdicts, two of them corrections to my *own* work — one written
half an hour ago.

## A22. `exists_differentiableOn_log` covers W3-06, but delivers one of the three conclusions

```lean
-- AnalyticControl.lean:1927
theorem exists_differentiableOn_log {U : Set ℂ} (hUo : IsOpen U) (hUc : Convex ℝ U)
    (hne : U.Nonempty) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (h0 : ∀ z ∈ U, f z ≠ 0) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L U ∧ Set.EqOn (Complex.exp ∘ L) f U
```

W3-06 asks for an analytic `L` on `ball c R` with **(i)** `exp ∘ L = f`, **(ii)**
`Re L = log ‖f‖`, **(iii)** `deriv L = logDeriv f`.

- **Domain: stronger than asked.** Any open convex nonempty `U`; a ball is open and convex,
  so `ball c R` is a special case.
- **Conclusion (i): delivered exactly.**
- **Conclusions (ii) and (iii): not stated.** Both are cheap corollaries of (i) —
  `‖f‖ = ‖exp L‖ = exp (Re L)` gives (ii) by `Real.log_exp`, and differentiating
  `exp ∘ L = f` gives (iii) — but *cheap corollary* is not *ported statement*, and a
  consumer node stated over (ii)/(iii) does not typecheck against this theorem.

**Verdict: covered, plus an XS corollary bridge.** Not the clean "yes" §A2 recorded. Fold
the two corollaries into whichever packet consumes the port; do not cut a node for them.

## A23. W3-05 is **not** covered — AINTLIB has no Borel–Carathéodory theorem

§A2 recorded `W3-05 | N5 Borel–Carathéodory off-center | AnalyticControl.lean | yes`. I
went looking for the statement. It is not there. The 45-declaration index contains nothing
Borel–Carathéodory-shaped, and a case-insensitive search for `borel`/`caratheodory` across
the file returns no declaration — only unrelated `Re ≤` strip hypotheses.

**AINTLIB reaches the same destination by a different route.** What N5 exists to feed is
N7, the zero-machinery kernel — ultimately a bound on `logDeriv`. AINTLIB states that
directly:

```lean
-- AnalyticControl.lean:2490
theorem norm_logDeriv_le_of_norm_le {h : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 3/4 < r)
    (hd : DifferentiableOn ℂ h (Metric.ball c r))
    (h0 : ∀ z ∈ Metric.ball c r, h z ≠ 0)
    {mS mL : ℝ} (hmL : 0 < mL) (hcL : mL ≤ ‖h c‖)
    (hS : ∀ z ∈ Metric.ball c r, ‖h z‖ ≤ mS) :
    ∀ s ∈ Metric.closedBall c (r - 3/4),
      ‖logDeriv h s‖ ≤ 32 * r * (Real.log (mS/mL) + 1)
```

That is the Borel–Carathéodory-plus-Jensen *consequence*, stated as a lemma, with the
intermediate BC step never surfaced. Note the hard-coded shrink `3/4` and constant `32` —
it is a specific instrument, not a general-radius API.

**So the correct verdict for W3-05 is three-part, and none of it is "AINTLIB covers it":**

1. **AINTLIB does not supply Borel–Carathéodory.** The §A2 row is wrong.
2. **It does not need to.** W3-05's own envelope already says the mathematics is in
   *Mathlib* — `Mathlib/Analysis/Complex/BorelCaratheodory.lean:109`, with
   `borelCaratheodory_zero` at `:86` — and that W3-05 is "API glue, not a theorem". So §A2
   credited AINTLIB with something Mathlib already had and AINTLIB does not.
3. **If N7 is restated over `norm_logDeriv_le_of_norm_le`, W3-05 is unnecessary entirely.**
   That is the cheaper end state, at the cost of inheriting the `3/4`/`32` constants.
   Decide at port time; it is a node-shape question, not a coverage question.

## A24. §A11 and §A20 are retired — the general bounds were one file over, and I missed them twice

This is the correction that matters most, because I made it twice and the second time was
today.

§A11 (yesterday) concluded from `GammaStrip.lean` that the Gamma bounds are windowed to
`[-1/2, 3/2]`, and cut a residual: *"general `[a,b]` wrapper; N3 drops M → S."* §A20 (this
morning, ADDENDUM 5) concluded from `norm_gammaFactor_le` that the gamma-factor bound is
windowed to `[1,2] × {|t| ≥ 2}`, and folded a second residual into the first. **Both
conclusions were drawn from the narrow file while the general statements sat in
`AnalyticControl.lean`, which I had only indexed by signature:**

```lean
-- :1187  upper bound, ALL σ ≥ 1/2 — a half-line, no upper cutoff
theorem exists_norm_Gamma_le (σ : ℝ) (hσ : 1/2 ≤ σ) :
    ∃ C, 0 < C ∧ ∃ P : ℕ, ∀ t, 1 ≤ |t| →
      ‖Γ(σ + tI)‖ ≤ C * (1 + |t|)^P * exp (-(π|t|)/2)

-- :1218  matching lower bound, ALL σ ≥ 1/2
theorem exists_le_norm_Gamma (σ : ℝ) (hσ : 1/2 ≤ σ) : …

-- :3112 / :3221  two-sided windows reaching negative σ: [-2,3] and [-1,2]
theorem exists_norm_Gamma_le_window : … -2 ≤ σ → σ ≤ 3 → …
theorem exists_le_norm_Gamma_window : … -1 ≤ σ → σ ≤ 2 → …

-- :1485  gamma factor to an ARBITRARY upper limit σ₁
theorem exists_norm_gammaFactor_le_range (σ₁ : ℝ) :
    ∃ C, 0 < C ∧ ∃ P : ℕ, ∀ σ t, 1 ≤ σ → σ ≤ σ₁ → 2 ≤ |t| → …
```

**N3 asked for a crude polynomial `(1+|t|)^A`.** That is *exactly* the `∃ C ∃ P` shape at
`:1187`, and it holds for every `σ ≥ 1/2` with no upper cutoff. **N3 is fully covered. The
general-strip wrapper packet should not be cut** — §A11's "N3 drops M → S" was too
pessimistic; N3 drops out. §A20's gamma-factor complaint is likewise answered by `:1485`
for any `σ₁`.

The one genuine distinction to carry forward, which replaces both residuals:

| need | use | why |
|---|---|---|
| **explicit constant** (`√(12π)·‖z‖`) | `GammaStrip.lean:346/484` | narrow window `[1/2,3/2]`, but the constant is written down |
| **wide σ range** | `AnalyticControl.lean:1187/1218/3112/3221/1485` | existential `∃ C ∃ P` — no explicit constant |

A consumer needing *both* an explicit constant and a wide window still has work. Nothing in
the current node set does.

**Why I got this wrong twice:** both §A11 and §A20 generalised from the file whose *name*
matched the topic. `GammaStrip.lean` is where Gamma strip bounds "should" live, so I read it
and stopped. The general versions live in the 181 KB file I kept deferring because it was
expensive to read. That is precisely the failure mode item 2 exists to catch, and it caught
my own work rather than the port's — which is the more useful outcome, since my residuals
were about to become dispatched packets.

## A25. Item 2 status — now ~80%, and the remaining 20% is named

**Verified from source:** W3-01, W3-02, W3-03, W3-04, W3-05 (negative), W3-06, W3-08, plus
N3/N19 settled and §A11/§A20 retired.

**Still at §A2's weaker "high confidence", not re-derived:** W3-07 (A5 anisotropic Gaussian
— `ThetaLattice`/`HeckeTheta`), W3-09 (F3a unit-orbit ↔ ideal — `ClassTheta`), W3-11 (D1
polar decomposition — `Existence`). Three units, three files, all fetched and on disk.
Whoever continues should do those three and then declare item 2 closed.

**Net effect on the hold list:** of the twelve held units, the port's coverage is now
confirmed strong enough for seven, one (W3-05) is confirmed *not* covered and probably
unnecessary, one (W3-06) needs an XS corollary, and three remain unverified. **No unit has
been found where the port is too weak for its consumer.** The two residuals I had recorded
against the port were both mine, not its.

---

# ADDENDUM 7, 2026-08-17T22:41Z — item 2 is CLOSED. The last three units read; two of them are not covered, and the reason matters more than the fact.

§A25 named the remaining 20% precisely — W3-07, W3-09, W3-11 — and said they were
finishable offline from `/tmp/aintlib/`. They were. This closes §A16 item 2.

## A26. W3-07 (A5, anisotropic Gaussian) — covered, exact constant, and the `2^{r₂}` risk is already discharged

The packet's own risk note says the `2^{r₂}` bookkeeping "is checked end-to-end much later
… until then it is unverified, so state it precisely." **AINTLIB has already stated it
precisely and proved it.**

```lean
-- ThetaLattice.lean:303
noncomputable def weightedGaussianCM (c : ι → ℝ) : C(EuclideanSpace ℝ ι, ℂ) :=
  ⟨fun x => Complex.exp (-(π : ℂ) * ∑ i, (c i : ℂ) * (x i : ℂ) ^ 2), by fun_prop⟩

-- ThetaLattice.lean:348
theorem fourier_weightedGaussianCM {c : ι → ℝ} (hc : ∀ i, 0 < c i) (w : EuclideanSpace ℝ ι) :
    𝓕 (⇑(weightedGaussianCM c)) w
      = (Real.sqrt (∏ i, c i))⁻¹ • weightedGaussianCM (fun i => (c i)⁻¹) w
```

**The constant is W3-07's constant.** Under the place→coordinate expansion
`placeWeights c = Sum.elim c (fun p => c p.1)` (`HeckeTheta.lean:54`), a complex place owns
two coordinates carrying the same weight, so `∏ᵢ placeWeights c i = ∏_v (c_v)^{n_v}` and
`(√∏ᵢ)⁻¹ = ∏_v (c_v)^{−n_v/2}`. Substituting `c_v = n_v y_v` gives exactly
`∏_v (n_v y_v)^{−n_v/2}` — the constant W3-07 demands be fixed in the statement.

**The exponent is W3-07's exponent**, via

```lean
-- HeckeTheta.lean:60
theorem sum_placeWeights_embeddingCoords_sq (c : InfinitePlace K → ℝ) (x : K) :
    (∑ i : index K, placeWeights K c i * embeddingCoords K x i ^ 2)
      = ∑ w : InfinitePlace K, c w * (w x) ^ 2
```

again with `c_w = n_w y_w`. Note the multiplicity is *not* written in this lemma — it comes
from the two coordinates of a complex place, which is the correct place for it to come from.

**And the archimedean duality factor is written down, not deferred:**

```lean
-- HeckeTheta.lean:192
noncomputable def dualPlaceWeights (c : InfinitePlace K → ℝ) : InfinitePlace K → ℝ :=
  fun w => if IsReal w then (c w)⁻¹ else 4 * (c w)⁻¹
```

The `4 = 2²` at complex places is the whole of the `2^{r₂}` bookkeeping, proved consistent
with the coordinate picture by `placeWeights_dualPlaceWeights` (:197) and consumed by
`heckeTheta_inversion` (:212). **This is the single most valuable thing the port carries for
C2/F3b**, and my §A2 row recorded it as an undifferentiated "yes".

**Two things W3-07 asks for that are not there, both small and both structural:**

1. **`SchwartzMap` membership is never stated.** AINTLIB works in `C(E, ℂ)` and supplies
   summability by hand (`summable_norm_restrict_weightedGaussianCM`,
   `summable_fourier_weightedGaussianCM`), because its Poisson summation is stated over
   continuous maps with explicit summability hypotheses rather than over the Schwartz class.
   If the FLT node is restated over AINTLIB's Poisson route, **the Schwartz requirement
   disappears entirely**; if it is kept as written, this is a genuine S-sized obligation.
2. **The domain is `EuclideanSpace ℝ (index K)`, not `mixedSpace K`.** The transport is not
   missing, it is Mathlib's own orthonormal coordinate map —
   `embeddingCoords K x i = (stdBasis K).repr (mixedEmbedding K x) i` (`IdealLattice.lean:117/121`).
   XS bridge, same class as W3-06's.

**Verdict: covered, stronger than recorded on the constant, with one XS transport lemma and
one S-sized `SchwartzMap` obligation that the right node shape deletes.**

## A27. W3-08 gets a better citation than the one I gave it

I verified W3-08 earlier via `covolume_idealZLattice`. That was the wrong lemma to cite —
the *statement* is in the port, directly:

```lean
-- IdealLattice.lean:148
noncomputable def dualityWeights : index K → ℝ :=
  Sum.elim (fun _ => 1) (fun p => if p.2 = 0 then 2 else -2)

-- IdealLattice.lean:162
theorem inner_diagScale_embeddingCoords (a b : K) :
    ⟪(diagScale (dualityWeights K) _) (embeddingCoords K b), embeddingCoords K a⟫
      = ((Algebra.trace ℚ K (b * a) : ℚ) : ℝ)
```

That **is** W3-08: `Trace_{K/ℚ}(b·a) = B(ι b, ι a)` with `B` the explicit bilinear form. And
the packet's stated trap — "the trace pairing is bilinear while the inner product is
sesquilinear-shaped at complex places; there is **no conjugation** in `B`" — is exactly the
`(2, −2)` weight pair at `(re, im)`. The minus sign *is* the absent conjugation, machine-
checked. W3-08 upgrades from "covered" to "covered, and the trap is already discharged."

## A28. W3-09 and W3-11 are **not covered** — and unlike W3-05, they are not covered because AINTLIB took a different road

This is the finding with dispatch consequences, so I am stating the negative evidence
explicitly rather than asserting absence.

**W3-09 (F3a, unit-orbit ↔ ideal bijection).** `ClassTheta.lean` contains no bijection of
this kind. Its 20 declarations are class-group bookkeeping (`classGroup_mk_eq_mk_iff`,
`classRep`, `dualClass_bijective`), an ideal norm (`idealNormR`), and the class-summed theta
`heckeGClass` / `heckeF` with their inversion laws. Searched across all 13 files:
`fundamentalCone`, `integerSet`, `idealSetEquivNorm` — **zero occurrences**, so the Mathlib
special case W3-09 says to generalise is not used anywhere in the port. `torsionOrder`
occurs in exactly two roles: as the divisor `(torsionOrder K)⁻¹` in the definition of
`heckeG` (`HeckeTheta.lean:362`) and inside the box-volume constant in `FEPair.lean`.
**Never as W3-09's counting statement** ("each orbit meets a torsion-free section in exactly
`w` elements"), and the norm identity `|Norm α| = N((α)I⁻¹)·N I` is nowhere stated.

The nearest thing is unit *invariance* of the theta — `unitMulLatticeEquiv` (:126) and
`heckeTheta_unit_mul` (:168) — which is a different assertion: the orbit is quotiented by an
integral over a fundamental box, not enumerated by a bijection.

**W3-11 (D1, polar decomposition of the parameter space).** Nothing in `Existence.lean`
resembles it; that file is the completed-zeta assembly. Across all 13 files there is **no**
`polar`, no `NormLeOne`, no `expMap`, and no norm-one surface `S = Nm⁻¹{1}`. AINTLIB never
constructs `Y ≅ (0,∞) × S`. It goes through log-coordinates a different way:

```lean
-- HeckeTheta.lean:361
noncomputable def heckeG (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) : ℝ :=
  (torsionOrder K : ℝ)⁻¹ *
    ∫ u in ZSpan.fundamentalDomain
      ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ),
      heckeTheta K I (heckeWeights K t u)
```

— a Lebesgue integral over a fundamental box of the **unit lattice** in `logSpace K`, with
`heckeWeights t u` carrying the single scale parameter `t`, periodicity supplied by
`heckeTheta_heckeWeights_periodic` (:311) so the box choice is immaterial, and the
`torsionOrder` divisor doing the job W3-09's counting statement was supposed to do.

**Both routes end at the same place, and AINTLIB's end is proved:**

```lean
-- Existence.lean:369
theorem exists_isCompletedDedekindZeta : ∃ Λ : ℂ → ℂ, IsCompletedDedekindZeta K Λ
-- Existence.lean:412
theorem completedDedekindZeta_one_sub (s : ℂ) :
    completedDedekindZeta K (1 - s) = completedDedekindZeta K s
```

So the correct statement is **not** "the port is missing two units." It is: **W3-09 and
W3-11 are artifacts of the route *we* designed** (polar decomposition + orbit enumeration —
the modern presentation), and **the port carries a complete alternative route to the same
theorem** (Hecke's own: unit-box average of a multivariable theta, torsion divided out).
If C2 is restated over AINTLIB, W3-09 and W3-11 are **not ported, not repaired, and not
needed — they are deleted.** If C2 keeps our route, they must be written from scratch and
the port helps with neither.

That is a route decision, and it is above my authority to take. It is now stated with
enough evidence to be taken by someone.

## A29. Item 2 CLOSED — final table for all twelve held units

| unit | verdict | what it costs |
|---|---|---|
| W3-01 (A2 fundamental domain) | **covered** | — |
| W3-02 (A3 dual covolume) | **covered**, exact generality | — |
| W3-03 (F2a gamma factor) | **covered** | — |
| W3-04 (C2 Gamma norms) | **covered, stronger** (no `t ≠ 0` at ½) | delete `ZeroTheoryN2.lean`, re-export |
| W3-05 (N5 Borel–Carathéodory) | **NOT covered** — and it is in **Mathlib** | restate N7 over `norm_logDeriv_le_of_norm_le`, or take BC from Mathlib |
| W3-06 (N6 analytic log) | **covered**, more general domain | XS: two corollaries (`Re L`, `deriv L`) |
| W3-07 (A5 anisotropic Gaussian) | **covered**, constant exact, `2^{r₂}` discharged | XS transport + S `SchwartzMap` (deleted by the right node shape) |
| W3-08 (B1 trace pairing) | **covered**, trap discharged | — |
| W3-09 (F3a orbit ↔ ideal) | **NOT covered** — route-specific | delete if C2 adopts AINTLIB's route; write from scratch if not |
| W3-11 (D1 polar decomposition) | **NOT covered** — route-specific | same |
| W3-12 (N19 test-function decay) | **covered, broader class** (§A10) | S inclusion lemma *or* restate over `IsAdmissibleTestFn` |
| W3-13 (N1 interface) | **hold by design** | write against ported names |

**Headline, unchanged and now complete: there is no unit where the port is too weak for its
consumer.** Every gap found is one of three kinds — a residual I invented (§A24, twice), a
statement that lives in Mathlib instead (W3-05), or a node that exists only because of a
route choice we made and the port did not (W3-09, W3-11).

**Where §A2 was reliable and where it was not, since this is the reusable lesson:** the map
is right on every row I derived from declarations, and wrong or overstated on four of the
rows I filled in from filenames — W3-05, W3-09, W3-11 (all three "yes (high confidence)",
all three wrong) and the W3-07 row that flattened a proved `2^{r₂}` result into "yes". Three
of the four wrong rows sit in the **single line** `W3-09 / W3-10 / W3-11 | … | yes (high
confidence)`. **One line covering three units is the shape of the error.** Whoever writes
the next substrate map: one row per unit, and cite the declaration or write "not checked".

**Item 2 is closed.** Sequencing for the rest of §A16 is unchanged: item 1 (`#print axioms`
on the `ExplicitFormula` consumers) needs a warm build and is not mine; item 3 waits on
items 1 and 2; **item 4 still must not run first.**

---

# ADDENDUM 8, 2026-08-17T22:52Z — **RETRACTION.** §A28 is wrong. W3-09 and W3-11 *are* covered. I asserted absence from a corpus I had not established was complete.

Twenty minutes after publishing ADDENDUM 7 I checked the AINTLIB tree against the files I
had on disk. **`CompletedZeta/` contains 16 Lean files. I had fetched 13.** The three I
never had are `MellinAgreement.lean` (110 KB), `ThetaEstimates.lean` (30 KB) and `GRH.lean`.
The negative evidence in §A28 — "zero occurrences of `fundamentalCone`, `integerSet`,
`idealSetEquivNorm`, `polar`, `NormLeOne`, `expMap` across all 13 files" — was run over an
incomplete corpus and is void. Re-run over all 16, the first three are all in
`MellinAgreement.lean`.

**This retraction supersedes §A28 and the W3-09 / W3-11 rows of §A29.** ADDENDUM 7's other
findings (§A26 W3-07, §A27 W3-08) are unaffected and re-confirmed below where they change.

## A30. W3-09 (F3a, unit-orbit ↔ ideal) — **covered**, in a different shape

```lean
-- MellinAgreement.lean:140  the orbit decomposition, on Mathlib's fundamentalCone/integerSet
noncomputable def coneUnfoldEquiv (J : (Ideal (𝓞 K))⁰) :
    (idealSet K J) × (Fin (rank K) → ℤ)
      ≃ {x : mixedSpace K // x ∈ mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J)
          ∧ x ≠ 0}

-- MellinAgreement.lean:812  the norm identity
theorem abs_norm_conePreimage (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) :
    ((|Algebra.norm ℚ (conePreimage K J a)| : ℚ) : ℝ) = (intNorm (idealSetMap K J a) : ℝ)

-- MellinAgreement.lean:822  the counting step, torsionOrder as the multiplicity
theorem tsum_idealSet_norm_rpow (J : (Ideal (𝓞 K))⁰) (σ : ℝ) :
    ∑' a : idealSet K J, ENNReal.ofReal ((|Norm ℚ (conePreimage K J a)|^2) ^ (-σ))
      = (torsionOrder K)
        * ∑' I : {I : (Ideal (𝓞 K))⁰ // J ∣ I ∧ IsPrincipal I},
            ENNReal.ofReal ((Ideal.absNorm I ^ 2) ^ (-σ))
```

Every ingredient W3-09 asks for is present: the unit-orbit unfolding, the norm identity, and
the `torsionOrder` multiplicity — and it is built on `fundamentalCone` / `integerSet`, which
is precisely what W3-09's envelope says to generalise ("read that file first; this node is
largely its generalization").

**What differs is the shape, and it matters for how the node is stated, not for whether it
must be proved:**

- W3-09 wants a **bijection of sets** `(I ∖ {0})/𝓞ˣ ≃ {𝔟 integral : [𝔟] = [I]⁻¹}`. AINTLIB
  gives an **equivalence** (`coneUnfoldEquiv`) plus a **summed identity over principal
  ideals divisible by `J`** (`tsum_idealSet_norm_rpow`, `principalDvdEquiv:933`,
  `tsum_principal_dvd_eq:980`).
- The **class indexing** is factored out elsewhere (`ClassTheta`'s `classRep` / `heckeGClass`)
  rather than carried inside the bijection.
- The torsion multiplicity appears as a **constant in a `tsum` identity**, not as
  "each orbit meets a torsion-free section in exactly `w` elements".

**Verdict: covered — restate the node over the port's shape rather than porting to W3-09's
signature.** The cost is node re-authoring, not proof work.

## A31. W3-11 (D1, polar decomposition) — **covered** on the log side, with the Jacobian left existential

```lean
-- MellinAgreement.lean:626 / :722 / :1058
noncomputable def heckeLogMap : (ℝ × logSpace K) →ₗ[ℝ] (InfinitePlace K → ℝ) where
  toFun p := fun w => p.1 / (Module.finrank ℚ K) + 2 * fullLog K p.2 w / mult w
noncomputable def heckeLogEquiv : (ℝ × logSpace K) ≃ₗ[ℝ] (InfinitePlace K → ℝ) := …
noncomputable def heckeLogCLE  : (ℝ × logSpace K) ≃L[ℝ] (InfinitePlace K → ℝ) := …

-- MellinAgreement.lean:1081  the measure statement
theorem map_heckeLogCLE_volume :
    Measure.map (heckeLogCLE K) (volume : Measure (ℝ × logSpace K))
      = heckeJacobian K • (volume : Measure (InfinitePlace K → ℝ))
theorem heckeJacobian_pos : 0 < heckeJacobian K          -- :1087
```

**This is W3-11, done exactly the way W3-11's own sketch says to do it** — "transport
everything along `log` to a linear direct-sum decomposition of `ℝ^{r₁+r₂}` into the weighted
diagonal and the trace-zero hyperplane; both summands carry Lebesgue measure and the
splitting is measure-preserving." The `ℝ` factor is the ray parameter, `logSpace K` is the
trace-zero hyperplane — the norm-one surface `S` in log coordinates — and `heckeLogCLE` is
the splitting, with the Haar pushforward computed.

**Two differences from W3-11 as written:**

1. It lives on the **log side** (`InfinitePlace K → ℝ`), not on `Y = (0,∞)^{places}` with
   the multiplicative Haar `⊗_v dy_v/y_v`. Transporting across `exp` is the remaining step
   if the consumer insists on the multiplicative picture.
2. **The Jacobian is existential.** `heckeJacobian` is defined as an
   `addHaarScalarFactor` and only `heckeJacobian_pos` is proved — AINTLIB's own docstring
   says "Its value is never needed — only positivity." W3-11 asks for measure-*preserving*,
   i.e. the constant `= 1`. If the FLT consumer only needs positivity, this is done; if it
   needs the exact constant, that is genuine residual work.
3. W3-11's `μ_S` invariance under multiplication and under `s ↦ s⁻¹` is not stated. On the
   log side both are translation and negation invariance of Lebesgue measure, so they are
   cheap, but they are not there.

**Verdict: covered, with an explicit `exp`-transport question and an explicit
constant-vs-positivity question.** Neither is a from-scratch node. **W3-11's own risk note —
"if this node starts to look L-sized, that is the signal that it was rebuilt instead of
reused" — is exactly right, and reusing means reusing `heckeLogCLE`.**

## A32. Two more corrections falling out of the same three files

- **W3-07's coordinate transport is not an obligation — it is stated.**
  `euclidMixedEquiv : EuclideanSpace ℝ (index K) ≃ₗ[ℝ] mixedSpace K`
  (`MellinAgreement.lean:246`), with `mem_idealZLattice_iff_euclidMixed` (:251) tying it to
  the lattice. §A26's "XS transport lemma" is discharged. **The `SchwartzMap` obligation
  stands** — zero occurrences of `SchwartzMap` across all 16 files, re-checked.
- **§A17's scope claim was wrong: it said "0 sorry / 0 admit / 0 axiom across 13 files".**
  Re-run across all **16**: still **0 sorry, 0 admit, 0 axiom**. The conclusion survives;
  the scope statement did not, and a scope statement that undercounts the corpus by three
  files is the kind of thing a port decision should not rest on.

## A33. Corrected final table — item 2, all twelve held units

| unit | verdict | what it costs |
|---|---|---|
| W3-01 (A2 fundamental domain) | **covered** | — |
| W3-02 (A3 dual covolume) | **covered**, exact generality | — |
| W3-03 (F2a gamma factor) | **covered** | — |
| W3-04 (C2 Gamma norms) | **covered, stronger** | delete `ZeroTheoryN2.lean`, re-export |
| W3-05 (N5 Borel–Carathéodory) | **not in the port; it is in Mathlib** | restate N7 over `norm_logDeriv_le_of_norm_le`, or take BC from Mathlib |
| W3-06 (N6 analytic log) | **covered**, more general domain | XS: two corollaries |
| W3-07 (A5 anisotropic Gaussian) | **covered**, constant exact, `2^{r₂}` proved, transport stated | S: `SchwartzMap`, deleted by the right node shape |
| W3-08 (B1 trace pairing) | **covered**, trap discharged | — |
| W3-09 (F3a orbit ↔ ideal) | **covered, different shape** | restate node over `coneUnfoldEquiv` + `tsum_idealSet_norm_rpow` |
| W3-11 (D1 polar decomposition) | **covered on the log side** | `exp`-transport if needed; Jacobian is positive-but-unevaluated |
| W3-12 (N19 test-function decay) | **covered, broader class** (§A10) | S inclusion lemma *or* restate over `IsAdmissibleTestFn` |
| W3-13 (N1 interface) | **hold by design** | write against ported names |

**Eleven of twelve are covered; the twelfth is in Mathlib.** The port is materially stronger
than my map ever claimed, and the corrected picture removes the route fork §A28 invented —
there is no fork, because AINTLIB carries both the orbit unfolding *and* the log splitting.

## A34. The failure, stated plainly, because it is now three of a kind

Same class, three mechanisms, all mine:

1. **§A11/§A20** — generalised from the file whose *name* matched the topic (`GammaStrip`),
   while the general statements sat in `AnalyticControl`.
2. **§A2's W3-05/W3-09/W3-11 rows** — filled in from filenames, never from declarations.
3. **§A28** — asserted absence from a corpus I had never established was complete, and said
   so in the strongest available terms ("zero occurrences … across all 13 files"), which
   made a wrong claim *read* as rigorous. The grep was honest; the corpus was not.

The rule that would have caught all three, and which I am writing into the record rather
than resolving to remember: **before asserting a negative, print the denominator.** State
what was searched and establish that it is everything — here, one `git/trees` call against
the pin, which took four seconds and which I ran only *after* publishing the claim.

**Blast radius, checked rather than assumed.** §A28 shipped in `d2b86cb` and in relay block
20 to hub-r7qdn.2 / hub-lsb1u.6.10, which asked C2 to consider deleting W3-09 and W3-11 as
route artifacts. Nothing has consumed it — the bridge is unreachable, so block 20 has not
been posted, and the fleet has produced nothing for ~32h. A retraction block follows it in
the same file. **No dispatch has been made on the strength of §A28**, which is luck rather
than process, and the process fix is the denominator rule above.

---

## ADDENDUM 9 — W3-10 is NOT fresh work. Its release was a fourth instance of the same error. (2026-08-17T23:00Z)

**§A2's W3-10 row said "not re-derived — treat as unchecked". It is now checked, and the
answer changes a dispatch decision: W3-10 was RELEASED from the hold on the strength of
"I checked all 35 files and there is no partial-zeta object anywhere, so it is genuinely
fresh work" (§A6 dispatch list, and `wave-3-packets.md` §2 line 45). That claim is wrong.**

### §A35 — the denominator, printed first this time

Before asserting anything about presence or absence I ran the rule from §A34:

```
GET api.github.com/repos/CBirkbeck/AINTLIB/git/trees/1c1c74664e40?recursive=1
→ 2678 .lean files, truncated: false
   projects/DedekindResidue/DedekindResidue/   35   ← the corpus "35 files" refers to
     CompletedZeta/    16
     ExplicitFormula/  11
     top level          8   ← Basic, AuxiliaryFunction, Lemma2–5, MainTheorem, QSide, Theorem1
```

So the **35 is right** — that scope statement survives, unlike §A17's "13". I had fetched
16 of the 35; the 8 top-level files were fetched for this addendum. Across all 25 files now
local: **0 sorry, 0 admit, 0 declared axiom** in tactic or term position. (`Basic.lean`
matches a naive `sorry` grep **in prose only** — its module docstring. Same live/prose split
the FLT oracle has; the naive grep is wrong on this file in exactly the way §4 of
`oracle-recount.md` describes.)

`Basic.lean:22-24` also states the port's own axiom claim, which is the closest thing to
§A16 item 1 available without a build: *"the generalized Riemann hypothesis is the **only**
assumption, threaded as an explicit hypothesis (never an `axiom`); every result is
`sorry`-free and axiom-clean (`#print axioms` = `propext`, `Classical.choice`,
`Quot.sound`)."* That is an author's docstring, not a machine check, and item 1 still needs
the build — but it is a claim from the source rather than an inference from mine.

### §A36 — what W3-10 actually asks for, and what is there

W3-10 wants four things. Checked one at a time, against declarations:

| W3-10 obligation | AINTLIB | verdict |
|---|---|---|
| define `ζ(A,s) = ∑_{𝔟 : [𝔟]=A} (N𝔟)^{−s}` | the sum `∑' b : {b : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 b = C}, ofReal ((N b)²)^(−σ)` — the summand of `lintegral_mellin_heckeGClass_dev` (`MellinAgreement.lean:1507`) and the RHS of `tsum_principal_dvd_eq` (:980); **14 occurrences, all in `MellinAgreement.lean`** | **present as an object, absent as a `def`** |
| absolute convergence on `Re s > 1` | `summable_ideal_norm_rpow` (:1860) for the **full** ideal sum at real `s > 1`, via `count_LSeriesSummable` (:1790) | **proved for the total; per-class is a nonneg-subtype comparison away, not stated** |
| `∑_A ζ(A,s) = dedekindZeta K s` | split on the **theta side**: `heckeF = ∑_C heckeGClass` (`ClassTheta.lean:245`), transported by `lintegral_mellin_heckeF_dev` (:1637), whose proof does the class split pointwise; then `dedekindZeta_real_eq` (:1940) identifies the total ideal norm-sum with `dedekindZeta K s` | **both halves proved; the direct Dirichlet-side statement is not** |
| crude `ζ(A,s) = O(ζ(Re s))` | not stated | **absent — but it is nonneg-subtype domination of an already-summable family** |

Two real limitations, stated so nobody over-reads this correction:

1. **Everything is at real `s`.** `dedekindZeta_real_eq` is `dedekindZeta K (s : ℂ)` for a
   **real** `s > 1`. W3-10 wants *analyticity on the half-plane* `Re s > 1`, and there is no
   complex-`s` statement for the class-restricted sum anywhere in the corpus (grep for
   `Summable`/`AnalyticOn`/`DifferentiableOn` near `ClassGroup`/`mk0` returns nothing).
2. **The normalisation differs.** AINTLIB's exponent is `((N b)^2)^(−σ)`, i.e. `N b^{−2σ}`
   — Hecke's `σ ↔ s/2`. Any consumer must carry that factor of two, and it is the kind of
   thing that silently halves a half-plane if nobody writes it down.

**Verdict: W3-10 is PARTIALLY covered — enough that dispatching it as "genuinely fresh
work" would send a worker to re-derive a summability proof and a zeta identification that
already exist, machine-checked, and to re-invent an object AINTLIB uses fourteen times.**
The genuinely new content is the packaging: a named `partialZeta` def, per-class summability
by subtype comparison, the complex-`s` upgrade, and the crude bound. That is still an S, but
it is an S *against ported signatures*, not an S from scratch — and it belongs on the
**hold** list with the other eleven, not on the dispatch list.

### §A37 — the error class, fourth instance, and the sharper rule

§A34 recorded three instances and the fix "before asserting a negative, print the
denominator." **I printed the denominator this time and still would have been wrong,
because that was not the failure here.** The corpus was right; the *query* was wrong.

`grep partialZeta` over all 25 files returns **zero** — and that is a true fact about a
name. The object is spelled `{b // ClassGroup.mk0 b = C}` inside a `tsum`, has no name of
its own, and appears in a file whose name promises Mellin transforms rather than zeta
functions. **I searched for the name of the thing instead of the shape of the thing**, got a
clean zero, and released a packet on it.

**Rule, extending §A34's:** a negative needs *two* things — a denominator you have
established is complete, **and a query that would find the object if it were spelled
differently**. For a mathematical object that means grepping the *type shape* (here: the
subtype of ideals restricted by `ClassGroup.mk0`, or `absNorm … ^ (-`), not the name a
Mathlib-idiomatic port would have used. The three previous instances were all "reasoned from
the file name"; this one is "reasoned from the identifier name". Same disease, one level
down.

**Blast radius, checked rather than assumed:** W3-10 sits on the dispatch list in
`wave-3-packets.md` §2 and in §A6 here. The fleet has produced no output since
2026-08-16T14:40:07Z and no worker has been sent to it, so — again by luck, not process —
nothing consumed the release. Both documents are corrected in place by this addendum.
