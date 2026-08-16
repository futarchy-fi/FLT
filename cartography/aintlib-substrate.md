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

| wave-3 unit | node | AINTLIB file | covered? |
|---|---|---|---|
| W3-01 | A3 Poisson on `ℤ^d` | `PoissonSummation.lean` (`zpoint`, `intEquivSpanBasisFun`, `fundamentalDomain_basisFun_eq`, `mFourier`) | **yes** |
| W3-02 | A1 dual lattice | `DualLattice.lean` (`dualZLattice`, `mem_dualZLattice`, `dualZLattice_eq_span`, `covolume_dualZLattice_mul`) | **yes — and A2 as well** |
| W3-03 | F2a Deligne Gamma integrals | `Normalisation.lean` `gammaFactor` + `Existence.lean` `prod_place_gamma`, `Gammaℝ_ofReal`, `Gammaℂ_ofReal` | **yes** |
| W3-04 | N2 Gamma modulus identities | `GammaStrip.lean` `norm_Gamma_half_add_mul_I_sq`, `norm_Gamma_one_add_mul_I_sq` | **yes — and N3's two-sided strip bounds too** (`norm_Gamma_le_mul_exp`, `le_norm_Gamma_base`) |
| W3-05 | N5 Borel–Carathéodory off-center | `AnalyticControl.lean` | **yes** |
| W3-06 | N6 holomorphic logarithm | `AnalyticControl.lean:1924` | **yes** |
| W3-07 | A5 anisotropic Gaussian | `ThetaLattice.lean` / `HeckeTheta.lean` | **yes (high confidence)** |
| W3-08 | B1 trace pairing | `IdealLattice.lean` (`embeddingCoords`, `dualityWeights`, `covolume_idealZLattice`) | **yes** |
| W3-09 / W3-10 / W3-11 | F3a, F1, D1 | `ClassTheta.lean`, `MellinAgreement.lean`, `Existence.lean` | **yes (high confidence)** |
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
