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
  baseline in `oracle-recount.md` (live baseline **60**, not 71); diff confined to
  declared `write_paths`; no new axioms; licence header present in every ported file.
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
