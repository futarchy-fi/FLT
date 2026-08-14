# Zeta-FE port audit — AINTLIB & lean-pool (hub-lsb1u.6.6)

Audit date: 2026-08-14. Against `cartography/zeta-fe-decomposition.md` (24-node
tree, hub-lsb1u.6.4). Our baseline: toolchain `leanprover/lean4:v4.34.0-rc1`,
Mathlib pin `bc06ce9f` (2026-08-13). Method: GitHub API + shallow clones in
`/tmp` (deleted after audit); grep census, no builds run (disk-full machine —
build verification is the first follow-up bead).

## Verdicts

| Repo | Verdict | Nodes | Toolchain delta | License |
|---|---|---|---|---|
| CBirkbeck/AINTLIB | **PORT** | ~22/24 | v4.33.0-rc1, Mathlib −271 commits | Apache-2.0 ✓ |
| Vilin97/lean-pool | **PARTIAL** (coordinate, don't duplicate) | ~20/24 but D–G totally-complex only | v4.34.0-rc1 (identical), Mathlib −85 | Apache-2.0 ✓ (headers "The FLT Project") |

## 1. CBirkbeck/AINTLIB — PORT

**Path**: `projects/DedekindResidue/DedekindResidue/CompletedZeta/` — 16 files,
11,022 lines. Latest main commit `1c1c7466` (2026-07-31).

**Existence & build**: pipeline exists exactly as reported. **No Lean build CI**
(only blueprint-pages workflows, failing since June); `DedekindResidue` is a
non-default lake target ("built on demand") in the monorepo `lakefile.toml`.
However `.mathlib-quality/HANDOVER.md` claims "whole library builds green, zero
sorries", axioms `{propext, Classical.choice, Quot.sound}`, target
`belabas_friedman_thm1` proven 2026-07-03. Self-reported but specific;
**must be verified by a local `lake build DedekindResidue` on their pin before
any port bead is cut**.

**Census**: grep of all 16 CompletedZeta files + full DedekindResidue tree:
**0 `sorry`, 0 `admit`, 0 `axiom`** (the two textual "sorry" hits are
doc-comments asserting sorry-freeness). Uses the Lean module system
(`module` / `public import`) — same as FLT.

**Statement fidelity: exact match.**
- `Normalisation.gammaFactor = Gammaℝ^{r₁} · Gammaℂ^{r₂}` — Deligne
  normalization, identical to our PQ4 freeze.
- `completedZetaPrefactor = |Δ_K|^{s/2} · gammaFactor` ; on `Re s > 1`,
  `completedDedekindZeta = prefactor · dedekindZeta` (Mathlib's).
- Final FE (`Existence.lean:412`):
  `completedDedekindZeta_one_sub : completedDedekindZeta K (1 - s) =
  completedDedekindZeta K s` — **arbitrary number field K**, via a self-dual
  `WeakFEPair` (`heckeFEPair_symm`, `ε = 1`).
- Continuation as our G3 wants it: `completedDedekindZetaEntire` entire with
  `H s = s(s−1)Λ(s)` off `{0,1}`, plus a uniqueness predicate
  `IsCompletedDedekindZeta` + `eqOn`. Bonus: `generalizedRiemannHypothesis_iff`,
  `completedDedekindZeta_real` on `(1,∞)`.

**Node map** (AINTLIB file → our nodes):
- `DualLattice` → A1, A2; `PoissonSummation` → A3; `PoissonLattice` → A4;
  `ThetaLattice`/`ThetaEstimates` → A5, C1
- `IdealLattice` → B1, B2, B3
- `HeckeTheta` → C2, C3 and the D1–D3 unit-domain work (uses
  `fundamentalCone`/`regulator` machinery)
- `FEPair`/`ClassTheta` → E1, E2, G1
- `GammaStrip`/`MellinAgreement` → F1, F2a, F2b, F3a, F3b
- `Normalisation` → PQ4 freeze; `FunctionalEquation` + `Existence` → G2, G3
- **Not covered**: G4 (`dedekindZetaExt` — ζ_K itself continued by dividing out
  the Γ-monomial; no analog found) and G5 (our interface freeze — ours by
  definition). H1 residue material likely exists elsewhere in DedekindResidue
  (it is a Belabas–Friedman residue project) — audit separately if wanted.
- **≈ 22 / 24 core nodes covered.**

**Port cost**: LOW-MEDIUM. Same module system; toolchain one rc behind
(v4.33.0-rc1 → v4.34.0-rc1); Mathlib pin `3edb3c06` (2026-07-29) is 271 commits
behind ours — roughly two weeks of Mathlib drift, typically a rename-level bump
for this subject area. Namespace surgery `DedekindResidue.*` → FLT convention.
Internal deps are self-contained (`public import Mathlib` + intra-CompletedZeta
imports only, plus a CebotarevDensity dep elsewhere in the project — check it
does not leak into CompletedZeta at build time). Estimated 2–4 port beads vs
24 prove-from-scratch nodes (deepest chain 9).

**Risks**: (a) build claim unverified — no CI; gate the port on one local build;
(b) 271-commit Mathlib bump may touch `WeakFEPair`/`ZLattice` API; (c) monorepo
extraction — confirm no hidden deps on `Common/`.

## 2. Vilin97/lean-pool — PARTIAL

**Path**: `LeanPool/Odlyzko/{CompletedZeta,Theta,DedekindZeta}/` — 52 files,
12,054 lines. Very active (pushed 2026-08-14, the audit day).

**Existence & build**: exists; **real build CI green** (`lean_action_ci.yml`,
success on main and PR branches, 2026-08-14). Toolchain **identical to ours**
(v4.34.0-rc1); Mathlib pin `de5ce8a9` only **85 commits behind** ours. License
Apache-2.0 and file headers read "Copyright (c) 2026 The FLT Project" — this
effort is explicitly FLT-branded; porting is legally trivial, and the right
move is coordination (it is upstream-of-us in spirit).

**Census**: **0 `sorry`, 0 `admit`, 0 `axiom`** across the Odlyzko subtree.

**Statement fidelity: PARTIAL — totally complex only, pole-cleared form.**
- Normalization (`Defs.lean`): `completed = |Δ|^{s/2} · Γℝ^{r₁} · (Γℂ/2)^{r₂}
  · ζ_K` — a `2^{−r₂}` constant off our Deligne freeze (harmless for the FE,
  but an interface delta to reconcile).
- Final FE (`FunctionalEquation.lean:348`):
  `poleClearedCompletedDedekindZetaContinuation K s = … K (1 - s)` where the
  pole-cleared object equals `n · s(1−s) · completed K s` on `Re s > 1` —
  **under `variable [IsTotallyComplex K]`**. Continuation is via the entire
  pole-cleared function (differentiability proved); class-group reindexing along
  `traceDualInverseClassEquiv` mirrors our G2/G3 involution exactly.
- **Key consumer fact**: FLT's actual axiom (`FLT/Assumptions/Odlyzko.lean:58`,
  `Odlyzko_statement`) is itself stated for `[IsTotallyComplex K]`. For the FLT
  axiom-discharge consumer, lean-pool's specialization is a near-direct hit;
  it fails only our tree's stricter arbitrary-K M2 target (r₁ > 0 fields).

**Node map**: general-K portions — `Theta/PoissonSummation`, `TraceDual*`
(≈ A3–A4, B1–B2), parts of C; `DedekindZeta/` (Euler product, prime-ideal
summability) feeds the parent map's **M1**, not this tree. Totally-complex-
restricted: `UnitFundamentalDomain`, `UnitSlab*`, `ConeGaussian*`,
`RadialKernelFormula`, Mellin files, `FunctionalEquation` (≈ D1–G3
specialized). Rough count: **~8–10 nodes general-K, ~20/24 if the
totally-complex specialization is acceptable.** Extra beyond our tree:
`FunctionalEquationLogDeriv`, `VerticalGrowth`, `RightHalfPlane` nonvanishing,
and a large `ExplicitFormula/` layer (zero-counting, Jensen, Poitou) — these are
downstream Odlyzko-chapter material (M3+), valuable beyond M2.

**Port cost**: LOWEST of the two mechanically (same toolchain, 85-commit
Mathlib delta, green CI, FLT copyright) — but porting the FE wholesale imports
the `IsTotallyComplex` restriction. Recommended mode: **coordinate** (repo is
live-active), take their A/B/theta general lemmas and their `ExplicitFormula`
downstream layer, and either (i) accept totally-complex M2 to match the FLT
axiom as stated, or (ii) port AINTLIB for the arbitrary-K FE.

## Recommendation

1. First bead: local build check of AINTLIB `DedekindResidue` on its own pin
   (their claim is unverified by CI). If green → port AINTLIB CompletedZeta as
   the arbitrary-K M2 spine (~22/24 nodes, 2–4 beads: bump pin 271 commits,
   toolchain +1 rc, namespace surgery, G4/G5 written fresh on top).
2. In parallel: contact lean-pool (FLT-branded, active today) — de-duplicate;
   adopt their `DedekindZeta/` Euler-product files for parent-map M1 and keep
   their ExplicitFormula layer on the radar for M3+.
3. Reconcile the `2^{−r₂}` (`Γℂ/2` vs `Γℂ`) normalization delta in G5's
   interface freeze if any lean-pool statement is consumed directly.
4. Licenses: both Apache-2.0, same as FLT — port freely with attribution
   headers preserved.
