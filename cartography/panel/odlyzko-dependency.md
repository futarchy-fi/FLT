# Panel verdict — dependency honesty (hub-lsb1u.6.12)

Reviewed: `cartography/odlyzko-reconciled.md` (13-node map: M1–M12 + optional M13),
`cartography/zeta-fe-decomposition.md` (24-node S/M tree, scoped to M2 only),
`cartography/zeta-port-audit.md` (AINTLIB/lean-pool port audit).
Lens: dependency honesty — every claimed "no dependency", "ready-now", or
"discharged" edge is adversarially challenged below. Mathlib decls spot-checked
against the mathlib4 docs site (no local `.lake`).

## 1. Hidden edges per reconciled-map node

- **M3 (strip zeros / horizontal estimates).** The stated deliverable ("zero
  counting, horizontal-contour estimates to choose admissible heights") silently
  contains two unlisted prerequisites: (a) a zero-spacing lemma — existence of a
  height `T` with all zeros at distance `≥ c/log T`, standard in every
  argument-principle explicit-formula proof but never named as its own node —
  and (b) a Phragmén–Lindelöf-type convexity bound on `ζ_K`/`Λ_K` in vertical
  strips, needed to control the horizontal-segment error term. Neither appears
  as a sub-node anywhere; "XL, medium confidence" is a black box, not a
  decomposition.
- **M4 (rectangle/argument-principle identity).** Its legality (contour avoids
  zeros) is *silently* supplied by M3's unlisted zero-spacing lemma above — the
  edge M3→M4 is drawn, but the specific fact it must deliver is not stated.
- **M6 (Archimedean Γ/digamma side).** "Digamma identities" is asserted but no
  Mathlib decl is cited (unlike every node in the 24-node M2 tree) — an
  unverified Fourier/special-function prerequisite.
- **M7 (assembly).** Explicitly depends on unfrozen hypotheses on the test
  function `F` (BV, Mellin/Fourier convergence, sign convention) — the doc's own
  PQ4 admits this is open; correctly flagged, but it means M7's "M once M2–M6
  exist" size is optimistic until PQ4 is resolved.
- **M8 (positivity/prime discard).** "Maximum-principle positivity on the full
  critical strip" needs a Borel–Carathéodory/convexity bound on `log ζ_K'/ζ_K`
  to control the sign argument off the real axis — this convexity input is
  nowhere named as a prerequisite, and M8 is listed as "ready-now" despite it.
- **M9 (Tartar function).** "Prove `f≥0` and `f̂≥0`" is a genuine Beurling–Selberg-
  adjacent extremal-function construction, not definition-unwinding; "M, high
  confidence" undersells the Fourier-positivity step.
- Verdict: every node has at least one uncredited analytic-continuation,
  convexity, or Fourier-analytic prerequisite; M3/M4/M8 are the worst offenders
  because their hidden inputs (zero-spacing, convexity bounds) are classical
  explicit-formula machinery that the reconciled map never lists as nodes.

## 2. Decomposition-coverage gap — CONFIRMED GAP

`zeta-fe-decomposition.md` states its own scope honestly ("Target: node **M2**")
and never claims to cover M3–M12. But the reconciled map's own M3 (zero
counting / argument principle) is graded XL — the *same* difficulty class the
24-node tree was built to eliminate for M2 — and receives zero decomposition in
either document. Zero-counting/argument-principle material is in **neither**
document. This is a real, undisclosed asymmetry: M2's XL wall got a full 24-node
audited tree with cited Mathlib decls; M3's XL wall got one line. A reader
skimming "no L, no XL" in the decomposition doc's node-count summary can easily
over-generalize that to the whole Odlyzko path, when in fact the argument-
principle/zero-density crater for M3–M4 is untouched and may be comparably deep
(a second 15–25-node tree is plausible and has not been attempted).

## 3. Ready-now audit (5 nodes: M8, M9, M10, M11, M12)

None of the five cite a single Mathlib declaration — a sharp contrast with the
24-node M2 tree's decl-by-decl discipline. "Ready-now" here means only "no
blocking upstream Lean artifact", not "verified against Mathlib." M8 is
explicitly conditional ("under an explicit-formula hypothesis") — cutting it
produces a parametrized lemma that discharges nothing until M2–M7 exist; tracking
it as progress risks phantom completion. Spot-checked decls actually cited by
the *decomposition* doc's first-wave nodes do check out on mathlib4 docs:
`WeakFEPair`/`AbstractFuncEq` (Loeffler), `UnitAddTorus.mFourierCoeff`/
`AddCircleMulti`, `Complex.Gammaℝ`/`Gammaℂ` (`Gamma.Deligne`),
`fourierIntegral_gaussian_innerProductSpace'`, `ZLattice.covolume`, and
`FractionalIdeal`/`DedekindDomain.Different` all exist as named. One overclaim
found: A1/A4 assert "Deps: none" (pure core-Mathlib), but the only working
Lean precedent for exactly this lattice-Poisson-summation-weighted-by-covolume
pattern (`dualLattice`, `SchwartzMap.PoissonSummation_Lattices`) lives in the
external **Sphere-Packing-Lean** repo, not core Mathlib's `ZLattice/Covolume`
file — and that repo is absent from the doc's own "Prior art" section, an
uncredited near-duplicate.

## 4. Port-discharge audit

The audit's own caveats are honest (AINTLIB build unverified, no CI; lean-pool
normalization delta flagged), but the headline "~22/24 PORT" undercounts real
risk: (a) the 22/24 figure is pre-build-verification — the audit itself says
this must gate any port bead, so today it is 0/24 *confirmed* discharged; (b)
the node-map entry "`HeckeTheta` → C2, C3 and the D1–D3 unit-domain work" is a
file-bucket guess, not a statement-level match — D1's measure-plumbing
(Haar-through-`exp` transport) is flagged in the decomposition doc itself as a
fiddly risk node, and the audit shows no line-level check that AINTLIB's
`HeckeTheta` file proves the same generality (arbitrary `K`) rather than
restating it under different hypotheses; (c) lean-pool's `Γℂ/2` vs `Γℂ`
constant is a genuine interface mismatch — porting it as-is would *restate*,
not discharge, node C2/G2; (d) lean-pool's FE is proved only under
`[IsTotallyComplex K]`, so relative to the reconciled map's arbitrary-`K` M2
target it discharges nothing (matches the FLT axiom's consumer shape, not the
tree's stated generality — correctly flagged by the audit as failing "the
stricter arbitrary-K M2 target"). Bottom line: even a fully successful port
discharges **only M2** of the 12-node reconciled map (~1/12 nodes, plus a
possible partial assist to M1 via lean-pool's `DedekindZeta/` files, itself
unbuilt) — it is not a shortcut for M3–M12, which remain 100% unaddressed by
either external repo.

## 5. Grade consistency

M2 = XL is well-supported by its own 24-node breakdown (deepest chain 9,
S/M-only) — consistent. M3 = XL is asserted with no supporting decomposition at
all — inconsistent *level of scrutiny* versus M2, even if the size guess is
correct; it should be graded "XL, low confidence" rather than "medium." M9 = M
"high confidence" looks too low against the difficulty of proving Fourier
positivity of an explicit extremal function — more plausibly L. M13 = M "high
confidence numerically, conditional on consumer degree" is properly hedged and
consistent, since §3 of the reconciled map shows no degree-19 lemma exists.
The port audit's "high" confidence badge on ~22/24 nodes sits awkwardly next to
its own "must be verified by a local build before any port bead is cut" —
confidence should read "medium, pending build" until that gate clears.

---

10-line summary:
1. Hidden edges: M3/M4 lack a stated zero-spacing/argument-principle lemma; M8 lacks a named convexity (Borel–Carathéodory) input; M6 cites no Mathlib digamma decl; M9's Fourier-positivity step is harder than its grade implies.
2. Decomposition-coverage gap: CONFIRMED — the 24-node tree covers only M2; M3 (zero-counting/argument-principle), also graded XL, has zero decomposition in either document.
3. Ready-now audit: the 5 nodes (M8–M12) cite zero Mathlib decls, unlike the M2 tree; M8 is only conditionally provable pending M2–M7. Spot-checked M2-tree decls (WeakFEPair, AddCircleMulti, Gammaℝ/ℂ Deligne, fourierIntegral_gaussian_innerProductSpace', ZLattice.covolume, DedekindDomain.Different) all genuinely exist.
4. Overclaim: A1/A4 say "Deps: none" but the real dual-lattice-Poisson precedent lives in the external Sphere-Packing-Lean repo, uncredited in "Prior art."
5. Port-discharge audit: AINTLIB's ~22/24 is pre-build-verification (0/24 confirmed today); the HeckeTheta→D1–D3 mapping is a file-bucket guess, not line-level; lean-pool's Γℂ/2 constant and totally-complex restriction mean it restates rather than discharges the arbitrary-K M2/G2 target.
6. Net port impact on the 12-node reconciled map: at best ~1/12 nodes (M2), not a general Odlyzko-chapter shortcut.
7. Grade consistency: M2=XL well-supported; M3=XL asserted with no scrutiny (should read low-confidence); M9=M/high plausibly underrated (more like L).
8. M13 (degree-19 shortcut) is properly hedged as conditional — no consistency issue there.
9. Recommend: decompose M3 with the same discipline as M2 before trusting the "no L/XL left" narrative; require AINTLIB build-green confirmation before crediting any port node as discharged.
10. Verdict file: /Users/kas/FLT/cartography/panel/odlyzko-dependency.md (working tree only, not committed).
