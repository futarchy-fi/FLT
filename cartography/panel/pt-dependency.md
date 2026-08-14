# Adversarial review: PT/CFT dependency graph (hub-lsb1u.7.4) — DEPENDENCY HONESTY

Reviewer: adversarial panel seat, FLT-on-Lean, Poitou–Tate chapter. Verified against
`origin/cartography/pt-reconciled:cartography/pt-reconciled.md`,
`origin/cartography/cft-reconciled:cartography/cft-reconciled.md`, and the working-tree
blueprint/Lean sources on 2026-08-14. Not committed.

## 1. CFT boundary leaks (walking the 16 merged PT nodes)

The boundary as stated ("CFT exports only inv_v: H²≅ℚ/ℤ [node 6] + sum-of-invariants=0
class-formation cut [node D2]") holds for 14 of 16 nodes on inspection. Two suspects:

- **Node 10 → 11′ seam (restricted-product topology).** Node 10 bundles "restricted product
  Pⁱ" as *defs only*, M/L. But NSW derives middle-exactness (11′, graded L, kept in-package)
  as a *special case* of the fully topologized nine-term theorem — the exactness proof itself
  routes through the same locally-compact/Pontryagin-duality apparatus for Pⁱ that node 11
  (explicitly descoped as "restricted-product topology, Pontryagin duals of non-compact
  groups") disclaims. The doc budgets that topology once, as free (node 10 "defs only"), then
  again implicitly inside 11′'s L-cost without naming it. This is exactly the leak the brief
  warns about: restricted-product topology *is* adelic CFT machinery wearing a definitional
  costume. No node explicitly re-derives or re-costs "topology needed to prove exactness at
  the middle term specifically (vs. the full complex)" — it's assumed inherited from 10 for
  free. Flag as a real, uncosted edge.
- **Node 12 (global Euler characteristic) has no `\uses`-style audit.** Every other
  consumer-facing claim in both docs is traced to a specific blueprint `\uses` list or Lean
  line (see MLT: ch04overview.tex:66-71, exhaustively re-verified). Node 12 gets only a
  literature citation (NSW 8.7.4/Milne I.5.1), no dependency breakdown. Global Euler
  characteristic is precisely the kind of theorem whose classical proof pulls in
  finiteness-of-class-group / unit-theorem-flavored global input beyond a bare local-inv
  black box — the doc's own discipline (rigorous \uses-tracing) is absent exactly where a
  CFT leak would be easiest to hide.

No other leak found: node 6 is correctly the sole explicit CFT import; D2 is correctly named
as the class-formation cut and is symmetric between the two docs (PT §2.4 / CFT §2.4, node
7/8) — the cross-doc alignment on the boundary itself is real, not just asserted.

## 2. Cup-product grading verdict: HONEST

Read `FLT/Mathlib/RepresentationTheory/Homological/ContCohomology/CupProduct.lean` (584
lines): `cupComplex`, `cupCochain`, `ContinuousCohomology.cup`, and the Leibniz rule
`cup_d_comm` are constructed/proved, not stubbed — zero `sorry`/`axiom`. The lone `## TODO` is
"minimise imports once construction complete," cosmetic. The doc's "S (residual)" grading for
node 2 is accurate, not sandbagged. Local Tate duality's remaining topological-group-cohomology
dependency (continuous cohomology of profinite groups, LES/inflation-restriction/Shapiro) is
explicitly carried as nodes 1 and 3 — not hidden. However, node 1's "M" size is optimistic
against external evidence: Livingston's ITP2023 account of Mathlib group cohomology states the
profinite-as-limit-of-finite-quotients comparison and associated spectral-sequence work remain
open/nontrivial in Mathlib proper — which is why FLT built its own bespoke `ContCohomology`
layer instead of using stock Mathlib. That bespoke layer exists and has real content, but
grading its "discrete-comparison over finite quotients" piece M rather than L/XL deserves
skepticism.

## 3. Euler-characteristic audit

Local (node 8, NSW 7.3.1) and global (node 12, NSW 8.7.4) are both present as distinct nodes —
good, not conflated. But per §1, node 12 is the least-audited node in the table: it has size L
and "yes" in-package with no listed prerequisites beyond a citation, unlike its sibling nodes.
Given Greenberg–Wiles (13) explicitly depends on 12, an unaudited global-Euler-char node is a
soft spot directly upstream of the one theorem the whole package exists to deliver.

## 4. Ready-now audit

Verified: `ContCohomology/Basic.lean` and `CupProduct.lean` have no `sorry`/`axiom` — the base
the "def-only" ready-now items (H¹_nr, M*, pairings, Selmer) would sit on is real, not
aspirational. But "truly unblocked in current Mathlib" overstates it: this infrastructure is
FLT-local (`FLT.Mathlib...ContCohomology`), not upstream Mathlib — stock Mathlib
`RepresentationTheory/Homological/GroupCohomology` has Shapiro's lemma etc. for ordinary
(finite-group) cohomology only; continuous/profinite Galois cohomology is still described in
the community literature as partly WIP outside the main library. The ready-now items are
unblocked against *FLT's own extension*, which is a materially weaker and more fragile claim
than "current Mathlib group-cohomology API," and the doc's phrasing elides that distinction.

## 5. Grade consistency

Inconsistent in two places: (a) node 1 sized M while carrying work independently described as
requiring spectral-sequence-level effort elsewhere; (b) node 12 sized L with zero dependency
audit, next to MLT's fully `\uses`-traced sibling claim in the same document — the rigor is not
applied uniformly, and the two least-audited nodes (10's "defs only" restricted-product
topology, 12's uncited Euler-char prerequisites) are exactly the two places a CFT leak would
most plausibly hide.

File written: `/Users/kas/FLT/cartography/panel/pt-dependency.md` (working tree only).
