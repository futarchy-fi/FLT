# Panel review — mb-reconciled.md (DEPENDENCY HONESTY lens)

Verified against `origin/main` @ e99f1674 (2026-08-14). All file/line citations in
mb-reconciled.md §2b, §3, §4 spot-checked directly; no fabricated anchors found.

## 1. D6 predicate sizing (induced-from-character, ordinary-reduction)
Confirmed S-sized and genuinely absent, not just "under-searched":
- `git grep -ni "induced.*character"` in FLT/ → zero hits. `dihedral` hits are all
  PGL2 finite-subgroup classification (`Slop/PGL2/FiniteSubgroups/*`), unrelated —
  no rep-theoretic induction functor exists anywhere in the repo (no
  `Induced`/`IsInduced` on `GaloisRep`). Mathlib's `Representation` induction
  machinery (`Representation.ind`/Frobenius reciprocity) is not imported/used by
  FLT at all, so "S-sized" assumes writing the induced-rep predicate from scratch
  over `GaloisRep` (not reusing an existing induction functor) — the doc doesn't
  say this but should; it's a real, if small, scope note.
- "Ordinary reduction": only prose hits, exactly as claimed —
  `Flat.lean:56` and `QuadraticTwists/QuadraticTwists.lean:182`. Mathlib's
  `WeierstrassCurve` + `Reduction.lean` gives `HasGoodReduction` (confirmed,
  `GoodReduction.lean:40`, `Flat.lean:128`) but nothing distinguishing
  ordinary/supersingular — no Hasse invariant, no formal-group-height predicate.
  D6's "S" size for *stating* ordinary-ness is fair; note it buys nothing toward
  ever *proving* ordinariness (a separate, unscoped debt not on the ledger).

## 2. Opaque node's hidden assumptions
- Chebotarev: web-checked (no local Mathlib vendored to grep, so this is
  secondhand, not primary-source verified this pass) — PNT+ project confirms
  Chebotarev density is not yet in Mathlib, tracked as a downstream goal of the
  L-functions/PNT+ effort. Doc's claim stands but the reconciled doc itself never
  flags "not vendored locally" for MB5/Chebotarev specifically, only for
  LinearDisjoint/IsKrasner — inconsistent hedging within the same document.
- Function-field vs. number-field: MB-D as drafted is number-field-only
  (`NumberField.IsTotallyReal`, `Representable.lean:56` confirms this exact
  combinator is number-field-scoped) — no mismatch risk since no function-field
  variant is claimed anywhere. Non-issue.
- Weak approximation: `AbsoluteValue.denseRange_algebraMap_pi` — zero hits in
  FLT/ (expected, it's a bare Mathlib anchor) and not independently confirmed
  against a vendored Mathlib this pass; carried over from pass 2 unverified.

## 3. Consumer wiring — B4_proof sorry (Proof.lean:98)
Real mismatch found. `B4 : Prop := ∀ P : FreyPackage, ¬ GaloisRep.IsIrreducible
(P.freyCurve.galoisRep P.p P.hppos)` (Proof.lean:53-59) — a bare irreducibility
statement about the Frey curve's mod-p representation. It does **not** mention a
totally real field, an auxiliary elliptic curve E/F, or any MB-D output object.
The doc's own B5/B6 sketch (Proof.lean:66-77 comments) confirms potential
modularity/MB-D lands several undrafted boss-theorems downstream (B5→B6a/b/c),
not at B4. So "the gap sits under B4_proof sorry" is true only in the trivial
sense that *all* undone work sits under that one sorry — describing B4 as "the
consumer" of MB-D overstates the wiring: no consumer type exists yet for MB-D to
be checked against. This is a statement-shape verification that **cannot be done
now** because the actual call site (B5/B6) isn't drafted, contrary to the framing
in §2b/§5Q4 that treats MB10 ergonomics as settled by MB-D's current phrasing.

## 4. Ready-now audit (R1-R5)
R1, R3, R5: confirmed ready, no blockers found. R2: ready only after R1, correctly
sequenced. R4 (weak-approx glue): downgrade confidence — Mathlib anchor unverified
this pass (see §2); doc should not list it as equal-confidence to R1/R3.

## 5. Grade consistency / blueprint hygiene fixes
Fixes 1-4 (chtopbestiary.tex:258/259/263/264) verified correct against current
tex — the missing `T` before `(L_v)`/`(L_w)` and the literal `∈`/missing subscript
are real and the proposed fixes are minimal/correct. Fix 5 (ch04overview.tex:71)
verified: MLT statement env (66-77) indeed never mentions MB; the `\uses` edge is
misattributed as drafted. Grades (S/M/L/XL) are internally consistent with the
Mathlib-anchor evidence found. No inflation detected.

## Bottom line
No fabricated citations. Two adversarial findings the doc undersells: (a) D6's
"induced from character" predicate has no Mathlib induction machinery to build
on — mint-from-scratch, not glue; (b) the B4_proof consumer-wiring claim is
premature — no drafted statement exists yet to check MB-D's shape against, so
panel sign-off on "MB10 ergonomics" (§5Q4) is not actually checkable today.
