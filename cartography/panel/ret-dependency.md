# R=T chapter — dependency-honesty attack (hub-lsb1u.11.4)

Seat: adversarial panel, dependency honesty. Against
`cartography/r-eq-t-reconciled.md` (2026-08-14) and
`cartography/panel/greps-adjudication.md` (G17 minting, same date).

## 1. Boundary re-tiling (G15/A2 vs G17)

A2's own reconciled description — "Galois rep attached to Hecke
eigensystem, ρ_π into T_𝔪" — is a compound claim bundling (a) pseudo-rep
construction from the eigensystem, (b) the Carayol/Nyssen lifting step,
and (c) upgrading to a T_𝔪-*valued* (not just field-valued) rep. G17
only minted (b). **A2 does NOT shrink as filed** — it stays XL, single
row, no G17 cross-reference added anywhere in §2.2 or §5 — but its true
remaining content after G17 is (a)+(c), i.e. it is now mis-scoped as a
monolith. **Unclaimed residue at the boundary, undetected by the
reconciled map: the T_𝔪-valued globalization (c)** — lifting per-
eigensystem into a rep valued in the *whole localized Hecke algebra*,
not the residue field, is neither G15's pseudo-rep bridge, G17's
lifting, nor A3's stated scope ("R→T surjection, T_𝔪 complete local,
universality" — surjectivity/universality, not construction). Also
unclaimed: T_𝔪's maximal-ideal localization/completion *procedure
itself* is asserted (A3, size L) but the merged inventory's own
evidence line ("absent... IsAutomorphicOfLevel compares, never
constructs") shows A3 is exactly as empty as A2 — the map treats it as
scoped/sized without a single positive citation. Verdict: re-tiling is
incomplete — file G17 as an explicit A2 dependency and split A2 into
(a)+(c), or the "does A2 shrink" question stays permanently
unanswerable.

## 2. XL decomposability scoping

- **A2 (Galois-reps-into-Hecke):** decomposable, now that G17 carves
  out (b). (a) pseudo-rep existence and (c) T_𝔪-globalization are
  plausible independent S/M-chain candidates once G15's bridge is
  cited explicitly.
- **A6 (local flat deformation rings):** decomposable — the weakest-
  sufficient-statement's own four S-good bullets (§2.3) already
  partition it by condition (flat at v|ℓ, trace-2 tame inertia at S);
  G17 panel's item 1 (Bp flatness reclass HIGH, Saito 2009/Breuil 1999)
  further confirms this is condition-by-condition, citation-by-
  citation work, not one indivisible proof.
- **A7 (TW-patching instantiation):** decomposable — reconciled §2.2's
  own edge list (A7 ← A5, A6, A16) plus CBC's D-9 finding (Q=∅
  hardcode, "patching-side sufficiency proven by whoever pins") splits
  it into TW-prime selection, level-Qₙ system construction, and the
  depth=dim discharge as separable sub-tasks.
- **Analytic block (A9 cyclic base change + A10 JL):** genuinely
  irreducible XL. No infrastructure exists to decompose against
  (DivisionAlgebra/ has adelic scaffolding only, zero automorphic-
  representation-theory Lean content); CBC's own adjudication resizes
  the tower step *upward* (Rajan 2002/Clozel–Rajan 2021 now load-
  bearing, contradicting a "just iterate" decomposition). Scoping
  verdict for the decomposition mandate: **exclude the analytic block
  from Kelvin's last-wall S/M-decomposition plan** — it needs a
  dedicated infra-first investment, not a work-breakdown.

## 3. Cross-obligation mirror audit

- **PT's A16:** mirrored (§2.2, §5, §6-Q5) — but the mirror is shallow.
  PT adjudication's R1 flags node 12 (global Euler characteristic) as
  "the least-audited entry directly under the payoff theorem," and
  deletes node 11′ as circular. Neither caveat appears against A16 in
  the reconciled map — A16 is spent as a monolithic KnownIn1980s input
  with no acknowledgment that its actual PT-side load-bearing node is
  under an open repair ticket. **Gap: mirror A16 → PT-node-12/R1, not
  A16 → "PT/Selmer" in the abstract.**
- **CBC's D-9 (Q=∅ hardcode):** NOT mirrored. D-9 explicitly conditions
  the Q=∅ specialization's acceptability on "patching-side sufficiency
  proven by whoever pins" — that's a direct obligation on A7/A8. The
  reconciled map's A7 row ("scaffold only... no existence/adequacy
  theorem") never cites D-9 or the sufficiency proof-obligation it
  creates. This is a live, unmirrored cross-chapter debt.
- **Galois-reps checkpoint (G17 item 5, good-primes-only sufficiency):**
  partially mirrored — reconciled map's A7/A8 rows functionally are the
  "patching consumer" the checkpoint says to re-validate against, but
  no explicit trigger/pointer back to the G-chapter checkpoint exists
  in §3 Watch PRs or §6 panel questions. Same failure mode as D-9: real
  dependency, absent citation.

Net: 1 of 3 cross-chapter obligations checked (A16) is mirrored but
under-specified; 2 of 3 (D-9, G17-checkpoint) are unmirrored entirely.

## 4. Gap-fill freshness (re-verified 2026-08-14 live)

`gh pr view 761`: still OPEN, non-draft, `updatedAt` 2026-01-12 —
**still stale, ~7 months, unchanged from the reconciled map's finding.**
Re-ran `gh pr list --state open` (31 PRs) filtered against
`Deformations/Representable.lean`, `Deformations/LiftFunctor.lean`,
`Patching/Utils/CompactHausdorffRings.lean`: **zero hits** — A4 and A14
remain genuinely unclaimed today, confirming the map's "ready-now"
verdict still holds.

## 5. Grade consistency

Consistent within its own terms, but A2/A3's shared "absent, XL/L"
grading is unearned given §1's finding that A3 has the same zero-
citation evidentiary base as A2 while being sized a full tier lower —
grade the two together or justify the split.

File: `/Users/kas/FLT/cartography/panel/ret-dependency.md` (working
tree only; not committed).
