# Odlyzko chapter — panel adjudication (hub-lsb1u.6.12)

Adjudicator: Fable, 2026-08-14. Seats: literature/numerics
(`panel/odlyzko-literature.md`), hypothesis-strength
(`panel/odlyzko-hypothesis.md`), dependency-honesty
(`panel/odlyzko-dependency.md`), all against
`cartography/odlyzko-reconciled.md`.

## Ruling: SOUND-WITH-REPAIRS — statements NOT yet frozen.

The chapter's analytics are fully verified; its *interface to the consumer*
is not yet formalizable-grade. Unlike Mazur, no statement freeze until the
repairs land.

**What IS certified now:**
- Every numerical claim, verified exactly against Poitou's Numdam scan:
  the p.17 table (9.305672 at n=18, GRH-free), closed-form (16)'s
  insufficiency at n=18 (8.24319 < 8.24838), the series machinery
  (19)–(26), the fixed-y monotonicity trick, the Minkowski asymptote, and
  U = 2^(2/3)·3^(3/2) = 8.248377821991616 with its 0.0197% / 12.796%
  margin arithmetic.
- Pass-2's "unreproducible 6.860404" hedge is REFUTED: the constant
  reproduces exactly from Poitou's printed inputs; the 6.8653 figure was an
  arithmetic slip. Hedge to be dropped (cosmetic repair).
- The axiom contract itself (verbatim repo `Odlyzko_statement`) and the
  M2 decomposition's Mathlib anchors (spot-verified to exist).

**Mandatory repairs before statement freeze:**
1. **R1 (blocking, first):** the consumer-side Fontaine upper bound — the
   ROLE of U — is stated nowhere in repo or blueprint; it is an external
   import with false precision. The interface-freeze node is upgraded to:
   state the consumer-side bound in Lean/blueprint WITH primary citation,
   including a coverage plan for the existing degree-15–17 gap
   (`le_fourteen_of_rootDiscrBound` stops at 14; nothing covers 15–17
   today; degree-19 shortcuts would widen, not fix, this).
2. **R2 (blocking):** decompose M3 (zero-counting / argument-principle)
   with the same rigor as M2's 24-node tree — it is currently an XL
   asserted without scrutiny, with hidden Borel–Carathéodory and
   zero-spacing edges found by the dependency seat.
3. **R3:** add the uncredited edges (Borel–Carathéodory into M8, digamma
   sourcing for M6) and credit Sphere-Packing-Lean as prior art on the
   dual-lattice Poisson nodes.
4. **R4 (policy):** port credit is 0/24 until AINTLIB passes the build
   gate (hub-lsb1u.6.10); the honest current expectation is ~1/12
   reconciled-map nodes (M2 only), not a chapter-wide shortcut; lean-pool
   restates rather than discharges the arbitrary-K target (Γℂ/2 delta,
   totally-complex scope) — though it matches the repo's actual consumer,
   which R1 will settle one way or the other.
5. **R5 (watch):** `mod_three`'s future instantiation (rep vs projective
   rep kernel field) is a soundness watch item — the axiom has no vacuity
   trap, but a wrong instantiation downstream would not trip one either.

Panel questions PQ1–PQ5 are answered across the three seat files; PQ5 is
amended per R1 (certify the consumer-side bound, not merely 8.25).
