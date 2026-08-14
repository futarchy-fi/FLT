# Galois-reps chapter — adversarial dependency/ledger audit (hub-lsb1u.10.4)

Seat: adversarial panel, dependency honesty + ledger audit. Input:
`cartography/galois-reps-reconciled.md` (G-schema, committed `b254d54`,
timestamp 2026-08-14T05:21:47-07:00) against the JL panel
(`cartography/panel/jl-adjudication.md` + `jl-dependency.md`, branch `panel/jl`,
committed `71ae014`, 05:49:44) and the CBC panel
(`cartography/panel/cbc-adjudication.md`, branch `panel/cbc`, committed
`be175cc`, 05:54:58), plus `cartography/r-eq-t-reconciled.md` (branch
`cartography/r-eq-t-reconciled`) for the A2/A3 boundary. Default skeptical.

## 1. Timing fault: the G-schema cannot respect either panel's findings

**The G-schema predates both panels it is being audited against.** Commit
order: galois-reps-reconciled (05:21) → JL panel (05:49) → CBC panel (05:55).
This is not a stale-but-still-correct situation to wave through — it means
every claim of "G-schema respects panel finding X" below is either (a) true
by accident of the underlying repo state, or (b) false and unrepaired.

- **JL H1 (automorphic induction orphaned, assigned to CBC/S4-S6):** grep of
  the G-schema for "induction" returns **zero hits**. The G-schema carries no
  AI content, so there is no double-claim against CBC's ownership — but this
  is negative evidence only, not confirmation the schema "respects" the
  reassignment. It was never in scope here to begin with (G1-G15 is Taylor/
  attachment content, not AI). **Verdict: no conflict, but also no explicit
  acknowledgment — the schema should gain a one-line note that AI is
  out-of-chapter per JL H1, or a future editor may re-import it thinking it's
  unclaimed.**
- **CBC PQ5 (mult-one descoping owner → "assigned to the Galois-reps
  chapter's G-schema at statement time"):** the G-schema has **no dedicated
  node for this ownership decision.** Mult-one appears only as a tag inside
  G9's status cell ("JL/mult-one/attachment content `[shared:.4][shared:G3]`"),
  inherited from the *pre-panel* JL reconciliation (§3, "per the JL
  reconciler's verified finding") — not as an owned decision responding to
  CBC's explicit PQ5 assignment, which didn't exist yet when this document
  was written. **PQ5 is currently unowned in practice, contrary to CBC's
  adjudication text**, which asserts the ownership landed here. It hasn't
  landed anywhere; it's a dangling forward-reference in one direction and a
  backward-reference to a superseded finding in the other.

## 2. `[shared:.4]` double-count accounting — consistent by bead, not by node

Direction 1 (G-schema → JL): G3 claims `[shared:.4]` (JL transfer, one
direction), G9/G10 claim `[shared:.4][shared:G3]`. Direction 2 (JL → G-schema):
`jl-dependency.md` Part 3 says "**.10 (Galois reps)** consumes nodes 5
[level/Hecke bridge] and 6 [ledger]" — bead-level, matches. But **no
document cross-references the other's node IDs**: JL's node 5/6 are never
mapped to G3 specifically (vs G9/G10) anywhere, and the G-schema's `[shared:
G3]` tag on G9/G10 has no counterpart tag in JL's inventory pointing back at
"G3". The accounting is **consistent at the bead-tag level, unverified at
the node level** — both documents independently assert symmetry without
either one naming the other's IDs. This is the same failure mode as §1: two
documents converging on the same conclusion by construction, not by mutual
check.

## 3. G15 vs A2/A3 — does not tile cleanly; likely gap, possible size mismatch

R=T reconciled: A2 = "Galois rep attached to Hecke eigensystem, ρ_π into
`T_𝔪`" (XL), A3 = "R → T surjection, `T_𝔪` complete local, universality" (L).
G15 = "Hecke-eigenvalue/**pseudo**representation bridge into R=T patching...
interface exists (`Automorphic.lean:85,93-94`; `Patching/REqualsT.lean`);
packaging literature-verify" (L-XL).

- **A3 (the surjection/universality argument itself) has no G-node at all.**
  Correctly so — that's R=T's own patching machinery, hub-lsb1u.11's job —
  but the G-schema never says this explicitly, so "G15 covers the A2/A3
  boundary" is not a claim either document actually makes; it's an
  assumption the prompt invites and the schema does nothing to block.
- **G15 vs A2 is a genus mismatch, not a match.** A2 wants a genuine
  representation `ρ_π` valued in `GL₂(T_𝔪)`; G15 is framed as a
  **pseudo**representation bridge (trace/det data only). Passing from a
  pseudo-representation to an actual representation into the Hecke algebra
  is a nontrivial extra step (residual absolute irreducibility ⇒ unique
  lift, Carayol/Nyssen-type argument) that neither G15 nor A3 names as a
  node. **This is a real seam, not just a labeling quibble** — if G15 ships
  as "packaging, L-XL" and is later treated as discharging A2, the
  pseudo-rep→rep lift is silently dropped.
- Sizing tension: A2 is graded XL standalone; G15 is graded L-XL but
  qualified "interface exists... packaging" (i.e., presented as lighter than
  a from-scratch XL). If G15 is meant to *be* A2's Lean-side content, the
  size grades should reconcile explicitly; they don't, and nothing flags the
  gap.

**Verdict: G15 and A2/A3 do NOT demonstrably tile the boundary. Gap on A3
(unclaimed by design, unstated in writing) and a genuine object-mismatch gap
on A2 (pseudo-rep vs rep) that the "packaging" framing papers over.**

## 4. Mult-one absorption node — CBC PQ5 has nowhere to land

Per §1: no dedicated node. G9's tag is the closest thing, but it (a) predates
CBC's PQ5 assignment and (b) is a status annotation on an existing sorry'd
Lean declaration, not an ownership record responding to a panel question.
**PQ5 remains functionally unowned** despite CBC's adjudication text
asserting otherwise.

## 5. G3 ledger contents — union of all panel findings to date

Reconciled §3.1 currently specifies only: JL transfer (one direction) +
Taylor 1989 (+ Carayol 1986 upstream). Per the four threads named in the
task, the mandatory ledger comment at G3-statement-time must ALSO carry:

1. **JL direction** (already specified): quaternionic eigensystem → Hilbert
   eigenform, credited once against hub-lsb1u.4, citing Taylor 1989 primary
   / Carayol 1986 upstream.
2. **Mult-one absorption** (CBC PQ5, unresolved per §4): if G3 is where
   mult-one descoping is decided, the ledger must say so explicitly and
   name what's being descoped (quaternionic mult-one, not just GL₂-side).
   Currently absent from the §3.1 spec entirely — a real omission, not
   pending future work.
3. **Coefficient bridge** (JL dependency Part 2 §2): the non-canonical
   ℂ ≅ ℚ̄_p comparison isomorphism that G3's own "A = ℚ_pᵃˡᵍ" statement form
   (panel Q2) depends on — flag that Frobenius-trace matching invariance
   under the choice of isomorphism is undocumented.
4. **Norm-factoring exclusion** (JL dependency node 5 / PQ6): the 1-dim
   norm-factoring-forms exclusion that P2 corrected (naive bijection false)
   belongs in G3's clause (W)/(I) ledger, not left implicit.
5. Should also note **AI is explicitly out-of-scope** here (JL H1 → CBC), to
   preempt re-import (see §1).

None of 2-5 are in the current §3.1 text; only item 1 is.

## 6. Grade consistency

- G-schema grades are internally consistent (Taylor-wins verdict, G7 ruled
  structurally inapplicable, G2 sorry LOW risk) and match CBC's
  re-adjudication of the `:100` sorry (LOW statement-risk stands, reassigned
  to CBC ownership, M-sized proof-load-bearing noted separately) — no
  conflict there.
- G15's "L-XL... packaging" grade is the one soft spot (§3): it undersells
  against A2's independent XL grade once the pseudo-rep/rep gap is counted.
- G5's MEDIUM-HIGH 1980s-boundary risk and G10/G11's "separate ledger class"
  framing are consistent with CBC's own post-1990 Rajan finding (same
  honesty pattern, different chapter) — no divergence.

---

Written 2026-08-14, working tree only, not committed.
