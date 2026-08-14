# Adversarial panel — LITERATURE + HYPOTHESIS STRENGTH — hub-lsb1u.10.4 (galois-reps-reconciled)

Reviewed: `origin/cartography/galois-reps-reconciled.md` vs `FLT/GaloisRepresentation/Automorphic.lean:60-184`.

## (1) Taylor 1989 load-bearing verdict
CONFIRMED, not merely plausible. Taylor, "On Galois representations associated to Hilbert
modular forms," Invent. Math. 98 (1989), 265–280
(https://link.springer.com/article/10.1007/BF01388853; EuDML keywords confirm: quaternion
algebras, totally real, even degree, congruences, pseudo-representations). Contemporaneous
independent route: Blasius–Rogawski, Bull. AMS 21 (1989), 65–69 — doc's G14 gap correctly
flags this as also missing from FLT.bib. Taylor's method is congruence/pseudo-rep, not purely
geometric — it *does* carry hidden analytic input (density of ordinary/definite forms, Hida-
style congruence to a form accessible by Carayol's odd-degree construction) but nothing
post-1990. Verdict AGREED, doc's §2.1 reasoning SOUND.

## (2) Three provability clauses vs literature basis
- (W)/(I): no issue, elementary from the Hecke-eigenform data itself.
- (Bℓ) tame rank-1 at S: standard Jacquet–Langlands local correspondence content, pre-1990,
  no objection.
- (Bp) flatness: CONFIRMED post-1990-only in the literature as stated. Saito, "Hilbert modular
  forms and p-adic Hodge theory," Compositio 145 (2009) 1081–1113
  (local-global compat at p via p-adic Hodge theory, explicitly extending Carayol's ℓ≠p work);
  Breuil, Bull. SMF 127 (1999) 459–472 (weight-2/BT via strongly divisible lattices). Both
  confirmed post-1990 by search. BUT the doc's own hedge — "pre-1990 derivation plausibly
  exists via Carayol's good-reduction models + Raynaud" — is in **direct tension with its own
  §2.1**: Carayol's integral models exist only via Shimura *curves*, which require a split
  infinite place, which the totally definite `D` here structurally lacks (that's precisely why
  G7 is ruled inapplicable). The hedge as written is not just unproven, it likely doesn't exist
  in the form claimed — Carayol has no integral-model machinery to hand off for this `D`. This
  STRENGTHENS the MEDIUM-HIGH grade toward HIGH: recommend striking the hedge sentence in §4.1,
  not softening the risk.

## (3) Good-primes-only attachment scope vs R=T patching's actual needs
UNVERIFIED — cannot check against the blueprint's real consumption because there isn't any yet.
`grep -n "IsAutomorphicOfLevel\|cyclic_base_change" FLT/Patching/REqualsT.lean
FLT/GaloisRepresentation/HardlyRamified/*.lean` → **zero matches**. G3 is not wired into the
patching/deformation argument anywhere in the tree. The doc's claim that (W)-only compatibility
suffices for the Galois-side of R=T is an assertion about a future consumer, not something the
repo lets you check today. Flag as UNVERIFIED, not AGREED — the reconciliation doc states this
too confidently for something with no consumer yet.

## (4) G3 nonvacuity/G3 axiom instantiation
No witness anywhere. `grep -rn "IsAutomorphicOfLevel"` across the whole repo returns exactly two
lines, both inside `Automorphic.lean` itself (the def and the `cyclic_base_change` statement) —
no `example`, no instance, no lemma exhibiting a single `(D, S, π)` satisfying the predicate.
The axiom-to-be-stated (G3) therefore has **no non-vacuity witness in-repo**; its truth for any
concrete `ρ` (e.g. the Frey curve's mod-3/mod-5 representations that the whole campaign chases)
is asserted nowhere in Lean. This is a genuine gap the doc's ready-now list doesn't mention.
Recommend adding it as a panel action item, not folding it silently into G3/G12.

## (5) Answers to the 7 PQs (lit + hypothesis-strength lens)
Q1 (1980s test for Bp): NO — post-1990 only (Saito/Breuil); doc's own hedge is unsound per (2).
   G5 should be booked as separate post-1990 assumption now.
Q2 (G3 statement form): state for `A = ℚ_pᵃˡᵍ` — matches `cyclic_base_change`'s existing form,
   least new surface area; deriving general `A` is extra unstated work, defer.
Q3 (supersede blueprint G13): yes, but only after G3–G5 stated — doc's own G13 status is "likely
   superseded," don't pre-commit.
Q4 (Bℓ/Bp into axiom now vs later): keep as consumer hypotheses until R=T's ⇐ direction is
   wired (see (3) — no consumer exists yet, no reason to bake in now).
Q5 (discriminant-1/even-degree rigidity): accept as-is; no evidence in repo of near-term need
   for auxiliary ramified D.
Q6 (shared-content ledger ratify): ratify — JL-to-.4 / attachment-to-.10 double-count rule is
   consistent with the JL reconciliation doc's absorber list, no objection found.
Q7 (G10/G11 ledger class — book KW/BLGGT now): book now — same post-1990 mismatch logic as Q1;
   leaving it inside sorried absorbers risks the same silent-pre-1990-assumption failure mode
   this whole review just caught in §4.1.

## Verdict tags
REFUTED: none of the doc's core claims are refuted.
UNVERIFIED (weakened by this review): §4.1's pre-1990 Carayol+Raynaud hedge for flatness
(internally inconsistent, recommend deletion); §3-item-3/PQ3-adjacent claim that good-primes
compatibility suffices for R=T (no consumer exists to check against).
NEW GAP (not in doc): G3 has no non-vacuity witness anywhere in the Lean tree.
