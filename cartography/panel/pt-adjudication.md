# Poitou–Tate chapter — panel adjudication (hub-lsb1u.7.4)

Adjudicator: Fable, 2026-08-14. Seats: literature (`panel/pt-literature.md`),
hypothesis-strength (`panel/pt-hypothesis.md`), dependency-honesty
(`panel/pt-dependency.md`), against `cartography/pt-reconciled.md`.

## Ruling: SOUND-WITH-REPAIRS — PARTIAL FREEZE granted.

**FROZEN for P2 drafting now** (the campaign's second statement freeze):
- The definition layer: `H¹_nr`, `M* = Hom(M, μ)`, the local pairing as a
  given map, `G_{K,S}` globals + localization, Selmer `H¹_L` with `L^⊥` —
  verified by the dependency seat to sit on real, sorry-free FLT
  infrastructure (`ContCohomology`, `CupProduct.lean` — 584 lines, zero
  sorry, Leibniz rule proved).
- The chapter axiom, in ORDER-FORMULA FORM directly:
  #H¹_L/#H¹_{L^⊥} = (#H⁰(K,M)/#H⁰(K,M*)) · Π_v (#L_v/#H⁰(K_v,M)),
  attributed to **NSW 8.7.9 / DDT Thm 2.18** (verified verbatim), with
  Wiles Prop 1.6 demoted to originating special case (K=ℚ, p-power order,
  archimedean split — cannot be opened to the displayed form) and Milne
  I.4.20 added as the finitely-generated generalization Wiles himself
  cites.

**Node 11′ (middle-exactness) is DELETED from the package**, resolving the
circularity both seats found independently: it cannot be typed without the
Pontryagin-duality-of-non-compact-groups machinery the descope drops
(smuggled back via node 10's restricted products). With the axiom in
order-formula form, 11′ is never needed; the package size claim is
corrected accordingly. The nine-term sequence and Sha-duality remain in
the deferred ledger (deferral never deletion) for whoever eventually
proves the axiom.

**Blocking repairs before FULL freeze (proof-package scope):**
1. **R1:** node 12 (global Euler characteristic) — the least-audited entry
   directly under the payoff theorem — gets a full dependency trace with
   MLT-grade citation discipline before it is trusted at its grade.
2. **R2:** node 1 (continuous/profinite cohomology) re-graded upward:
   external evidence (Livingston ITP2023) says Mathlib proper lacks the
   profinite comparison; FLT's bespoke layer is load-bearing and its
   maintenance cost belongs in the grade.

**Watch items:** the Mazur-chapter D6a descent could reopen Sha-adjacent
needs (couples to hub-lsb1u.2 — cross-chapter watch, both ledgers annotated);
the non-minimal-case "PT-free via Skinner–Wiles" claim is MEDIUM confidence
resting on a `\notready` sketch — revisit when the MLT blueprint node
matures.

CFT boundary: CONFIRMED under adversarial attack — exactly two imports
(local inv_v, global sum-inv=0), genuinely aligned with the CFT chapter's
reconciled cut.
