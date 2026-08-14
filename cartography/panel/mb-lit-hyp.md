# Panel seat: LITERATURE + HYPOTHESIS STRENGTH — MB-D (bead hub-lsb1u.8.4)

Source verified: Snowden, "Potential Modularity and Applications" (Conrad seminar L26),
http://virtualmath1.stanford.edu/~conrad/modseminar/pdf/L26.pdf (fetched, OCR'd via
pdftotext). Cross-checked against `FLT/GaloisRepresentation/HardlyRamified/Defs.lean`
and `blueprint/src/chapter/ch04overview.tex:80-98`.

**(1) Curve-free interface — CONFIRMED, stronger than MB-D states.** Thm 14's proof
consumes **Proposition 10** (Snowden), which is stated purely in Galois-representation
terms — a compatible system `{ρ_w}` with `ρ_v1 ≅ ρ1`, `ρ_v2 ≅ ρ2`, ordinary-crystalline
at all places over p/ℓ, F′/F linearly disjoint — no curve appears in the statement, only
in Prop 10's *proof* (moduli space `Y` of elliptic curves with prescribed p- and
ℓ-torsion). MB-D as reconciled phrases the interface via an elliptic curve `E` (matching
ch04overview.tex:93-98's own sketch, not Prop 10's abstract form) — faithful to the
blueprint's chosen sketch, but a strictly narrower, curve-committed statement than the
literature's cleanest curve-free packaging (Prop 10). Recommend MB-D cite Prop 10, not
just the sketch, as the true minimal-data interface.

**(2) "E[p] induced from a character" — condition identified, MB-D underspecified.**
This is Snowden's Prop 13: `σ = Ind_E^F(ψ)`, where **E is a freely-chosen imaginary
quadratic extension of F** (not K^avoid, not a field tied to ρ̄'s projective image), split
at all places of F above the auxiliary prime, with ψ chosen so `Ind ψ` is ordinary
crystalline above that prime and irreducible mod ζ_(aux prime). MB-D's listed condition
("E[p] induced from a character") omits the existential quantification of E itself — the
D6 predicate must be `∃ (E : imaginary quadratic ext of F), ∃ ψ : Character G_E, ...`,
not a bare property of ρ̄|_{G_F}. Minting D6 without this field-existence clause would
under-state the literature's actual condition.

**(3) Good-ordinary-above-ℓ-and-p — sufficient for ch04overview.tex:93-98, imprecise
wording risk.** Snowden Prop 10: "ordinary crystalline at **all** places over p (resp.
ℓ)" — matches the consumer's needs (MLT hypothesis + JL/converse-theorem step). MB-D's
phrasing "good ordinary above ℓ, p" should be tightened to "at all places of F above ℓ
and all places above p" to avoid a single-place misreading — a real drafting risk, not a
strength gap.

**(4) Vacuity vs. unprovability — genuine risk found, not in the reconciled doc.**
`IsHardlyRamified` (`HardlyRamified/Defs.lean:48,96-107`) allows residue field `k` to be
**any finite field of characteristic ℓ**, and `R` a general profinite local ring over
`ℤ_ℓ` — not the prime field `F_ℓ`. Snowden's Prop 10/Thm 14 proof as given needs `ρ1`
valued in the **prime field**; Remark 11 explicitly flags this and prescribes the fix:
replace "elliptic curve E" with a **GL2(K)-type abelian variety** (Rapoport moduli). If
MB-D is minted literally as "elliptic curve E/F with E[ℓ] ≅ ρ̄," it may be unprovable
for hardly-ramified ρ̄ with non-prime-field residue field — not vacuous, but requires the
abelian-variety generalization MB-D currently elides. Disjointness/linear-disjointness
and irreducibility/oddness demands are not overtight (Snowden shows F′/F disjointness is
free — a feature, always achievable).

## 6 panel questions, from this lens

1. **Altitude sign-off**: Accept MB-D conditionally — only if restated via Prop 10's
   curve-free compatible-system form, or if the elliptic-curve form is paired with a
   proof obligation that ρ̄'s residue field reduces to F_ℓ (else must generalize to
   GL2(K)-type abelian varieties per Remark 11). As literally drafted (elliptic curve,
   no residue-field caveat), do not ratify yet.
2. **D6 minting**: This campaign should mint both predicates, but the induced-character
   one must existentially quantify the imaginary quadratic field E (see §2) — upstream
   FLT has no reason to have this shape yet since no curve-free MB statement exists there.
3. **`knownin1980s` vs named module**: Named module — MB-D's caveats (§1, §4) are
   substantive enough that phase-2 auditors need it visible, not folded into a tactic.
4. **Auxiliary prime p**: Existentially quantify inside the node — Snowden's Prop 13/14
   treat it as "any prime ≠ p" chosen for convenience, not consumer-supplied; forcing it
   as an input over-constrains callers.
5. **Upstream hygiene**: Batch with first blueprint contribution — the 5 typo fixes are
   independent of the §1/§4 substantive gaps found here, which should be resolved first
   so the upstream PR carries a correct MB-D citation.
6. **Shimura coupling**: No opinion from this lens (curve/geometry question, not
   literature-fidelity); defer to geometry seat.

## REFUTED vs UNVERIFIED

- REFUTED: reconciled doc's implicit assumption that MB-D's elliptic-curve phrasing is
  a safe, literature-faithful narrowing of Prop 10 — it is faithful to the *sketch* but
  risks unprovability against `IsHardlyRamified`'s general residue field (§4).
- REFUTED: "no induced-from-character predicate exists in the literature" framing as if
  the condition were free-floating — it is Snowden's Prop 13 `Ind_E^F(ψ)` with E an
  existentially-chosen imaginary quadratic field, not a predicate on ρ̄ alone (§2).
- UNVERIFIED: whether `WeierstrassCurve.galoisRep`'s eventual construction (D5) can even
  target non-prime-field residue fields without first generalizing to abelian varieties —
  not checked this pass, flagged for whoever picks up R1/R2.
