# R=T chapter — hypothesis-strength / posture-integrity attack (hub-lsb1u.11.4)

Seat: adversarial panel, hypothesis strength + posture integrity. Against
`cartography/r-eq-t-reconciled.md` (2026-08-14), ground truth
`FLT/Patching/REqualsT.lean`, `FLT/GaloisRepresentation/HardlyRamified/{Lift,Family}.lean`,
and sibling seat `cartography/panel/ret-dependency.md`.

## 1. Posture pricing — "monitoring + gap-filling" is a bet, not a safety property

The reconciled map lists Watch PRs (§3) for A7 (#1089), A11 (#1071), A12 (#1083/#761),
A13 (#761), A16 (#1110/#1105) — but **A2, A3, A9, A10, A15 have zero listed watch PR
and zero contingency owner anywhere in the cartography tree** (grepped for
"fallback"/"owner"/"contingency"/"stall" across `cartography/`: no hits, any chapter).
If upstream stalls or pivots on the XL analytic block (A9 cyclic base change, A10 JL —
`ret-dependency.md` §2 independently confirms these are "genuinely irreducible XL, no
infrastructure exists to decompose against"), the posture has **no detection mechanism**:
nothing in §3's sync cadence triggers on their absence, only on PRs that don't exist yet.
Same gap for A2/A3 (Hecke→Galois attachment, R→T construction) — `ret-dependency.md` §1
already shows A3 has zero positive citation despite being sized a tier below A2. Priced
honestly: the bet is "upstream lands A1/A7/A11/A16's inputs within a fundable horizon";
the uninsured tail is the analytic block plus A2/A3, worth roughly half the remaining
XL-graded mass, with no fallback plan drafted for any of it.

## 2. A16→REqualsT.lean:76 shape-compose verdict: MISMATCH, not a clean plug-in

Line 76 confirmed: `H : .some (Module.depth Λ Λ) = ringKrullDim Rₒₒ` — an equation
between the **depth of the coefficient ring Λ** and the **Krull dimension of R∞**
(`Rₒₒ`), consumed at the `ker_RtoT_le_nilradical` payoff (line 86, confirmed). This
hypothesis quantifies over zero cohomology, zero Selmer groups, zero Galois modules.
The PT panel's FROZEN axiom (`f2bdc79`, order-formula form) is
`#H¹_L/#H¹_{L^⊥} = (#H⁰(K,M)/#H⁰(K,M*))·Π_v(#L_v/#H⁰(K_v,M))` — a Selmer-group
cardinality formula for an arbitrary Galois module M. **There is no direct type-level
plug**: getting from the order-formula to "depth Λ = dim R∞" requires the full
Taylor–Wiles numerical-criterion chain (tangent-space = H¹_Selmer via A5, local
condition dimensions via A6, presentation/generator-relation count via A7) — A16 is
one input among three, not the consumer. The reconciled map's own §2.2 dependency
edge (`A7 ← A5, A6, A16`) already says this, but §6-Q5 and the merged-inventory row
still describe A16 as "spent exactly at" the :76 hypothesis, collapsing A7's chain
into A16 alone. `ret-dependency.md` independently catches the same fault from the
PT side (PT-node-12/global-Euler-characteristic, flagged as least-audited under an
open R1 repair ticket, never cited against A16). **Verdict: catch this now** — reword
every "A16 discharges REqualsT.lean:76" claim to "A16 is a necessary but insufficient
input to A7, which discharges :76 via A5+A6+A16," and inherit PT's R1/node-12 caveat.

## 3. Shadow-sorry fidelity: Lift.lean:48 / Family.lean:68 have no pinned blueprint target

Confirmed: `HardlyRamified/Lift.lean:48` (theorem `lifts`) and
`HardlyRamified/Family.lean:68` (theorem `mem_isCompatible`) are exactly where the
sorries sit. But `ch04overview.tex`'s "Compatible families, and reduction at 3"
section (the only prose these could shadow) has **no `\label`, no formal theorem
environment, no `\notready` marker** — it is unstructured prose ("we now use
Khare–Wintenberger to lift ρ... put it into an ℓ-adic family using the Brauer's
theorem trick"), unlike `modularity_lifting_theorem` at :66-77 which *is* pinned.
Two concrete drift points against that prose: (a) `Lift.lean`'s conclusion asserts
only `IsHardlyRamified ∧ baseChange = ρ` — no modularity or potential-modularity
predicate anywhere in the statement, though the prose frames this step as producing
"a potentially modular ℓ-adic Galois representation" (plausibly deliberate
factoring — modularity supplied later via family-compatibility — but nothing in
either file's docstring says so); (b) no cross-reference from either file back to
ch04overview exists to confirm the factoring is intentional rather than drifted.
**Fidelity cannot be verified, only assumed** — the reconciled map's "Frey-side
shadow" framing overstates traceability by citing an anchor (weakest-form :66-77)
these two sorries are not actually shadows of.

## 4. Vacuity/nonempty obligations (A1, unstated)

Not assessable yet — A1 has no Lean statement to check for vacuous hypotheses. Flag
for when A1 lands: the four S-good bullets plus absolute-irreducibility-over-F(ζ_ℓ)
must be checked non-vacuous (i.e., an S-good lift exists at all) before the theorem
is worth anything; `narrowSLiftFunctor`'s representability sorries (A4) currently
block even checking the functor is nonempty on interesting inputs.

## 5. Six PQs — skeptical answers

1. **Coverage basis**: adopt effort (~25–30%) as headline — correct, but log that
   breadth (~60%) is not a floor: two of its "declared" rows (A16 abstract hypothesis,
   HardlyRamified sorries) are themselves shown above to be under-specified interfaces,
   not settled scaffolding.
2. **PR #761 rescue**: offer rescue now — 7 months stale (re-confirmed 2026-08-14,
   `updatedAt` unchanged) is past any reasonable "wait one more cycle" threshold; do
   not seek guidance passively while it decays further.
3. **A1 collision policy**: confirm watch-only, but demote confidence — "single
   best-leverage item" is doing a lot of work for a theorem with no pinned Lean
   target for its consumption layer (§3 above); best-leverage should be paired with
   an explicit trigger, not left implicit.
4. **Axiomatization map**: unresolved and should stay a standing question, not a
   one-time PQ — A9/A10 (analytic block) have no signal either way; treat as
   "unknown, high consequence" rather than folding into the axiomatized bucket.
5. **hub-lsb1u.7 handoff**: **do not confirm as stated** — see §2. The honest
   handoff is A16 → A7 (via A5/A6), not A16 → :76 directly, and it inherits PT's
   own R1 (node-12) and node-1 regrade blockers, so it is not yet a clean freeze
   on either side.
6. **A4/A14 ready-now**: approve both — independently re-verified 2026-08-14
   (grep against live `gh pr list`, zero hits on the relevant files), consistent
   with `ret-dependency.md`'s §4 re-verification.

File: `/Users/kas/FLT/cartography/panel/ret-hypothesis.md` (working tree only, not committed).
