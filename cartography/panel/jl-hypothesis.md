# JL chapter panel — HYPOTHESIS STRENGTH / ABSORPTION-BOUNDARY INTEGRITY (adversarial seat)

Bead hub-lsb1u.4.4. Route A (absorption) is ratified and NOT relitigated here; this
attacks whether the boundary the absorbing axioms draw actually covers all JL content the
route needs. Ground truth re-verified 2026-08-14 against `/Users/kas/FLT` (repo HEAD) and
`origin/cartography/{jl-reconciled,galois-reps-reconciled}`.

## 1. Enumeration of absorbed JL content vs. what's needed

| Absorbing site | Status in Lean | JL content it actually carries |
|---|---|---|
| `cyclic_base_change` (`Automorphic.lean:127-184`, `sorry` at `:184`) | statement exists, unproved | Per jl-reconciled: "JL-both-directions + mult-one + image classification" — **but the statement text (`:109-126` docstring, `:127-178` binders) contains zero mention of JL, multiplicity one, or image classification.** The claimed absorbed content is asserted by the reconciliation record, not evidenced in the Lean source itself. No ledger comment exists. |
| G3 attachment axiom (galois-reps-reconciled) | **not yet stated anywhere in the repo** | Claimed to absorb "JL transfer, one direction" + Taylor 1989 attachment. Cannot be checked against source because it doesn't exist yet — its vacuity/coverage is unverifiable until stated. |
| Automorphic-induction axiom (GL₁→GL₂, named in `chtopbestiary.tex:212-213`, `README.md`) | **not stated; not even a placeholder or `sorry`** | No node in either reconciled map assigns this a home. Neither `cyclic_base_change` nor G3 mentions automorphic induction. |

**Coverage verdict: NOT proven closed.** Automorphic induction from GL₁(K) to GL₂(F) is
named by the blueprint (`chtopbestiary.tex:212-213`) and by `Assumptions/README.md` as
required machinery alongside JL, cyclic base change, and image classification — but it
appears in neither `Automorphic.lean` nor the G-schema's 15-node inventory as an owned
absorption site. This is an orphan: JL-adjacent content named by the blueprint with no
current or planned Lean-side carrier. (It may be intended to live inside `cyclic_base_change`
too, but nothing says so — the hidden-content ledger rider, if honored, would force this to
be made explicit and it currently isn't.)

## 2. U1(S,Q) — Taylor-Wiles augmented levels: ORPHANED, not resolved

`GaloisRep.IsAutomorphicOfLevel` (`Automorphic.lean:67-94`) builds its `HeckeAlgebra` via
`⟨Fact.out, S, ∅, 1, by simp, hp⟩` (`:85`, `:94`) — **the TW-prime set `Q` is hardcoded to
`∅`**. `U₁Data.Q` ("the set of taylor wiles primes", `Concrete.lean:380`) is real
infrastructure, but `IsAutomorphicOfLevel`, and hence `cyclic_base_change` (which is stated
purely in terms of `IsAutomorphicOfLevel`), only ever quantifies over `Q = ∅`.

Grep confirms `cyclic_base_change` and `IsAutomorphicOfLevel` have **zero consumers anywhere
else in the repo**, including `FLT/Patching/REqualsT.lean` (zero hits for either name). So
today this is latent rather than actively broken — but pass 2's own flagged risk (R2, jl
pass-2 map: *"the route hardwires ... `U_1(S,Q)` levels [including TW `Q`-levels] ... A
JL/mult-one statement matching only `U_1(S)` would silently under-serve the patching
argument"*) is **unresolved in the source**, not "won" by pass 2 in any substantive sense.
`jl-reconciled.md`'s "pass 2 wins on ... U1(S,Q) Taylor–Wiles level scope" credits pass 2 for
raising the risk, not for closing it — no follow-up shows the risk discharged. When
hub-lsb1u.11 (R=T patching) actually needs base-change compatibility at `U₁(S,Q)`, neither
`cyclic_base_change` nor any stated G3/G9/G10 axiom supplies it. **This is the single
clearest orphan in the current boundary.**

## 3. Vacuity check

- `cyclic_base_change` is an unconditional `sorry`-axiom biconditional, universally
  quantified over `ρ` satisfying (irreducibility, det=cyclo, flatness, unramified-outside-S,
  tame-at-S). It is not vacuous by construction (these hypotheses are jointly satisfiable by
  real Galois representations), but its **usefulness** depends on a nonempty-instance
  obligation that lives *outside* this axiom: some concrete `ρ` must independently be shown
  to satisfy `IsAutomorphicOfLevel` (the base case, via Langlands–Tunnell for the mod-3
  representation). That obligation is currently undischarged in this file and — per the grep
  above — `cyclic_base_change` is not yet wired to anything that would discharge it.
  **Named obligation:** the mod-3 (or 3-adic) Frey-curve representation must be proved
  automorphic of some level via the Langlands–Tunnell route before `cyclic_base_change` does
  any work; track this against the langlands-tunnell cartography branch, not this chapter.
- G3 (attachment axiom): not yet stated, so its vacuity is presently unverifiable. When
  stated, its nonempty-instance obligation is: some quaternionic eigenform `π` (i.e. a
  nonzero `HeckeAlgebra →ₐ A`) must be shown to exist and have a Galois representation
  attached — flag this explicitly in G3's ledger comment when it is written.
- `IsAutomorphicOfLevel` itself is an `∃`-Prop (`:80-94`); it is satisfiable vacuously in the
  logical sense only if no `D`/`π` ever exists for given `(F,p,ρ,S)` — that's exactly the
  content the axioms assert nonvacuously, so the obligation above is the real check, not a
  separate one.

## 4. PQ2–PQ7 (panel questions from `jl-reconciled.md` §"Panel questions")

- **PQ2 (ledger/ownership).** Scheme is sound on paper (credit JL once to .4, attachment
  once to .10, `[shared:...]` tags) but **not yet instantiated**: `cyclic_base_change` has no
  ledger comment today (its `:109-126` docstring is pure math, no absorption inventory). The
  binding rider from the JL adjudication is currently unmet in the working tree.
- **PQ3 (U1(S,Q) scope).** See §2: unresolved, orphaned. Recommend blocking G9's pinning (and
  any R=T wiring) until either (a) `cyclic_base_change`/`IsAutomorphicOfLevel` is generalized
  to arbitrary `Q`, or (b) a written argument shows `Q = ∅` suffices and TW-level base change
  is never actually needed (unlikely given standard R=T patching architecture, but the panel
  should not assume the standard architecture is what this repo will use without checking
  `Patching/System.lean`/`REqualsT.lean`'s actual level bookkeeping).
- **PQ4 (mult-one as separate bead).** Both passes agree: absorb into `cyclic_base_change`,
  do not separate. No objection, contingent on the ledger comment actually naming it
  (currently absent).
- **PQ5 (Shimizu vs trace formula).** Moot under Route A; default to Shimizu as the
  deprecation target per the reconciler. No boundary impact today.
- **PQ6 (norm-factoring exclusion).** Real content gap: pass 2's R3 shows a naive
  "bijection of all eigensystems" is false (1-dim norm-factoring forms in `S^D` have no JL
  partner). `IsAutomorphicOfLevel`'s `∃ π` form sidesteps this for the attachment direction
  (existence, not bijection) but any future ⟸-direction or uniqueness use inside `.5`'s
  base-change image argument will need the exclusion stated explicitly. Not yet in any
  ledger.
- **PQ7 (coefficient bridge ℂ↔ℚ̄_p).** Real, unavoidable (R4), correctly flagged as missing
  from pass 1. Must appear in G3/G9 ledger when written; currently absent (G3 doesn't exist,
  G9 has no ledger).

## Bottom line

Route A's absorption is architecturally sound, but the boundary as *currently instantiated
in Lean* is not proven to cover all named JL content: automorphic induction has no assigned
carrier, the mandatory hidden-content ledgers don't exist yet in `Automorphic.lean`, and most
concretely, `cyclic_base_change`/`IsAutomorphicOfLevel` hardcode `Q = ∅` and so do not range
over the Taylor–Wiles-augmented `U₁(S,Q)` levels that R=T patching is expected to need — a
risk pass 2 raised and no source-level evidence has closed. Recommend the panel treat U1(S,Q)
coverage as a blocking pre-condition on pinning G9, not a background risk note.
