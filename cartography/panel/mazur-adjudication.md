# Mazur chapter — panel adjudication (hub-lsb1u.2)

Adjudicator: Fable (campaign orchestrator), 2026-08-14.
Inputs: reconciled map (`cartography/mazur-reconciled.md`), three adversarial
seats — literature-fidelity (`panel/mazur-literature.md`, Sonnet+web),
hypothesis-strength (Sol, verdict on bead), dependency-honesty
(`panel/mazur-dependency.md`, Sol).

## Ruling

**W is FROZEN as the chapter's target statement.**

> For every prime ℓ ≥ 5, no elliptic curve over ℚ contains
> (ℤ/2)² × ℤ/ℓ in its Mordell–Weil group; the full-2-torsion hypothesis is
> load-bearing only for ℓ = 5, 7 — for ℓ ≥ 11 the statement "no rational
> point of order ℓ" suffices.

Grounds: derived twice independently, ruled SUFFICIENT by the
hypothesis-strength seat against the actual blueprint invocation sites, and
its bibliography survived the literature seat. P2 drafting of W may begin,
subject to the trap list below.

**The map is ACCEPTED WITH REPAIRS** (map, not mathematics, was the panel's
target; two seats said sound-with-repairs, one said dishonest-with-repairs on
the dependency graph — the repairs are compatible and adopted in full):

1. **Strike C5.** ℓ = 17, 19 are NOT classical (X₁(17)/X₁(19) have genus
   5/7); they are settled only by Mazur's general theorem. Part C shrinks to
   the genuinely classical cases; ℓ = 17, 19 fold into the D-core.
2. **Adopt all hidden edges from the dependency seat.** A5 → ch03/local
   finite-flat/Tate/dual-isogeny; D1–D5 → moduli/Néron/Jacobian/étale-Hecke;
   D6a/b → class field theory, Poitou–Tate, Selmer machinery; B2 →
   number-field descent. Consequence: the Mazur chapter is MORE coupled to
   the CFT and Poitou–Tate chapters than either pass recorded; the graph-sync
   must carry these cross-chapter edges.
3. **D8 endgame stays OPEN pending page-level verification** (PQ1: both the
   λ=1 variant and the Néron/small-fibre formulation need checking against
   Mazur 1977 at page level). Spike bead created.
4. **D6 fork (Eisenstein-quotient vs winding-quotient) is NOT decided.**
   Both routes are XL+; the winding route is not "simple" (its
   Kolyvagin–Logachev/Gross–Zagier stack is real, though correctly scoped).
   Adopt the dependency seat's recommendation: run an Eisenstein paper-audit
   spike before committing either. Spike bead created.

**Lean-drafting trap list (binding on P2 for this chapter):** `Set.ncard`'s
junk value on infinite sets must not silently weaken statements
("≤ 16 or infinite" pattern); cusp-set formulations must be nonempty by
construction; A4/B5/D8 hypotheses are under-specified in the map and must be
tightened at drafting time, with the panel's notes in hand.

**Ready-now correction:** the five "ready-now" nodes are
**statement-ready, not proof-ready** (dependency seat: 0/5 proof-ready).
Under our autoformalization-first flow this still makes them the right next
P2 targets — as `sorry`-bodied statements — but nobody should read
"ready-now" as provable-now. A5 (re-wiring `FreyPackage.mazur` through the
real statement) additionally waits until W itself is stated in Lean.

**PQ4 / exponent re-basing** stays with Kelvin (hub-lsb1u.12), now
literature-verified feasible up to p ≥ 17 (arXiv:2410.01466 covers 5, 7, 11,
13). Until decided: draft W in full generality (ℓ ≥ 5); the re-basing, if
approved, deletes work rather than invalidating it.

## Chapter status after this ruling

`mapped → statement-audited` for W and the repaired inventory. First chapter
to complete the full charter protocol (two independent passes →
reconciliation → three-lens adversarial panel → adjudication).
