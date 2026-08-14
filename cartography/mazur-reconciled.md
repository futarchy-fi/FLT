# Mazur chapter — reconciled map (bead hub-lsb1u.2)

Reconciliation of two independent cartography passes:
- **P1** = `origin/cartography/mazur : cartography/mazur.md` (Claude/Fable, 2026-08-13)
- **P2** = `origin/cartography/mazur-b : cartography-b/mazur.md` (Cartographer B, independent)

Reconciler: adversarial cross-check pass, 2026-08-13. Repo facts below were re-verified
directly against `main` at reconciliation time, not taken from either pass.

---

## 1. Agreement matrix (high confidence — independently derived twice)

Both passes agree, with no coordination, on all of the following. These are the
high-confidence backbone of the chapter map.

| # | Agreed item | P1 | P2 |
|---|---|---|---|
| G1 | Blueprint invocation sites: `ch02reductions.tex:172-188` (`Mazur_Frey` / `FreyPackage.mazur`), `ch03freyold.tex:306-308` (`mazur`, "torsion ≤ 16"), plus `chtopbestiary.tex:233-246` "first sentence" warning | §1 | §1.1 |
| G2 | The Lean axiom is `Mazur_statement` at `FLT/Assumptions/Mazur.lean:105-106`, and its `ncard` phrasing literally means "≤ 16 **or infinite**", so torsion finiteness is a separate needed input | §1 | §1.2 |
| G3 | The bound 16 is only ever applied to curves with **full rational 2-torsion** (Frey curve and its quotient E/C) plus a rational point of prime order ℓ ≥ 5; contradiction 4ℓ ≥ 20 > 16 | §1 | §1.1, 1.3 |
| G4 | **The same weakest statement W** (see below), independently derived, including the same per-ℓ refinement | §1 W, W-a/b/c | §1.3 |
| G5 | Quotient-by-finite-Galois-stable-subgroup (blueprint `Elliptic_curve_quotient_by_finite_subgroup`) is a hard, blueprint-flagged (`\notready`) prerequisite; grade L | node 3 | A3 |
| G6 | The ℓ ≥ 17 core goes through modular Jacobians: X₀(ℓ) over Q + integral model, J₀(ℓ), Néron models, Hecke algebra, a rank-0 quotient, and a formal-immersion argument at the cusp | nodes 8-19 | D1-D9 |
| G7 | **The D6 fork**: Mazur's Eisenstein-quotient descent vs Merel-style winding quotient; both XL(+); the single biggest route decision; no third route found by either pass | node 16/16′, §5 | D6a/D6b, R2 |
| G8 | Cheapening via the FLT-regular Lean project (arXiv:2410.01466): classical FLT for small regular exponents can delete the fiddly small-ℓ cases by re-basing the top-level reduction; this is an **interface change** needing a project-level decision | §1, §5 | R3 |
| G9 | Mathlib status: elliptic curves/group law **exist**; division polynomials **partial**; modular forms/q-expansions **partial**, no Hecke operators; modular curves as schemes, Jacobians/abelian varieties, Néron models, finite flat group schemes, étale cohomology **absent**; class groups/Minkowski **exist**; FLT-repo seeds in `FLT/EllipticCurve/Torsion.lean`, `FLT/TateCurve/`, `FLT/GroupScheme/FiniteFlat.lean` | §4 | §4 |
| G10 | Classical small-curve determinations (Billing–Mahler 1940 for 11; Mazur–Tate 1973 for 13; Kubert 1976 for the 2×2ℓ cases) are the sources for the small-ℓ nodes | node 21 | C1-C4 |
| G11 | Route bibliography: Mazur 1977 (IHÉS 47), Mazur 1978 (Invent. 44), Merel 1996 (Invent. 124), Serre Duke 1987 §4.1 Prop. 6, Rebolledo & Darmon Clay expositions, Michaud-Jacobs arXiv:2209.03153 | §5 lit | §6 |

### The reconciled weakest statement W

Both passes independently converged on:

> **(W)** For every prime ℓ ≥ 5, there is no elliptic curve E over ℚ with
> E(ℚ) ⊇ ℤ/2 × ℤ/2 and a rational point of order ℓ
> (equivalently: ℤ/2 × ℤ/2ℓ never embeds in E(ℚ); equivalently, X₁(2, 2ℓ)(ℚ) = cusps).

with the agreed refinement:

- **Full 2-torsion is only needed for the small primes ℓ = 5, 7** (and would be needed
  for ℓ = 13 only in the "no-rebasing" branch as bookkeeping relief — see below). For
  ℓ = 5, 7 it is **essential**: ℤ/5, ℤ/7, ℤ/10 all occur as rational torsion, so
  "no point of order ℓ" is false there; only ℤ/2 × ℤ/2ℓ is excludable.
- **For ℓ ≥ 11 the cleaner, stronger statement suffices and should be used**:
  E/ℚ has no rational point of prime order ℓ (Y₁(ℓ)(ℚ) = ∅), discarding the
  2-torsion bookkeeping.
- W is strictly weaker than the repo's `Mazur_statement` (says nothing about torsion
  group structure, composite orders, or curves without full 2-torsion), and proving
  the literal `ncard ≤ 16` axiom would be strictly more work for no FLT gain. If W is
  proven, the axiom should be replaced by W and `FreyPackage.mazur` re-proved via the
  ch03 chain (P2's R4; endorsed).

---

## 2. Divergences, each resolved

### D-a. P1's node-20 endgame — "(?) reconstructed, not sourced" (adjudicated)

P1's node 20 derives "no ℓ-point, ℓ ≥ 11 (where the Eisenstein machinery applies)" by
splicing the *isogeny*-theorem endgame of Michaud-Jacobs with trivial isogeny character
λ = 1: potentially good reduction at q = 3 (node 19), then
ℓ | 1 − a₃ + 3 = 4 − a₃ with |a₃| ≤ 2√3 (Hasse), so ℓ ≤ 7 — contradiction. P1 itself
marked this reconstructed.

P2's D8 instead follows the standard torsion-theorem shape (Mazur 1977 / Snowden
Math 679 / Rebolledo): an order-ℓ point with ℓ ≥ 17 forces the associated non-cuspidal
point of X₀(ℓ)(ℚ) to reduce to a cusp mod 2 (or 3) — via Néron-model/small-special-fibre
counting (an order-ℓ point cannot inject into Ẽ(F₂), #Ẽ(F₂) ≤ 5, unless reduction is
multiplicative) — and the formal immersion then forces the point to *equal* the cusp.

**Resolution:** the two endgames are near-equivalent counting arguments
(ℓ | #Ẽ(F_q) with #Ẽ(F_q) small), but **P2's D8 formulation matches the sourced
literature route and is adopted as primary**; P1's λ = 1 trace-bound variant is retained
as an unverified alternative (it has the merit of reusing the isogeny-paper skeleton and
Michaud-Jacobs's write-up). Residual: the exact derivation must still be checked against
Mazur 1977 Theorem 8 and Snowden L20–L25 before Lean statements are frozen —
**panel question PQ1**. A side benefit of the P2 shape: at q = 2, 3 the fibre counts can
be obtained by finite enumeration, potentially avoiding the general Hasse bound (see D-e).

### D-b. P2's Merel/winding claim: Kolyvagin–Logachev 1989 + Gross–Zagier (adjudicated)

Verification: Kolyvagin–Logachev, *Finiteness of Ш and the group of rational points for
some modular abelian varieties*, is **1989** (Algebra i Analiz 1; transl. Leningrad
Math. J. 1990) — P2's year is right. Gross–Zagier is **1986** (Invent. Math. 84), not
1989; P2 only names it without a year, P1 groups it correctly. The winding-quotient
route (Merel 1996, applied at level ℓ) needs "analytic rank 0 ⇒ Mordell–Weil rank 0"
for quotients of J₀(ℓ), i.e. Kolyvagin–Logachev (which itself builds on Gross–Zagier
Heegner-point machinery), or alternatively Kato's Euler system (2004 — P1 notes this
option, P2 omits it).

**P2's "borderline for the repo's pre-1990 rule" concern is moot for our campaign**: the
pre-1990 restriction is the upstream FLT project's self-imposed rule, not ours. However,
**both passes' substantive point stands and they agree on it**: the literature-dependency
stack of D6b (Eichler–Shimura L-function theory + Gross–Zagier + Kolyvagin–Logachev, or
Kato) is enormous, comparable to D6a's Eisenstein-descent stack (flat cohomology,
Raynaud, finite flat group schemes over ℤ). Resolution: claim verified with the year
correction; the fork decision is **panel question PQ2**, to be decided on formalization
cost and reuse value (BSD-adjacent machinery), not on publication dates.

### D-c. The dead-code finding (adjudicated — VERIFIED against source)

P2 claimed `Mazur_statement` is used nowhere and `FreyPackage.mazur` is discharged by
the universal axiom. Re-verified directly against `main` at reconciliation time:

- `grep -rn Mazur_statement --include=*.lean` hits **only** its own declaration at
  `FLT/Assumptions/Mazur.lean:105`. No consumers. **Dead code: CONFIRMED.**
- `FLT/FreyCurve/Mazur.lean`: `theorem FreyPackage.mazur` (line 30) is proved by
  `knownin1980s` at **line 36** exactly as claimed, with the comment "this is in
  Serre's 1987 Duke paper".

**P2 is right, and the consequence is adopted**: the ch03 chain (unramified ⇒ trivial
characters ⇒ torsion point ⇒ contradiction with W) is not wired up in Lean at all. The
chapter's **first deliverable is that wiring** (node A5 below), which can be done *now*
with W stated as an axiom — it retires the blanket `knownin1980s` at this site and
replaces it with the precise assumption W, independent of proving W. P1 missed this
entirely (P1 read `Mazur_statement` as "the axiom actually assumed by the Lean
development", which is inaccurate — it is declared but unconsumed).

### D-d. Threshold of the hard core: ℓ ≥ 11 (P1) vs ℓ ≥ 17 (P2)

P1's W-a targets ℓ ≥ 11 via Eisenstein machinery "where J_e(p) ≠ 0", with 11, 13, 17, 19
also doable classically (node 21, listing X₁(17), X₁(19) as Ogg/Kubert). P2 places
ℓ = 11, 13 firmly in the classical Part C and starts the modular-Jacobian core at
ℓ ≥ 17, with no classical claim for 17, 19.

**Resolution:** partially resolved. ℓ = 11 (Billing–Mahler) and ℓ = 13 (Mazur–Tate,
genus 2 — note P1 itself observes X₀(13) has genus 0, so 13 cannot go through the
Eisenstein route regardless) are certainly classical: both passes agree. Whether
ℓ = 17, 19 have genuinely classical, formalization-cheaper proofs (P1's Ogg/Kubert
attribution, explicitly marked unverified) **is unresolved — panel question PQ3**. The
reconciled map conservatively routes ℓ ≥ 17 through the D-core (P2), with C5 recorded
as a possible cheapening.

### D-e. Hasse bound and Serre–Tate nodes (P1-only: nodes 5, 6)

P2 has no Hasse-bound or Serre–Tate/potentially-good-reduction-trace nodes; its D8
uses special-fibre counting at q = 2, 3. **Resolution:** these nodes are *conditional* —
required by P1's endgame variant, plausibly avoidable in P2's (finite enumeration of
Ẽ(F₂), Ẽ(F₃)). Kept in the inventory as conditional nodes B3, B4 pending PQ1. Note the
Tate curve (P1 node 7 / P2 external) is needed on **both** endgames (multiplicative
reduction ⇒ cusp) and stays unconditional.

### D-f. Formal-immersion criterion granularity

P1 splits the pure commutative-algebra criterion (node 17, S/M, "genuinely
Mathlib-ready") from its application to f_p (node 18, L). P2 merges both into D7
(L–XL). **Resolution: P1 is right** — the criterion (completed local rings, cotangent
surjectivity + Nakayama ⇒ point separation) has no modular content and is an immediate
work-bead candidate; keeping it separate preserves the only shovel-ready node in
Part D. Adopted as D7a/D7b.

### D-g. Rank-0 certification machinery (P2-only: B2/B3)

P2 alone itemizes *how* the small-curve cases are certified (per-curve full 2-descent;
a two-prime point-count sieve reduces the torsion part but cannot remove the rank-0
input). P1's node 21 hand-waves "explicit descent". **Resolution: P2 adopted** — this is
a real cost (one descent per target curve) and belongs in the map.

### D-h. Which regular primes the FLT-regular cheapening removes

P1 proposes re-basing at p ≥ 11 (deleting ℓ = 5, 7). P2 proposes deleting p ∈ {5, 7, 13}
(shrinking W to "no ℓ-point, ℓ ≥ 11, ℓ ≠ 13"). **Reconciler observation: both
understate the option.** 11 is *also* a regular prime (the first irregular prime is 37),
and the FLT-regular project covers all regular primes ≥ 5, so re-basing could in
principle go to **p ≥ 17 with p regular-excluded**, i.e. delete C1–C4 entirely and leave
only the D-core plus glue. Whether the upstream/top-level reduction interface allows
citing an external Lean development, and how far to push the re-basing, is the
**hub-lsb1u.12 decision (panel question PQ4)**. Until decided, the map keeps all of
Part C.

### D-i. Difficulty-grade disagreements (resolved by max, per protocol)

| Node | P1 | P2 | Reconciled |
|---|---|---|---|
| Torsion finiteness (A1) | S/M | M | **M** |
| Reduction injectivity (B1) | M/L | M | **L** (P2 notes minimal models/formal groups absent, supporting the high end) |
| ℓ = 5, 7 curves (C1, C2) | M | M–L | **L** (P2's descent-cost analysis, D-g) |
| ℓ = 11 (C3) | M | M | M |
| ℓ = 13 (C4) | M (P1 node 21) | L | **L** (genus-2 Jacobian; P2's analysis is more careful) |
| Formal immersion at ∞ (D7b) | L | L–XL | **L–XL** |
| Eisenstein descent (D6a) | XL | XL+ | **XL+** |

### D-j. Minor factual corrections

- P1 cites the Frey deduction reference correctly; both quote Serre §4.1 Prop. 6
  [number still unverified — PQ5].
- P2's conductor/genus claims for X₁(2,10) (=X₁(2,10) conductor 20), X₁(2,14), X₁(11)
  = 121b1 are all marked unverified by P2 itself — folded into PQ5.
- P1's "node count: 23" and P2's "22" are consistent with the merged 26 below (overlap
  minus granularity differences); no substantive node exists in one pass with no
  counterpart in the other **except**: P1's Atkin–Lehner involution content (in node 8,
  needed to swap cusps in its node 19) and P2's Eichler–Shimura relation (D5) — both
  retained in the merged D1/D5.

**Divergence tally: 10 catalogued; 7 fully resolved (D-b, D-c, D-e, D-f, D-g, D-i,
D-j); 3 resolved-with-residual routed to panel (D-a → PQ1, D-d → PQ3, D-h → PQ4).**

---

## 3. Reconciled statement inventory

Difficulty S < M < L < XL < XL+ (max of the two passes where they disagreed).
Confidence: high = both passes agree on statement and role; medium = one pass,
uncontradicted and plausible; low = one pass, unverified content.

### Part A — glue (chapter interface)

| Node | Statement | Diff | Conf | Source |
|---|---|---|---|---|
| A1 | E(ℚ)_tors is finite (reduction injection or Nagell–Lutz; far below Mordell–Weil) | M | high | P1:1, P2:A1 |
| A2 | E[n](ℚ̄) ≅ (ℤ/n)², Galois rep ρ̄, det = cyclotomic (sorried in `FLT/EllipticCurve/Torsion.lean`; Angdinata WIP — external blocker) | L | high | P1:2, P2:A2 |
| A3 | Quotient E/C by a finite Galois-stable subgroup, over ℚ, Galois-equivariant (blueprint `\notready`; Vélu-formula route vs fppf route open) | L | high | P1:3, P2:A3 |
| A4 | The three rational 2-torsion points survive in E/C for odd ℓ | S | high | P2:A4 (implicit in P1) |
| A5 | **Lean rewiring**: state W as the chapter axiom; prove `FreyPackage.mazur` from W via the ch03 chain, replacing `knownin1980s` at `FLT/FreyCurve/Mazur.lean:36`; retire the dead `Mazur_statement` (`FLT/Assumptions/Mazur.lean:105`) in coordination with upstream | M | high (repo facts re-verified) | P2:A5/R4; P1:22 partial |

### Part B — elliptic-curve toolbox

| Node | Statement | Diff | Conf | Source |
|---|---|---|---|---|
| B1 | Good reduction at q ⇒ E(ℚ)_tors → Ẽ(F_q) injective on prime-to-q torsion | L | high | P1:4, P2:B1 |
| B2 | Rank-0 certification for the specific curves X₁(11), X₁(2,10), X₁(2,14) by per-curve full 2-descent (+ point-count sieve for the torsion part); genus-2 variant for X₁(13) | M per curve (L for genus 2) | high | P2:B2/B3; P1:21 implicit |
| B3 | Hasse bound #Ẽ(F_q) = q+1−a_q, |a_q| ≤ 2√q — **conditional**: needed by the P1 endgame variant; possibly replaceable by finite enumeration over F₂, F₃ in the P2 endgame | L | medium (pending PQ1) | P1:5 |
| B4 | Serre–Tate: potentially good reduction ⇔ v_q(j) ≥ 0; integral trace bound — **conditional**, same status as B3 | L | medium (pending PQ1) | P1:6 |
| B5 | Tate curve / potentially multiplicative reduction: structure over ℚ_q for v_q(j) < 0; multiplicative reduction ⇒ the X₀-point reduces to a cusp (FLT-repo `FLT/TateCurve/` in progress) | L | high | P1:7, P2:D8-input |

### Part C — small primes (survives in full only if no re-basing; see PQ4)

| Node | Statement | Diff | Conf | Source |
|---|---|---|---|---|
| C1 | ℓ = 5: no ℤ/2×ℤ/10 ⊆ E(ℚ) — X₁(2,10) elliptic, rank 0, cusps only (Kubert 1976) | L | high | P1:21 W-c, P2:C1 |
| C2 | ℓ = 7: no ℤ/2×ℤ/14 — X₁(2,14) (Kubert 1976) | L | high | P1:21 W-b, P2:C2 |
| C3 | ℓ = 11: Y₁(11)(ℚ) = ∅ — X₁(11) elliptic, rank 0 (Billing–Mahler 1940) | M | high | P1:21, P2:C3 |
| C4 | ℓ = 13: Y₁(13)(ℚ) = ∅ — X₁(13) genus 2, rank-0 Jacobian descent (Mazur–Tate 1973) | L | high | P1:21, P2:C4 |
| C5 | ℓ = 17, 19 by classical explicit methods (Ogg/Kubert) — possible cheapening of the D-core's lower edge | M–L | **low** (P1-only, unverified — PQ3) | P1:21 |

### Part D — the modular-Jacobian core (ℓ ≥ 17)

| Node | Statement | Diff | Conf | Source |
|---|---|---|---|---|
| D1 | X₀(N), X₁(N) smooth proper geometrically connected over ℚ; cusps; j-map; Atkin–Lehner w_N over ℚ; moduli interpretation (coarse — twists, j = 0/1728 care) | XL | high | P1:8+9, P2:D1 |
| D2 | Integral model of X₀(ℓ) over ℤ, smooth over ℤ[1/ℓ]; cuspidal sections; Deligne–Rapoport fibre at ℓ; reduction map; v_q(j) < 0 points reduce to cusps | XL | high | P1:10, P2:D2 |
| D3 | J₀(ℓ) = Jac(X₀(ℓ)) as abelian variety over ℚ; Abel–Jacobi x ↦ [x−∞] | XL | high | P1:12, P2:D3 |
| D4 | Néron models; A(ℚ) = 𝒜(ℤ); torsion-specialization injectivity at odd good primes; char-2 subtlety (kernel of reduction at 2 is 2-power) | XL | high | P1:13, P2:D4 |
| D5 | Hecke algebra 𝕋 on J₀(ℓ); Cot ≅ S₂(Γ₀(ℓ)) compatibly with q-expansions; Eichler–Shimura relation on the fibre at p | XL | high | P1:14, P2:D5 |
| D6a | **Fork prong 1**: Eisenstein ideal, 𝕋/𝕀 ≅ ℤ/num((ℓ−1)/12), Mazur's descent ⇒ Eisenstein quotient has rank 0 (flat cohomology, Raynaud, finite flat group schemes over ℤ) | XL+ | high | P1:15+16, P2:D6a |
| D6b | **Fork prong 2**: winding quotient (Merel), analytic rank 0 by construction; MW rank 0 via Kolyvagin–Logachev 1989 (on Gross–Zagier 1986) or Kato 2004 | XL+ | high | P1:16′, P2:D6b |
| D7a | Formal-immersion criterion (pure commutative algebra: cotangent surjectivity + Nakayama ⇒ points reducing to the same F_q-point and mapping equally are equal) | S/M | high | P1:17 (P2:D7 subsumed) |
| D7b | X₀(ℓ) → J₀(ℓ) → A is a formal immersion at ∞̃ in char q ∈ {2, 3} (Cot(A) ↪ Cot(J₀), q-expansions, a₁ ≠ 0) | L–XL | high | P1:18, P2:D7 |
| D8 | An order-ℓ rational point (ℓ ≥ 17) yields non-cuspidal x ∈ X₀(ℓ)(ℚ) reducing to a cusp mod 2 (or 3); formal immersion + w_ℓ ⇒ x is a cusp — contradiction. **Primary formulation = P2's small-fibre/Néron route; P1's λ = 1 trace-bound variant recorded as alternative** | L | medium (formulation frozen only after PQ1) | P2:D8; P1:19+20 |
| D9 | Assembly: Y₁(ℓ)(ℚ) = ∅ for prime ℓ ≥ 17 | M | high | P2:D9; P1:20 |

### Assembly

| Node | Statement | Diff | Conf | Source |
|---|---|---|---|---|
| W | W from C1–C4 + D9 (ℓ = 5, 7 in full-2-torsion form; ℓ ≥ 11 in no-ℓ-point form); then A5 | S | high | P1:22, P2:W |

**26 nodes** (A1–A5, B1–B5, C1–C5, D1–D9 counting the D6 fork as two, W). Six are
XL-or-worse (D1–D6), one conditional pair (B3/B4), one low-confidence (C5).

Not needed (both passes concur, P1 explicit): Raynaud's isogeny-character
classification λ¹² = χˢ, resultant computations, class-number-1 endgame — those serve
the full isogeny theorem, not the torsion route (P1's "(?) confirm no hidden use" is
answered: P2's independent D-part makes no use of them).

Dependency edges: union of the two passes' edge lists (P1 §3, P2 §3) — no
contradictions between them; P2's extra edges (A2 → A3, D2 → D5) adopted.

---

## 4. Panel questions

- **PQ1 — Endgame formulation (from D-a).** Verify the D8 derivation against Mazur
  1977 Theorem 8 and Snowden L20–L25: exact use of the Néron special fibre at 2 vs 3,
  the char-2 torsion subtlety (D4), whether w_ℓ cusp-swapping is needed, and whether
  Hasse/Serre–Tate (B3/B4) can be dropped in favour of finite F₂/F₃ enumeration.
  P1's λ = 1 trace-bound variant: valid alternative or subtly wrong at the Hasse
  boundary (a₃ = 4 case)?
- **PQ2 — The D6 fork.** Eisenstein descent (self-contained, needs the finite-flat
  group-scheme + flat-cohomology stack, overlapping other FLT chapters) vs winding
  quotient (simpler quotient, imports Eichler–Shimura L-theory + Gross–Zagier 1986 +
  Kolyvagin–Logachev 1989, or Kato). **Our campaign has no pre-1990 restriction** — the
  decision is on total formalization cost and cross-chapter reuse only. A paper-audit
  decision spike is recommended before any Part-D formalization.
- **PQ3 — Are ℓ = 17, 19 classical?** P1's unverified Ogg/Kubert attribution (C5). If
  yes, the D-core's *first* required prime moves to 23, which changes nothing
  structurally but affects milestone ordering.
- **PQ4 — Exponent re-basing interface (feeds the hub-lsb1u.12 decision).** How far to
  push the FLT-regular cheapening: keep all of W; delete {5,7} (P1); delete {5,7,13}
  (P2); or delete {5,7,11,13} (reconciler: 11 is also regular) leaving only the D-core.
  Depends on whether the top-level reduction may cite the external FLT-regular Lean
  development and on upstream-interface politics.
- **PQ5 — Unverified citations to confirm before freezing Lean statements.** Serre
  Duke 1987 §4.1 Prop. 6; Silverman AEC VII.3.1; Mazur 1977 Thm 4/Thm 8 and Ch. II
  §9–10; Serre–Tate Thm 2; Kubert 1976 case locations; Billing–Mahler J. LMS 15 (1940)
  32–43; Mazur–Tate Invent. 22 (1973) 41–49; genus/conductor claims for X₁(2,10),
  X₁(2,14), X₁(11) = 121b1; Katz Invent. 63 (1980) Appendix.
- **PQ6 — Integral-model sizing (P1 §5).** Full Katz–Mazur/Deligne–Rapoport vs an ad
  hoc smooth-over-ℤ[1/ℓ] model with a "cusps catch potentially-multiplicative points"
  lemma; and the coarse-moduli rigidification for D1 (no circularity with D2).
- **PQ7 — Axiom replacement protocol.** Upstream (KMB) coordination for retiring the
  dead `Mazur_statement` in favour of W (verified dead at reconciliation; see §2 D-c).

---

## 5. Recommended next actions (ordered)

**Ready to become work beads now** (no panel dependency, no Mathlib blocker):

1. **A5 (wiring)** — state W in Lean as the chapter axiom and prove
   `FreyPackage.mazur` from it via the ch03 chain, removing the blanket
   `knownin1980s` at `FLT/FreyCurve/Mazur.lean:36`. Highest leverage per unit effort;
   makes the chapter's true interface machine-checked. (Coordinate PQ7 in parallel;
   the wiring itself does not need the upstream decision.)
2. **D7a (formal-immersion criterion)** — pure commutative algebra on Mathlib's
   existing completed-local-ring/cotangent/Nakayama stack; upstreamable to Mathlib.
3. **A4** — 2-torsion survives odd-order quotient (statement-level now, proof once A3
   lands; the statement can be frozen immediately).
4. **A1 (torsion finiteness)** — via Nagell–Lutz to avoid the reduction-theory
   dependency of B1; also unblocks the `ncard` reading of any interim axiom.
5. **Explicit plane models** of X₁(11), X₁(2,10), X₁(2,14), X₁(13) as curves with their
   rational-point statements frozen (proofs await B1/B2) — cheap, de-risks Part C.

**Await panel:**

- B3/B4 (Hasse, Serre–Tate) and the final D8 formulation — PQ1.
- Any Part-D formalization beyond D7a — PQ2 (fork) and PQ6 (model sizing) first;
  a decision-spike bead auditing D6a vs D6b on paper should be cut immediately.
- C5 — PQ3.
- Statement-freezing for D1 (coarse moduli) — PQ6.

**Await hub-lsb1u.12 (re-basing decision, PQ4):**

- C1, C2, C4 (deleted under any re-basing), C3 (deleted only under the p ≥ 17 variant),
  and the final shape of W in A5 (state W parametrically over "ℓ ≥ ℓ₀ with small-case
  side-conditions" so the wiring bead need not wait for the decision).

**Long-lead shared infrastructure** (start scoping with other chapters regardless of
panel outcomes, since every branch needs them): A2 (Angdinata's torsion work), A3
(quotient isogeny — Vélu route recommended for de-risking), B1, B5 (Tate curve, already
in progress in-repo), and the D1–D4 stack (shared with Shimura-curve chapters).
