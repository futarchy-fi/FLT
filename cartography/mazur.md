# Mazur — torsion of elliptic curves over Q (first independent map)

P1 cartography pass for bead hub-lsb1u.2. Mapper: Claude (Fable 5), 2026-08-13.
Everything below is a *map*, not a proof. Guessed or spliced edges are marked "(?)".

---

## 1. What FLT needs

### Where the blueprint invokes Mazur

- `blueprint/src/chapter/ch02reductions.tex:172-188` — **Theorem `Mazur_Frey`** (Lean:
  `FreyPackage.mazur`): *"If ρ is the mod p Galois representation associated to a Frey
  package (a,b,c,p) then ρ is irreducible."* The proof note says: *"This follows from a
  profound and long result of Mazur \cite{mazur-torsion} from 1977, namely the fact that
  the torsion subgroup of an elliptic curve over Q can have size at most 16. … A pre-1990
  reference for the full proof of this claim is Proposition 6 in §4.1 of \cite{serreconj}"*
  (Serre, Duke 1987).
- `blueprint/src/chapter/ch03freyold.tex:306-308` — **Theorem `mazur`**: *"Let E be an
  elliptic curve over Q. Then the torsion subgroup of E has size at most 16."*
- `FLT/Assumptions/Mazur.lean:105-106` — the axiom actually assumed by the Lean
  development:

  ```lean
  axiom Mazur_statement (E : WeierstrassCurve ℚ) [E.IsElliptic] :
      (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).ncard ≤ 16
  ```

  (Implementation note in the file: because `ncard` of an infinite set is 0, the axiom
  literally says "≤ 16 or infinite"; finiteness of torsion is easy and is assumed to be
  supplied separately.)
- `FLT/FreyCurve/Mazur.lean:30-36` — `FreyPackage.mazur` (irreducibility of the Frey
  curve's mod-p representation) is currently discharged by the `knownin1980s` axiom
  wrapper, citing Serre's 1987 Duke paper.
- `blueprint/src/chapter/chtopbestiary.tex:233-246` — discussion of the formalization
  cost; identifies "the first sentence of Mazur's proof" (quasi-finite separated
  commutative group schemes over Spec Z, finite flat over Z[1/N]) as the first milestone.

### How the bound 16 is actually used (blueprint ch03, lines 303-430)

The blueprint's own reduction (`Frey_characters_are_unramified` →
`Frey_characters_at_ell` → `Frey_characters_trivial` → `Frey_curve_reducible_structure`)
shows: if the Frey curve's E[ℓ] (ℓ ≥ 5 prime) is reducible, then **either** E **or** the
quotient E/C by the Galois-stable line has a *rational point of order ℓ*. Both E and E/C
also have **full rational 2-torsion** (the Frey curve is y² = x(x−aᵖ)(x+bᵖ); C has odd
order ℓ, so the three 2-torsion points survive in E/C). The contradiction drawn is
4ℓ ≥ 20 > 16.

### Weakest sufficient statement

The bound 16 is stronger than needed. What the argument uses is exactly:

> **(W)** For every prime ℓ ≥ 5, there is no elliptic curve E over Q with
> E(Q) ⊇ (Z/2Z)² × Z/ℓZ  (equivalently, E(Q) ⊇ Z/2Z × Z/2ℓZ).

W is what we should state in Lean as the Mazur-chapter target. It is *strictly weaker*
than the repo's `Mazur_statement` (torsion Z/2 × Z/8, size 16, is allowed by W and by
Mazur; Z/10 and Z/12 points are allowed by W but would violate a naive "no order-2ℓ
point" statement — note Z/10 **does** occur, so "no rational point of order 2ℓ" is FALSE
for ℓ = 5; the full 2-torsion hypothesis is essential).

W decomposes as:

- **(W-a)** [hard core] No elliptic curve over Q has a rational point of prime order
  ℓ ≥ 11. (Mazur 1977; the cases ℓ = 11, 13, 17, 19 are classical, see node 21.)
- **(W-b)** No elliptic curve over Q has a rational point of order 14
  (X₁(14)(Q) = cusps; classical, pre-Mazur).
- **(W-c)** No elliptic curve over Q has torsion containing Z/2 × Z/10
  (classical, pre-Mazur).
- **(W-glue)** trivial group theory: full 2-torsion + order-ℓ point ⇒ subgroup
  Z/2 × Z/2ℓ.

Cheaper still (route option, see §5): FLT for exponents 5 and 7 is classical (both are
regular primes; the Lean FLT-regular project, arXiv:2410.01466, already covers them), so
if the top-level reduction were re-based at p ≥ 11, only **W-a** would be needed and
W-b/W-c disappear.

---

## 2. Statement inventory

Nodes needed to prove W, following Mazur 1977/1978 as reorganized by modern expositions
(Michaud-Jacobs arXiv:2209.03153; Rebolledo, Clay Proc. 8 (2009); Darmon, Clay Proc. 8
(2009)). Difficulty: S < M < L < XL (formalization effort guess, given current
Mathlib/FLT state).

### Group I — elliptic curve infrastructure

1. **Finiteness of E(Q)_tors.** The torsion subgroup of an elliptic curve over Q is
   finite. Needed to make the `ncard`/W statement bite; much easier than Mordell–Weil
   (reduction injectivity or Lutz–Nagell). — **S/M** — Silverman AEC VII.3 / VIII.7.
2. **Mod-ℓ representation and Weil pairing.** E[ℓ](Q̄) ≅ (Z/ℓ)² for ℓ ≠ char, Galois
   action gives ρ̄: G_Q → GL₂(F_ℓ), det ρ̄ = mod-ℓ cyclotomic character. — **M** —
   Silverman AEC III.8; FLT repo already has `FLT/EllipticCurve/Torsion.lean` and
   `FLT/KnownIn1980s/EllipticCurves/WeilPairing.lean`.
3. **Quotient by a finite rational subgroup.** For C ⊂ E(Q̄) Galois-stable of order ℓ
   there is E/C over Q and an isogeny E → E/C with kernel C, Galois-equivariant on
   points. (Blueprint node `Elliptic_curve_quotient_by_finite_subgroup`,
   ch03freyold.tex:399, already flagged `\notready`; Conrad's fppf-quotient sketch is
   recorded there.) — **L** — Silverman AEC III.4.12 + Exercises; Katz–Mazur for the
   scheme-theoretic version.
4. **Reduction mod q and injectivity on prime-to-q torsion.** For E/Q with good
   reduction at q, reduction E(Q) → Ẽ(F_q) is injective on prime-to-q torsion. —
   **M/L** — Silverman AEC VII.3.1; Mathlib now has
   `Mathlib.AlgebraicGeometry.EllipticCurve.Reduction` as a starting point.
5. **Hasse bound.** #Ẽ(F_q) = q + 1 − a_q with |a_q| ≤ 2√q. — **L** (mathematically M,
   but absent in Lean; provable via division polynomials / the degree quadratic form) —
   Silverman AEC V.1.1.
6. **Potentially good reduction and the trace bound.** E has potentially good reduction
   at q iff v_q(j(E)) ≥ 0; for such E and q ≠ p, Tr ρ_{E,p}(σ_q) ∈ Z with
   |Tr| ≤ 2√q (attain good reduction over a totally ramified extension, then Hasse).
   — **M/L** given 5 — Serre–Tate, Ann. Math. 88 (1968) 492–517, Theorem 2 & §2
   (number unverified); Michaud-Jacobs Lemma 4.2.
7. **Tate curve / potentially multiplicative reduction.** Structure of E over Q_q with
   v_q(j) < 0: Tate curve or quadratic twist thereof; consequences for ρ̄ and for which
   point of X₀ the reduction hits (a cusp). — **L** — Silverman, Advanced Topics V;
   FLT repo has `FLT/TateCurve/` and `FLT/KnownIn1980s/EllipticCurves/TateCurve*.lean`
   in progress.

### Group II — modular curves

8. **X₀(N) over Q.** Smooth projective geometrically connected curve over Q; two
   rational cusps 0, ∞; the j-map X₀(N) → P¹ with cusps as poles; Atkin–Lehner
   involution w_N over Q swapping the cusps. — **XL** — Diamond–Shurman GTM 228,
   Ch. 7–8; Deligne–Rapoport.
9. **Moduli interpretation over Q.** A pair (E, C)/Q (C rational cyclic of order N)
   gives a non-cuspidal point [E,C] ∈ X₀(N)(Q) with j([E,C]) = j(E); conversely up to
   twist (coarse moduli — care needed at j = 0, 1728). Only the forward direction plus
   "j of a non-cuspidal point is the j of some curve with an isogeny" is needed. —
   **L/XL** — Diamond–Shurman 8.6; Katz–Mazur Ch. 8.
10. **Integral model of X₀(N), N prime.** A model over Z, smooth over Z[1/N], with
    cuspidal sections; reduction map X₀(N)(Q) = X₀(N)(Z_q) → X₀(N)(F_q) for q ≠ N;
    a point with v_q(j) < 0 (potentially multiplicative reduction) reduces to a cusp
    mod q. — **XL** (this is the bestiary's "first sentence" bottleneck) —
    Deligne–Rapoport 1973; Katz–Mazur; Mazur 1977 Ch. II.
11. **Genus computations for small levels.** Genus of X₀(p), X₁(p), X₁(2N) for the
    small cases (X₁(11), X₁(13), X₁(14), the Z/2×Z/10 curve): explicit plane models.
    — **M** — Diamond–Shurman 3.1, 3.9; explicit models in the classical papers of
    node 21.

### Group III — Jacobian, Eisenstein quotient, formal immersion

12. **Jacobian J₀(N).** J₀(N) = Jac(X₀(N)) as an abelian variety over Q; Abel–Jacobi
    ι: X₀(N) → J₀(N), y ↦ [y − ∞]. — **XL** (abelian varieties absent from Mathlib) —
    Milne, "Jacobian varieties"; Diamond–Shurman 6.1.
13. **Néron models and torsion injectivity for abelian varieties.** Néron model over
    Z_q; for q > 2 (or q odd, good reduction) reduction is injective on
    A(Q)_tors; more precisely the specialization statement needed to turn
    "reductions agree mod q" into "points agree". — **XL** — BLR, *Néron Models*;
    Katz, Invent. Math. 63 (1980), Appendix (cited for this in Michaud-Jacobs §3.2).
14. **Hecke algebra on J₀(p) and cotangent = cusp forms.** Hecke operators T_r (r ≠ p)
    and w_p acting on J₀(p); T := Z[w_p, T_r]; identification
    Cot₀(J₀(p)/Z_q) ≅ S₂(Γ₀(p); Z_q) compatibly with q-expansions (T_r on
    q-expansions by the usual formula). — **XL** — Mazur 1977 Ch. II §5–6; Ribet–Stein,
    *Lectures on Modular Forms and Hecke Operators*; Diamond–Shurman 6.3, 7.9.
15. **Eisenstein ideal and Eisenstein quotient.** I := (w_p + 1, T_r − r − 1 : r ≠ p)
    ⊂ T; J_e(p) := J₀(p)/(∩ₖ Iᵏ)J₀(p), a non-trivial *optimal* quotient for p ≥ 11,
    p ≠ 13 (genus X₀(p) > 0). — **L** given 12–14 — Mazur 1977 Ch. II §9–10 (numbers
    unverified); Michaud-Jacobs §3.2.
16. **Rank zero of the Eisenstein quotient.** J_e(p)(Q) is finite. This is the deepest
    single node: Mazur's descent using the Eisenstein ideal, group schemes over Z,
    flat/étale cohomology. — **XL** — Mazur 1977, Theorem 4 (theorem number as cited
    in Michaud-Jacobs; the paper's III.§3).
    - **16′ (alternative).** Winding quotient J^w(p) (Merel 1996): its analytic rank is
      0 by construction and its Mordell–Weil rank is 0 by Kolyvagin–Logachev (or Kato).
      Simpler quotient construction, but imports the Gross–Zagier/Kolyvagin (or Kato
      Euler system) machine. — **XL** — Merel, Invent. Math. 124 (1996) 437–449;
      Kolyvagin–Logachev; Rebolledo (Clay 2009).
17. **Formal immersion criterion.** f: X → Y over Z_q a formal immersion at
    x ∈ X(F_q) (surjectivity on completed local rings ⇔ surjectivity on cotangent
    spaces when residue fields agree, via Nakayama); if P, Q ∈ X(Z_q) both reduce to x
    and f(P) = f(Q) then P = Q. — **S/M** (pure commutative algebra; a genuinely
    Mathlib-ready node) — Michaud-Jacobs Lemmas 3.3, 3.4; Mazur 1978 §3.
18. **f_p is a formal immersion at ∞ in characteristic q.** For q ≠ 2, p and A_p a
    non-trivial optimal quotient of J₀(p), the composite
    f_p: X₀(p) → J₀(p) → A_p is a formal immersion at ∞̃ ∈ X₀(p)(F_q): uses
    Cot(A_p) ↪ Cot(J₀(p)) for q > 2 (Mazur 1978, Corollary 1.1), the q-expansion
    identification (node 14), and a₁ ≠ 0 for Hecke eigenforms. — **L** — Mazur 1978,
    Proposition 3.2; Michaud-Jacobs Proposition 3.5.
19. **Non-cuspidal rational points don't reduce to cusps.** For p such that J_e(p) ≠ 0
    and rank 0, q ≠ 2, p: x ∈ X₀(p)(Q) with x̃ = ∞̃ in X₀(p)(F_q) forces x = ∞.
    Consequently (via 7, 10, and w_p to swap cusps): an elliptic curve E/Q with a
    rational p-isogeny has potentially good reduction at every prime q ≠ 2, p. —
    **L** (glue) — Mazur 1978, Corollary 4.4 (stated there for the isogeny theorem);
    Michaud-Jacobs Theorem 3.1 + Proposition 3.2.
20. **Torsion endgame (W-a for ℓ ≥ 23, and ℓ ≥ 11 where J_e ≠ 0).** Suppose
    P ∈ E(Q) has prime order ℓ ≥ 11. Then ⟨P⟩ is a rational ℓ-isogeny whose isogeny
    character λ is *trivial* (P is rational). By node 19, E has potentially good
    reduction at q = 3; λ(σ₃) = 1 is an eigenvalue of ρ̄(σ₃), so
    ℓ | 1 − a₃ + 3 with |a₃| ≤ 2√3 (node 6), and 0 < |4 − a₃| ≤ 4 + 2√3 < 8 < ℓ —
    contradiction. **(?)** — this endgame is my splicing of Mazur's torsion argument
    onto the isogeny-paper skeleton (Michaud-Jacobs §4.2 with λ = 1); the official
    statement is Mazur 1977, Theorem 8 ("[11, Theorem 8]" as cited by Michaud-Jacobs)
    via Theorem 2/Theorem 7 of that paper (numbers unverified). A verifier must check
    the exact derivation, including that q = 3 is legitimate (q ≠ 2, p ✓) and how
    Mazur handles a₃ = 4 being impossible vs. the boundary of the Hasse bound. — **M**
    given the rest.
21. **Classical small cases.** Explicit determinations, each a rank-0 computation on a
    genus ≤ 2 curve with an explicit plane model — attractive early formalization
    targets:
    - X₁(11)(Q) = cusps (no rational 11-torsion point): Billing–Mahler, J. London
      Math. Soc. 15 (1940) (number unverified).
    - X₁(13)(Q) = cusps: Mazur–Tate, "Points of order 13 on elliptic curves",
      Invent. Math. 22 (1973) (number unverified).
    - X₁(17), X₁(19) = cusps: Ogg, and/or Kubert, "Universal bounds on the torsion of
      elliptic curves", Proc. LMS 33 (1976) (attribution/numbers unverified).
    - **W-b**: X₁(14)(Q) = cusps: Kubert 1976 / Ogg (unverified).
    - **W-c**: no torsion Z/2 × Z/10: Kubert 1976 (unverified).
    — **M each**.
22. **Assembly of W.** W-glue (trivial) + W-a (nodes 19–21) + W-b + W-c (node 21);
    then `Mazur_Frey` follows via the blueprint's own ch03 reduction (which lives in
    the Frey chapter, not this one). — **S** given the rest.

Node count: 23 (counting 16′).

Explicitly NOT needed for W (route economy): Raynaud's theorem on group schemes of type
(p,…,p), the isogeny-signature classification λ¹² = χ^s, the resultant computations
R_{q,s}, and the class-number-1 endgame (Michaud-Jacobs §4.1–4.3) — those are only
needed for the full *isogeny* theorem (non-trivial λ). The torsion route sets λ = 1 and
skips all of it. **(?)** — second mapper should confirm no hidden use.

---

## 3. Dependency edges

Internal (by node number):

| Node | Depends on |
|------|-----------|
| 1 | 4 (or standalone Lutz–Nagell) |
| 2 | — (Mathlib EC + Weil pairing) |
| 3 | 2 |
| 4 | — (EC reduction theory) |
| 5 | — (isogenies, dual isogeny, deg quadratic form) |
| 6 | 4, 5, 7 |
| 7 | — (p-adic analysis, formal groups lite) |
| 8 | — (curves over Q, function fields / modular forms) |
| 9 | 8, 3 |
| 10 | 8, 9 (moduli over Z) |
| 11 | 8 |
| 12 | 8 |
| 13 | 12 |
| 14 | 12, + modular forms q-expansions |
| 15 | 14 |
| 16 | 15, + flat/étale cohomology, finite flat group schemes over Z (descent) |
| 16′ | 15-analog, + modular L-functions, Gross–Zagier/Kolyvagin or Kato |
| 17 | — (commutative algebra only) |
| 18 | 12, 14, 15, 17 |
| 19 | 7, 9, 10, 13, 16 (or 16′), 17, 18 |
| 20 | 2, 3, 6, 19 (?) |
| 21 | 11, + explicit descent on genus 1–2 curves (Mordell–Weil rank 0 computations) |
| 22 | 20, 21, W-glue |

External chapter / Mathlib dependencies:

- **Frey chapter (blueprint ch03)**: the reduction from `Mazur_Frey` to W uses
  `frey_curve_unramified`, `frey_curve_at_2`, `Frey_curve_mod_ell_rep_at_ell`
  (finite flat at ℓ), the Tate curve, Serre's Prop 11 (canonical subgroup /
  ordinary case), Minkowski's discriminant theorem, and node 3. That reduction is
  already mapped in the blueprint and is *not* re-counted here; interface = statement W.
- **Finite flat group schemes chapter**: nodes 10, 16 (FLT repo:
  `FLT/GroupScheme/FiniteFlat.lean` is the seed).
- **Modular forms / Hecke chapter**: node 14 (Mathlib has modular forms and Eisenstein
  q-expansions; no Hecke operators yet — see §4).
- **Algebraic geometry (Mathlib)**: nodes 8, 10, 12, 13 need proper curves, Jacobians,
  abelian schemes, Néron models — essentially all absent (§4).
- **Number fields (Mathlib)**: node 21 descent arguments need class groups / unit
  computations — largely available.

---

## 4. Mathlib anchors

Checked 2026-08-13 against the Mathlib pinned by this repo's imports plus web docs.
"exists / partial / absent" refers to Mathlib proper; FLT-repo files noted separately.

| Area | Status | Anchor |
|------|--------|--------|
| Weierstrass/elliptic curves, group law | **exists** | `Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass`, `…EllipticCurve.Affine.Point` (`WeierstrassCurve.Affine.Point`), `…VariableChange` |
| Division polynomials / n-torsion structure | **partial** | `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`; full E[n] ≅ (Z/n)² not there (?) |
| Reduction of elliptic curves | **partial** | `Mathlib.AlgebraicGeometry.EllipticCurve.Reduction` (imported by FLT repo) |
| Mod-p Galois rep of an EC | **absent in Mathlib; exists in FLT repo** | `FLT/EllipticCurve/Torsion.lean` (`galoisRep`), `FLT/KnownIn1980s/EllipticCurves/WeilPairing.lean` |
| Mordell–Weil / torsion finiteness | **absent** (?) | roadmap item in the group-law paper; nothing found in Mathlib docs |
| Hasse bound over F_q | **absent** (?) | — |
| Modular forms, Eisenstein series, q-expansions | **partial** | `Mathlib.NumberTheory.ModularForms.*`, incl. `…EisensteinSeries.QExpansion` (imported by FLT repo) |
| Hecke operators | **absent** (?) | not found in Mathlib docs search |
| Modular curves X₀(N)/X₁(N) as curves/schemes | **absent** | only `Mathlib.NumberTheory.Modular` (group action on ℍ, fundamental domain) |
| Jacobians of curves / abelian varieties | **absent** | — |
| Néron models | **absent** | — |
| Finite flat group schemes | **absent in Mathlib; seed in FLT repo** | `FLT/GroupScheme/FiniteFlat.lean`; blueprint bestiary names this the first milestone |
| Étale/flat cohomology | **absent-to-partial** (?) | some étale-site groundwork in Mathlib AG; nothing usable for node 16 |
| Tate curve | **absent in Mathlib; in progress in FLT repo** | `FLT/TateCurve/`, `FLT/KnownIn1980s/EllipticCurves/TateCurve*.lean` |
| Cyclotomic character | **exists** | `Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter` (imported by FLT repo) |
| Class groups, Minkowski bound, unit computations (node 21 descents) | **exists** | `Mathlib.NumberTheory.ClassNumber.*`, `Mathlib.RingTheory.ClassGroup.Basic` |
| Completed local rings, cotangent, Nakayama (node 17) | **exists** | `Mathlib.RingTheory.AdicCompletion.*`, `Mathlib.RingTheory.Ideal.Cotangent`, Nakayama in `Mathlib.RingTheory.Nakayama` (module names partly guessed (?)) |

Ready-now formalization targets: node 17 (formal immersion criterion — pure commutative
algebra), node 21 (explicit small modular curves as plane curves + descent), node 5
(Hasse), node 1.

---

## 5. Route risk

- **The p ∈ {5,7} discharge decision.** W-b/W-c (small-level modular-curve
  computations) could be avoided entirely by re-basing the top-level FLT reduction at
  p ≥ 11 and citing classical FLT for exponents 5 and 7 (both regular primes; already
  formalized in the FLT-regular Lean project, arXiv:2410.01466). This changes the
  *interface* of the Mazur chapter (W → W-a) and needs a project-level decision;
  a second mapper should cost both branches. Similarly, ℓ ∈ {11,13,17,19} can go via
  node 21 classical computations instead of the Eisenstein machinery — check exactly
  which ℓ the formal-immersion route covers (J_e(p) non-trivial requires genus > 0,
  so p = 13 must go via Mazur–Tate regardless).
- **Eisenstein descent (16) vs winding quotient (16′).** Both are XL and this is the
  single biggest fork in the map. Mazur's descent is self-contained but needs flat
  cohomology and group schemes over Z (the "first sentence" stack). The winding route
  has a simpler quotient but imports Kolyvagin–Logachev or Kato — machinery with
  possible reuse elsewhere in a BSD-adjacent future but enormous on its own. I did
  not find a route that avoids both. Second mapper: hunt specifically for any
  post-2010 proof of W-a with a cheaper rank-0 input.
- **Node 20 is spliced, not sourced.** My torsion endgame (λ = 1 into the
  isogeny-paper skeleton, q = 3, Hasse bound) reproduces folklore but I did not
  verify it against Mazur 1977 Theorem 8's actual derivation or Rebolledo's notes;
  the handling of ℓ | 4 − a₃ at the Hasse boundary and of additive reduction at 3
  needs checking. Marked (?) throughout.
- **Integral models (node 10) sizing.** Whether one needs full Katz–Mazur /
  Deligne–Rapoport or can get away with an ad hoc smooth-over-Z[1/p] model plus a
  "cusps catch potentially-multiplicative points" lemma is the largest *infrastructure*
  uncertainty; it dominates the XL estimates for 8, 10, 12, 13, 14.
- **Coarse moduli subtleties (node 9).** X₀(N) is a coarse moduli space; twists,
  j = 0, 1728, and the exact statement of "x̃ = cusp ⇒ potentially multiplicative"
  need a careful rigidified formulation (auxiliary level structure) before Lean
  statements are frozen. Verify no circularity with node 10's model.

### Primary literature

- Mazur, *Modular curves and the Eisenstein ideal*, Publ. Math. IHÉS 47 (1977) 33–186.
- Mazur, *Rational isogenies of prime degree*, Invent. Math. 44 (1978) 129–162.
- Michaud-Jacobs, *Mazur's isogeny theorem*, arXiv:2209.03153 (expository; source of
  the Section-3 skeleton used above).
- Rebolledo, *Merel's theorem on the boundedness of the torsion of elliptic curves*,
  Clay Math. Proc. 8 (2009) 71–82; Darmon, *Rational points on curves*, ibid. 7–53.
- Merel, *Bornes pour la torsion des courbes elliptiques sur les corps de nombres*,
  Invent. Math. 124 (1996) 437–449.
- Serre, *Sur les représentations modulaires de degré 2 de Gal(Q̄/Q)*, Duke Math. J. 54
  (1987), §4.1 Prop. 6 (the Frey-irreducibility deduction cited by the blueprint).
- Serre–Tate, *Good reduction of abelian varieties*, Ann. Math. 88 (1968) 492–517.
- Katz–Mazur, *Arithmetic Moduli of Elliptic Curves*, Ann. of Math. Studies 108.
- Katz, *Galois properties of torsion points on abelian varieties*, Invent. Math. 63
  (1980), Appendix.
