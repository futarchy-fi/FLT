# Mazur D6 fork — Eisenstein-quotient paper audit (bead hub-lsb1u.2.7)

Panel-mandated decision spike for **PQ2** of `cartography/mazur-reconciled.md`
(branch `cartography/mazur-reconciled`, §4). Audits the two candidate routes for
the rank-zero input to node D8 (an abelian-variety quotient A of J₀(ℓ) with
A(ℚ) finite, receiving X₀(ℓ) via a formal immersion):

- **D6a** — Mazur's Eisenstein-quotient descent (Mazur, *Modular curves and the
  Eisenstein ideal*, Publ. Math. IHÉS 47 (1977), 33–186; Chapters I–III).
- **D6b** — Merel-style winding quotient (Merel, Invent. 124 (1996)) with rank 0
  via Kolyvagin–Logachev 1989 on Gross–Zagier 1986 (or Kato 2004).

Auditor: web-grounded literature pass, 2026-08-14. Working tree only, not committed.
Grades S < M < L < XL < XL+ are against Mathlib + FLT-repo state as of the
reconciled map's §G9 (re-spot-checked: `FLT/GroupScheme/FiniteFlat.lean` exists on
`main`; Mathlib has modular forms as ℂ-vector spaces but **no Hecke operators**
(q-expansions/Hecke algebras still WIP outside Mathlib per the Lean community blog
modular-forms post); **no** modular curves as schemes, Jacobians, abelian
varieties, Néron models, Néron–Tate or Weil height machine, Heegner points, or
Euler systems — nothing Heegner-adjacent has been formalized anywhere).

**Scope note that frames everything:** our target is W for ℓ ≥ 17 over **ℚ only**
(d = 1). Merel 1996's actual content is uniform boundedness over degree-d number
fields; for d = 1 his theorem *is* Mazur's theorem, and route (b) is really
"replace Mazur's Ch. I+III descent by KL/GZ, keep everything else". Both routes
share the entire D1–D5 + D7 substrate (X₀(ℓ) with integral model, J₀(ℓ), Néron
models, Hecke algebra, formal immersion). The fork only decides how rank 0 of the
chosen quotient is proved.

---

## 1. Route D6a — Eisenstein-quotient descent: dependency stack

Primary source structure (Mazur 1977, verified against the MR summary, the
numdam text, Parson's *Mazur's Eisenstein descent* (Stanford VIGRE notes), the
Snowden Math 679 course (25 lectures; Achenjang's typed notes), and the
Cambridge 2020 study-group schedule):

| # | Component | Content | Grade | Notes |
|---|---|---|---|---|
| a1 | Mazur I §1 | Finite flat group schemes over ℤ; Oort–Tate classification of order-p group schemes; **admissible** group schemes (filtration by ℤ/p, μ_p) and their fppf invariants | **XL** | Builds directly on `FLT/GroupScheme/FiniteFlat.lean`; Raynaud (p,…,p) is needed only in mild form here (full Raynaud serves the isogeny paper, not this route) |
| a2 | Mazur I (cont.) + III §2 prep | fppf cohomology over Spec ℤ; H¹ of elementary admissibles (unit/class-group computations); dévissage; the **model theorem**: A/ℚ good outside ℓ, toric at ℓ, A[p] admissible ⇒ rank A(ℚ) = 0 (Parson's exposition) | **XL** | The genuinely novel infrastructure; fppf site partially exists in Mathlib (flat topology on schemes), Néron-model interface shared with D4 |
| a3 | Mazur II §§1–9 | Modular forms over rings, q-expansion principle mod p | XL | Substantially shared with D5 (already on the map); Katz-style geometric modular forms |
| a4 | Mazur II §§9–18 | Hecke algebra 𝕋, Eisenstein ideal 𝕀, 𝕋/𝕀 ≅ ℤ/n with n = num((ℓ−1)/12), Gorenstein/multiplicity one at Eisenstein primes, cuspidal group C of order n (Ogg) | **XL** | Pure algebra over the D5 interface; Wake–Wang-Erickson (Duke 169 (2020), arXiv:1707.01894) give a pseudodeformation-ring reproof of the 𝕋-structure results for p > 3 — an *option*, not obviously cheaper (needs finite-flat deformation conditions + Galois cohomology/Massey products) |
| a5 | Mazur III §§1–3 | Eisenstein quotient J̃ = J₀(ℓ)/γJ₀(ℓ); J̃[𝔓] admissible; apply a2 ⇒ **J̃(ℚ) finite** (III.3.1); transfer of X₀(ℓ)(ℚ)-points | **XL** | The descent proper; consumes a1–a4 + D2/D3/D4 |

Modern expositions that de-risk the audit: Snowden's Math 679 (full course,
L01–L25, with typed notes — effectively a pre-made blueprint at lecture
granularity), Parson's descent notes (isolates a1–a2 as a standalone ~15pp
argument), the Cambridge study-group schedule (dependency-ordered), Rebolledo's
Clay survey and Darmon's companion (context), Wake–Wang-Erickson (a4 option).

**Route total (beyond shared D1–D5/D7):** ≈ 3 net-new XL blocks (a1+a2 ≈ one
infrastructure XL-pair, a4, a5); a3 is largely D5. Everything is *algebraic*,
p-adic/fppf-flavored, and decomposes (see §3). High intra-campaign reuse:
finite flat group schemes and fppf descent are needed by the FLT main line
anyway (flat deformation conditions in R=T; `FLT/GroupScheme/` already seeded).

## 2. Route D6b — winding quotient: dependency stack

Primary sources: Merel 1996; Rebolledo's Clay exposition; Stein's torsion-points
survey; KL = Kolyvagin–Logachev, Algebra i Analiz 1 (1989); GZ = Gross–Zagier,
Invent. 84 (1986); Kato, Astérisque 295 (2004) as the alternative.

| # | Component | Content | Grade | Notes |
|---|---|---|---|---|
| b1 | Modular symbols | H₁(X₀(ℓ); ℤ), Manin symbols, winding element e, Hecke action; Merel's independence computation (for d = 1 this shrinks to Mazur/Kamienny's formal-immersion input, already node D7b) | **M–L** | The one genuinely Lean-friendly item in the whole landscape: finite combinatorics + linear algebra; would upstream well |
| b2 | Winding quotient | J_e = J₀(ℓ)/I_e J₀(ℓ); needs abelian-variety quotients by Hecke-stable subvarieties | L | Comparable to a5's quotient formation; shared with D3/D4 |
| b3 | Eichler–Shimura L-theory | L(f, s) for weight-2 newforms, analytic continuation, L(J_e, 1) ≠ 0 by construction of e (period integrals; Eichler–Shimura relation already node D5) | **XL** | Mathlib has Dirichlet L-series machinery but no modular L-functions, no period integrals on X₀(N) |
| b4 | **Gross–Zagier 1986** | Heegner points via CM theory; Néron–Tate heights; local height decomposition; automorphic Green functions on Γ₀(N) (archimedean); arithmetic-intersection computation on the integral model (non-archimedean); Rankin–Selberg convolution + functional equation; **holomorphic projection**; the height = L′ identity | **XL+** | ~130pp mixing hard analysis and Arakelov-flavored arithmetic geometry. Mathlib has: no height machine at all (Néron–Tate, local heights, Green functions all absent), no Rankin–Selberg, no holomorphic projection, no CM theory/ring class fields. Alone plausibly exceeds all of D6a |
| b5 | **Kolyvagin–Logachev 1989** | Heegner-point Euler system for quotients of J₀(N): ring class fields, Kolyvagin derivative classes, Galois cohomology/Tate local duality, Čebotarev; L(A,1) ≠ 0 ⇒ A(ℚ), Ш(A) finite | **XL** | Needs b4's Heegner points + class field theory (FLT CFT chapter helps somewhat) + Selmer-group formalism (absent) |
| b5′ | Kato 2004 (alt. to b4+b5) | Euler system from Beilinson elements in K₂ of modular curves; p-adic Hodge theory; explicit reciprocity laws | **XL+** | Strictly worse for formalization than b4+b5; recorded for completeness |

**Route total (beyond shared substrate):** b1 (M–L) + b2 (L) + b3 (XL) + b4
(XL+) + b5 (XL). The analytic/Arakelov content of b4 has **zero** overlap with
the rest of the FLT campaign; no formalization effort anywhere has touched
Heegner points, height pairings, or Euler systems.

## 3. Decomposition mandate — D6a's top three XL components into ≤ M steps

Grades below are **conditional on the shared interfaces** (D2 integral model,
D3 Jacobian, D4 Néron model, D5 Hecke/q-expansions) being available as stated
Lean interfaces (axioms/sorried defs during development), per campaign practice.

### 3.1 a1+a2 — admissible group schemes and the model theorem

| Step | Statement | Grade |
|---|---|---|
| G1 | Order-p finite flat group schemes over ℤ are ℤ/p or μ_p (Oort–Tate over ℤ; can use the low-ramification/Fontaine-style shortcut — discriminant bounds — rather than full Oort–Tate over general bases) | M |
| G2 | Definition + closure properties of admissible group schemes (filtration with quotients ℤ/p, μ_p; subs/quotients/extensions) | S–M |
| G3 | Invariants of elementary admissibles: H⁰ and H¹_fppf(Spec ℤ, ℤ/p) and (Spec ℤ, μ_p) computed via Kummer/Artin–Schreier-type sequences + ℤ's unit group and Pic(ℤ) = 0 | M |
| G4 | Dévissage: long-exact-sequence bookkeeping bounding H¹_fppf of any admissible group by its filtration length | M |
| G5a | fppf Kummer sequence for the Néron model 𝒜/ℤ: 0 → 𝒜[p] → 𝒜 → 𝒜 → 0 for good-reduction-outside-ℓ, toric-at-ℓ A (correction term at ℓ isolated as its own lemma) | M |
| G5b | Selmer-vs-integral comparison: Sel_p(A/ℚ) ↪ H¹_fppf(Spec ℤ, 𝒜[p]) | M |
| G5c | Toric-at-ℓ correction: component-group contribution at ℓ is controlled (Mazur I.3/App.; finite explicit group) | M |
| G6 | Model theorem: A[p] admissible ⇒ Sel_p finite of bounded order ⇒ (iterated p-descent) rank A(ℚ) = 0 | M |

### 3.2 a4 — Eisenstein ideal and Hecke-algebra structure

| Step | Statement | Grade |
|---|---|---|
| E1 | Arithmetic of n = num((ℓ−1)/12); the Eisenstein series E of weight 2 level ℓ, its q-expansion, constant term (ℓ−1)/24 | S |
| E2 | 𝕋 ⊆ End(S₂(Γ₀(ℓ); ℤ)) as a finite free ℤ-algebra via q-expansions (interface to D5) | M |
| E3 | 𝕀 = (1 + q − T_q : q ≠ ℓ prime; 1 + w_ℓ); 𝕋/𝕀 is cyclic as ℤ-module | S–M |
| E4 | Cuspidal group C = ⟨[0] − [∞]⟩ ⊆ J₀(ℓ)(ℚ) has order exactly n (Ogg's theorem; divisor-class computation on the modular curve, interface to D2/D3) | M (given D2/D3) |
| E5a | Upper bound: 𝕋/𝕀 is killed by n (Eisenstein/cusp-form congruence mod p for p ∣ n via the mod-p q-expansion principle, interface to a3/D5) | M |
| E5b | Lower bound: ℤ/n ↠ 𝕋/𝕀 via the action on C; conclude 𝕋/𝕀 ≅ ℤ/n | M |
| E6 | Multiplicity one / Gorenstein at Eisenstein primes 𝔓 (J[𝔓] is 2-dimensional over 𝕋/𝔓) — the deepest single step; if it resists, the Wake–Wang-Erickson pseudodeformation route (arXiv:1707.01894, p > 3) is the recorded alternative | M–L (split further at bead time: E6a statement + consumers, E6b proof) |

### 3.3 a5 — Chapter III descent

| Step | Statement | Grade |
|---|---|---|
| Q1 | Construction of the Eisenstein quotient J̃ (quotient of J₀(ℓ) by the abelian subvariety cut out by 𝕀-power kernels; needs abelian-variety quotient machinery shared with b2/A3-analogue) | M (given D3) |
| Q2 | J₀(ℓ), hence J̃, has good reduction outside ℓ and purely toric reduction at ℓ (Deligne–Rapoport fibre; interface to D2/D4) | M (given D2/D4) |
| Q3 | J̃[𝔓] is admissible (consumes E6 + G1–G2: the 𝔓-torsion's constituents over ℤ are ℤ/p's and μ_p's) | M |
| Q4 | Apply G6 ⇒ J̃(ℚ) is finite | S |
| Q5 | Transfer: non-cuspidal x ∈ X₀(ℓ)(ℚ) gives a torsion point of J̃ via [x − ∞]; feed D7b/D8 | S–M |

No step above requires analysis; every step is a finite algebraic argument over
the shared substrate. This satisfies the decomposition mandate: all three XL
components decompose into ≤ M steps modulo the substrate interfaces (with E6
flagged as the one step that may need one further split).

---

## 4. Recommendation

**Commit to D6a (Mazur's Eisenstein-quotient descent).** Reasoning:

1. **The fork only buys the rank-0 proof; D6b's price for it is b3+b4+b5.**
   Both routes pay for D1–D5 and D7 regardless. D6a's route-specific cost is
   ~3 algebraic XL blocks that decompose cleanly (§3). D6b's is an XL (modular
   L-functions) + an XL+ (Gross–Zagier: heights, Green functions, Rankin–Selberg,
   holomorphic projection — every ingredient absent from Mathlib and never
   formalized anywhere) + an XL (Kolyvagin–Logachev Euler system). GZ alone
   plausibly exceeds all of D6a's marginal cost.
2. **Reuse points the same way.** D6a's finite-flat/fppf stack is needed by the
   FLT main line anyway (`FLT/GroupScheme/FiniteFlat.lean` is already seeded for
   the R=T flat deformation conditions); D6b's Heegner/height/Euler-system stack
   has zero overlap with anything else in the campaign.
3. **Exposition coverage is asymmetric.** D6a has a lecture-granularity modern
   blueprint (Snowden Math 679 + Achenjang notes + Parson's isolated descent
   writeup + WWE as an a4 fallback). D6b's core (GZ) has no simplified
   d = 1-scale exposition — the modern treatments (Yuan–Zhang–Zhang) are *more*
   general and *harder*.
4. **d = 1 kills route (b)'s raison d'être.** Merel's machinery earns its keep
   for torsion over number fields of degree d > 1; over ℚ it reduces to Mazur's
   own setup with the rank-0 input swapped for strictly heavier machinery.

**Salvage from route (b):** b1 (Manin/modular symbols, winding element) is
Lean-friendly, Mathlib-upstreamable, and useful for D5/D7b computations —
recommend cutting it as an independent bead regardless of the fork decision.

**What would flip the recommendation:**
- An external, importable formalization of BSD-analytic-rank-0 machinery
  (Heegner points + Kolyvagin, or Kato's Euler system) appearing at usable
  maturity — none exists or is announced as of 2026-08.
- The fppf-over-Spec-ℤ infrastructure (a2) turning out to require full
  SGA-scale site theory beyond what Mathlib's flat topology can support, *and*
  simultaneously a cheap b4/b5 import materializing (both conditions; the first
  alone only re-grades a2, since b-route still needs Néron models and more).
- A campaign scope change that makes GZ/KL a deliverable in its own right
  (e.g., a BSD campaign), amortizing b4+b5 across campaigns.
- PQ4 re-basing does **not** affect this fork: any surviving ℓ ≥ 17 case needs
  D6a-or-D6b identically.

**Suggested next beads if the panel ratifies:** (i) freeze the D6a↔D8 interface
statement ("∃ quotient A of J₀(ℓ), Cot(A) ↪ Cot(J₀) Hecke-compatibly, A(ℚ)
finite") so D7/D8 work is fork-independent; (ii) cut G1–G4 (admissible groups)
as the first D6a work beads — they sit closest to existing
`FLT/GroupScheme/FiniteFlat.lean`; (iii) cut b1 (modular symbols) as a
Mathlib-upstream bead; (iv) PQ5 citation checks for Mazur II.9.7/II.16.6/III.3.1
before freezing E5/E6/Q4 statements.

## 5. Sources

- Mazur, Publ. Math. IHÉS 47 (1977) — numdam.org/item/PMIHES_1977__47__33_0
- Snowden, Math 679 (UMich, F2013), L01–L25 — public.websites.umich.edu/~asnowden/teaching/2013/679/; typed notes: Achenjang, mit.edu/~NivenT/assets/pdf/UMich_679_Notes.pdf
- Parson, *Mazur's Eisenstein Descent* — math.stanford.edu/~conrad/vigregroup/vigre03/eisendescent.pdf
- Cambridge Eisenstein-ideal study group (2020) — dpmms.cam.ac.uk/~jcsl5/mazur/mazur.html
- Wake & Wang-Erickson, *The rank of Mazur's Eisenstein ideal*, Duke 169 (2020) — arXiv:1707.01894
- Merel, Invent. 124 (1996); Rebolledo, Clay proceedings (claymath.org/wp-content/uploads/2022/03/cmip08c.pdf); Darmon, *Rational points on curves* (ibid.)
- Kolyvagin–Logachev, Algebra i Analiz 1 (1989); Gross–Zagier, Invent. 84 (1986); Kato, Astérisque 295 (2004); Weston, AWS Euler-systems notes — swc-math.github.io/notes/files/01Weston2.pdf
- Stein, *Torsion points on elliptic curves* survey — williamstein.org/Tables/Notes/20100508-sfu-torsion/20100508-stein-torsion.pdf
- Lean community blog, modular-forms post (Mathlib status: no Hecke operators; q-expansions/Hecke algebras WIP) — leanprover-community.github.io/blog/posts/modular-forms/
