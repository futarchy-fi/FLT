# Mazur chapter map — second independent pass (bead hub-lsb1u.2)

Cartographer B. Produced from the blueprint LaTeX sources, the Lean sources under
`FLT/`, and the literature only. The first mapper's output was deliberately not
consulted.

---

## 1. Where the blueprint invokes Mazur, and the weakest sufficient statement

### 1.1 Blueprint invocation sites (exact quotes)

**`blueprint/src/chapter/ch02reductions.tex:172-186`** (label `Mazur_Frey`, Lean name
`FreyPackage.mazur`):

> \begin{theorem}[Mazur]
>   If $\rho$ is the mod $p$ Galois representation associated to a Frey package
>   $(a,b,c,p)$ then $\rho$ is irreducible.
> \end{theorem}
> \begin{proof} \notready
>   This follows from a profound and long result of Mazur \cite{mazur-torsion} from
>   1977, namely the fact that the torsion subgroup of an elliptic curve over $\Q$
>   can have size at most~16. In fact there is still a little more work which needs
>   to be done to deduce the theorem from Mazur's result. A pre-1990 reference for
>   the full proof of this claim is Proposition~6 in~\S4.1 of~\cite{serreconj}.

**`blueprint/src/chapter/ch03freyold.tex:306-309`** (label `mazur`, the assumed
statement itself):

> \begin{theorem}\label{mazur}\notready Let $E$ be an elliptic curve over $\Q$.
>   Then the torsion subgroup of $E$ has size at most 16.
> \end{theorem}

**`blueprint/src/chapter/ch03freyold.tex:374-377`** (corollary
`Frey_curve_no_trivial_submodule`, first of the two places the bound is used):

> \begin{proof}\uses{mazur, Frey_curve_trivial_submodule}
>   We have just seen that in this case, the Frey curve has a point of order $\ell$.
>   It also has three points of order 2, meaning that its torsion subgroup has order
>   at least $4\ell\geq 20$, contradicting Mazur's theorem~\ref{mazur}.

**`blueprint/src/chapter/ch03freyold.tex:415-418`** (corollary
`Frey_curve_no_trivial_quotient`, second use, on the isogenous curve):

> \begin{proof}\uses{Elliptic_curve_quotient_by_finite_subgroup, mazur} $\rho$ has a
>   Galois-stable submodule $C$. The quotient curve $E/C$ now has a trivial
>   1-dimensional submodule, and also three points of order~2 (the images of the
>   three 2-torsion points in $E$). Hence the torsion subgroup of $E/C$ has order at
>   least $4\ell\geq 20$, again contradicting Mazur's theorem.

Ancillary mentions: `ch01introduction.tex:51,68` (overview), `ch02reductions.tex:5,14,237`
(reduction narrative), `ch04overview.tex:3`, and `chtopbestiary.tex:233-245`, which warns:

> At the time of writing (May 2024), Lean's algebraic geometry cannot get us through
> *the first sentence of Mazur's proof* […] Anyone interested in formalising Mazur's
> paper should make a formalisation of its first sentence their first milestone.

### 1.2 What the repo's Lean axiom actually says

**`FLT/Assumptions/Mazur.lean:105-106`**:

```lean
axiom Mazur_statement (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (AddCommGroup.torsion E⟮ℚ⟯ : Set E⟮ℚ⟯).ncard ≤ 16
```

Two things worth flagging:

1. As the implementation note at `Mazur.lean:96-101` admits, `ncard` returns the junk
   value 0 on infinite sets, so the axiom literally says "the torsion subgroup has
   size ≤ 16 **or is infinite**". Discharging it therefore also needs finiteness of
   torsion (easy: injectivity of torsion into a good reduction, or Nagell–Lutz — far
   below Mordell–Weil strength).
2. **The axiom is currently used nowhere.** `grep Mazur_statement` hits only its own
   declaration. The theorem the FLT proof actually consumes is
   `FreyPackage.mazur` (`FLT/FreyCurve/Mazur.lean:30-36`), stated as irreducibility of
   `E.galoisRep p` for a Frey package, and its proof is the universal escape hatch
   `knownin1980s` (the `axiom knownin1980s {P : Prop} : P` of
   `FLT/Assumptions/KnownIn1980s.lean`). So the ch03 chain (unramifiedness ⇒
   trivial character ⇒ torsion point ⇒ contradiction with `Mazur_statement`) is not
   yet wired up in Lean at all; the Mazur chapter's first deliverable is that wiring,
   independent of proving the axiom.

### 1.3 The weakest sufficient statement

The FLT route never needs the classification of the 15 torsion groups, and it never
needs the "≤ 16" bound for arbitrary curves. Tracing ch03: the bound is applied only
to curves that have **full rational 2-torsion** (the Frey curve
$y^2 = x(x-a^p)(x+b^p)$ and its ℓ-isogenous quotient $E/C$, which inherits the three
rational 2-torsion points) **and** a rational point of exact prime order
$\ell \ge 5$. Hence:

> **(W) For every prime ℓ ≥ 5, there is no elliptic curve $E/\mathbb{Q}$ with
> $E(\mathbb{Q}) \supseteq \mathbb{Z}/2 \times \mathbb{Z}/2$ and a rational point of
> order ℓ.**
>
> Equivalently: $\mathbb{Z}/2 \times \mathbb{Z}/2\ell$ never embeds in
> $E(\mathbb{Q})$; equivalently, the modular curve $X_1(2,2\ell)$ (full 2-level plus
> a point of order $\ell$) has no non-cuspidal rational points, for any prime
> $\ell \ge 5$.

Notes on exactly which torsion must be excluded, per prime:

- For $\ell = 5, 7$ the full-2-torsion hypothesis is **essential**: $\mathbb{Z}/5$,
  $\mathbb{Z}/7$ and $\mathbb{Z}/10$ all occur as rational torsion ($X_1(5)$,
  $X_1(7)$, $X_1(10)$ are rational curves with non-cuspidal points), so "no point of
  order ℓ" is false; only $\mathbb{Z}/2\times\mathbb{Z}/2\ell$ is excludable.
- For $\ell \ge 11$ the stronger and cleaner statement "$E/\mathbb{Q}$ has no
  rational point of prime order $\ell$" (i.e. $Y_1(\ell)(\mathbb{Q}) = \emptyset$
  for $\ell = 11$ and $\ell \ge 17$; for $\ell = 13$ this is Mazur–Tate) is true and
  can be used, discarding the 2-torsion bookkeeping.
- (W) is strictly weaker than the repo axiom: it says nothing about curves without
  full 2-torsion, nothing about the group structure, and nothing about composite
  torsion orders. Semistability of the Frey curve is *not* needed in the blueprint's
  torsion route (it is consumed earlier, in the unramifiedness nodes of ch03).

If (W) is proven, `Mazur_statement` should be **replaced** by (W) (or by the pair
of statements in nodes 3–4 below), and `FreyPackage.mazur` re-proved from it via the
already-blueprinted ch03 chain; proving the literal `ncard ≤ 16` axiom would be
strictly more work for no gain on the FLT route.

An alternative equally-weak packaging used in the modern Diophantine literature
(Freitas–Siksek, arXiv:1309.4748; and Serre [serre-duke-1987, §4.1 Prop. 6 —
theorem number unverified]) goes through isogenies instead of torsion: full
2-torsion plus a reducible $E[\ell]$ gives a non-cuspidal rational point on
$X_0(2\ell)$, ruled out by Mazur's isogeny theorem (Mazur 1978). That variant is
*not* weaker than (W) in formalization cost, and the blueprint's torsion route
avoids $X_0(2\ell)$ entirely, so this map follows the blueprint's route.

---

## 2. Statement inventory

Difficulty scale: S (days), M (weeks), L (months), XL (year+ / research-level
formalization). "unverified" marks theorem/section numbers I could not check against
the source text.

### Part A — glue: from (W) to `FreyPackage.mazur`

1. **A1. Torsion of an elliptic curve over ℚ is finite.** Torsion injects into
   $E(\mathbb{F}_q)$ for a prime $q$ of good reduction (or Nagell–Lutz). Needed to
   make `ncard`-style statements non-vacuous and for every rank-0 descent below.
   **M.** [Silverman AEC VII.3.1 / VIII.7.1 — numbers unverified]
2. **A2. $E[n](\overline{\mathbb{Q}}) \cong (\mathbb{Z}/n)^2$ and Galois action.**
   Already stated (with `sorry`) as `WeierstrassCurve.n_torsion_card` /
   `n_torsion_dimension` in `FLT/EllipticCurve/Torsion.lean:46-72`; ongoing work of
   D. Angdinata via division polynomials. **L** (in progress; external to this
   chapter but a hard blocker).
3. **A3. Quotient by a finite Galois-stable subgroup.** For $C \subset
   E(\overline{K})[\ell]$ Galois-stable of order ℓ, there is $E' = E/C$ over $K$ and
   an isogeny $E \to E'$ with kernel $C$, Galois-equivariantly surjective on
   $\overline{K}$-points. This is blueprint `Elliptic_curve_quotient_by_finite_subgroup`
   (`ch03freyold.tex:390`), flagged there as hard ("the proof above is a no-go right
   now"). Vélu's formulas give a concrete Weierstrass-equation route avoiding
   fppf quotients. **L.** [Vélu 1971; Silverman AEC III.4.12 — unverified]
4. **A4. 2-torsion of the quotient.** The three rational 2-torsion points of the
   Frey curve survive (injectively) in $E/C$ for ℓ odd, since $C$ has odd order.
   **S** given A3.
5. **A5. (W) ⇒ `FreyPackage.mazur`.** Assemble with the ch03 chain
   (`Frey_curve_reducible_structure`, `Frey_curve_trivial_submodule`, A3, A4): a
   reducible $\rho$ yields $E$ or $E/C$ with full 2-torsion and a point of order
   $\ell \ge 5$, contradicting (W). **S–M** (given the ch03 nodes, which belong to
   the Frey-curve chapter, not this one).

### Part B — descent toolbox (shared by all small-prime cases)

6. **B1. Reduction mod q injects prime-to-q torsion.** $E(\mathbb{Q})_{tors} \hookrightarrow
   \tilde{E}(\mathbb{F}_q)$ for good primes $q$ (formal-group kernel has no
   prime-to-$q$ torsion). **M.** [Silverman AEC VII.3.1 — unverified]
7. **B2. Rank-0 certification for specific rational elliptic curves by full
   2-descent.** Machinery: complete 2-descent over ℚ via the map
   $E(\mathbb{Q})/2E(\mathbb{Q}) \hookrightarrow (\mathbb{Q}^\times/\square)^2$ for
   curves with rational 2-torsion, plus finitely many explicit local computations.
   Does **not** need general Mordell–Weil if packaged as: "the odd part of
   $E(\mathbb{Q})$ maps into $\tilde{E}(\mathbb{F}_q)$" combined with point counts —
   see B3. **L** for the descent machinery; avoidable for our purposes (B3).
8. **B3. Cheap alternative to descent: two-prime point-count sieve.** For a fixed
   target curve $X$ (elliptic, rank 0), "no rational point of order ℓ" statements can
   often be certified by B1 alone: torsion injects into $X(\mathbb{F}_3)$ and
   $X(\mathbb{F}_5)$, and $\gcd$ of point counts kills order ℓ. This works whenever
   the needed statement is about *torsion* points of the moduli curve — which is the
   case for $X_1(11)$, $X_1(2,10)$, $X_1(2,14)$ **only if** their ranks are 0 and
   non-cuspidal points are torsion; the rank-0 input cannot be sieved away, so a
   one-off 2-descent per curve (three curves total) is still needed. **M per curve.**

### Part C — the small primes ℓ ∈ {5, 7, 11, 13}

9. **C1. ℓ = 5: no $E/\mathbb{Q}$ with $\mathbb{Z}/2\times\mathbb{Z}/10 \subseteq
   E(\mathbb{Q})$.** $X_1(2,10)$ is an elliptic curve (genus 1, conductor 20
   [unverified]) of rank 0 whose rational points are all cusps. Classical, pre-Mazur:
   Kubert's classification work for curves with rational 2-torsion. **M–L.**
   [Kubert, *Universal bounds on the torsion of elliptic curves*, Proc. LMS (3) 33
   (1976) 193–237 — specific case location unverified]
10. **C2. ℓ = 7: no $\mathbb{Z}/2\times\mathbb{Z}/14$.** Same shape via
    $X_1(2,14)$ (genus 1 [unverified]), rank 0, only cusps. **M–L.** [Kubert 1976 —
    unverified]
11. **C3. ℓ = 11: no rational point of order 11.** $X_1(11)$ is an elliptic curve
    (121b1 [unverified]) of rank 0 with 5 rational points, all cusps. Oldest hard
    case, fully classical. **M.** [Billing–Mahler, *On exceptional points on cubic
    curves*, J. LMS 15 (1940) 32–43 — unverified]
12. **C4. ℓ = 13: no rational point of order 13.** $X_1(13)$ has genus 2; its
    Jacobian has rank 0 and the argument is a (pre-Mazur) descent on a genus-2
    Jacobian — noticeably harder than C3 (needs at least an ad-hoc treatment of a
    specific genus-2 Jacobian, or Chabauty-flavoured reasoning). **L.**
    [Mazur–Tate, *Points of order 13 on elliptic curves*, Invent. Math. 22 (1973)
    41–49 — unverified]. Cheapening: 13 is a regular prime, see risk R3.

### Part D — the core: no rational point of prime order ℓ ≥ 17

This is where all known proofs go through the arithmetic of modular Jacobians.
Statement to prove: **$Y_1(\ell)(\mathbb{Q}) = \emptyset$ for prime $\ell \ge 17$**
(Mazur 1977; modern streamlining via Merel's winding quotient and Kamienny's
formal-immersion formulation, as exposited by Rebolledo and in Snowden's Math 679
course).

13. **D1. Modular curves $X_0(N)$, $X_1(N)$ as smooth proper curves over
    $\mathbb{Q}$,** with moduli interpretation and cusps. **XL** (nothing usable in
    Mathlib; the blueprint's bestiary chapter names this whole area as beyond
    current Lean AG). [Deligne–Rapoport 1973; Katz–Mazur 1985]
14. **D2. Integral models: $X_0(\ell)$ over $\mathbb{Z}$, good reduction away from
    ℓ, and the Deligne–Rapoport description of the fibre at ℓ** (two copies of
    $\mathbb{P}^1$ crossing at supersingular points). Needed for the reduction
    arguments and for D6. **XL.** [Deligne–Rapoport, Antwerp II — unverified]
15. **D3. Jacobians of curves as abelian varieties over $\mathbb{Q}$;** functorial
    points, Albanese maps $X \to J$, behaviour under base change. **XL** (no
    Jacobian varieties, no abelian varieties in Mathlib beyond elliptic curves).
    [Milne, *Jacobian varieties*, in Arithmetic Geometry]
16. **D4. Néron models of abelian varieties over $\mathbb{Z}$;** Néron mapping
    property, component groups; specialization $A(\mathbb{Q}) = \mathcal{A}(\mathbb{Z})$;
    injectivity of torsion specialization at odd good primes (and the char-2
    subtlety: kernel of reduction at 2 has only 2-power torsion, forcing arguments
    mod 3 or careful mod-2 work). **XL.** [BLR, *Néron Models*, 1990 — published
    1990, content pre-1990]
17. **D5. Hecke algebra $\mathbb{T}$ acting on $J_0(\ell)$; Eichler–Shimura
    relation $T_p = F + \langle p\rangle F'$ on the fibre at $p$.** **XL** (Hecke
    operators on modular Jacobians; Mathlib has no Hecke operators even on modular
    forms). [Snowden Math 679, Part II; Diamond–Shurman ch. 8 — unverified]
18. **D6. A rank-0 quotient $A$ of $J_0(\ell)$ in which $(0)-(\infty)$ remains
    nonzero.** Two known routes, both deep:
    - **D6a (Mazur's original): the Eisenstein quotient.** Define the Eisenstein
      ideal $\mathfrak{I} = (T_q - q - 1, \dots)$, prove
      $\mathbb{T}/\mathfrak{I} \cong \mathbb{Z}/n$ with $n = \text{num}((\ell-1)/12)$,
      and perform Mazur's descent to show the Eisenstein quotient
      $\tilde{J}^{(p)}$ has finite Mordell–Weil group. Self-contained
      algebro-geometric, but this is the 150-page core (Galois cohomology of finite
      flat group schemes over $\mathbb{Z}$, Raynaud's theorem on prolongations,
      admissibility arguments). **XL+.** [Mazur 1977, Chapters II–III — unverified]
    - **D6b (Merel's simplification): the winding quotient $J_e$.** Rank 0 follows
      from analytic non-vanishing $L(f,1)\ne 0$ plus Kolyvagin–Logachev ("analytic
      rank 0 ⇒ rank 0" for quotients of $J_0(N)$). Structurally simpler, but
      imports modularity of $J_0(\ell)$ factors (Eichler–Shimura theory of
      L-functions) **and** the Euler-system/Heegner-point machinery of
      Gross–Zagier + Kolyvagin–Logachev — an enormous analytic-arithmetic stack,
      and borderline for the repo's pre-1990 rule (Kolyvagin–Logachev is 1989).
      **XL+.** [Merel 1996; Rebolledo, *Merel's theorem…*, Clay proceedings;
      Darmon, *Rational points on curves*, Clay proceedings]
19. **D7. The formal immersion / Kamienny-style criterion.** The map
    $X_0(\ell) \to A$ (via $x \mapsto [x - \infty]$ composed to the rank-0
    quotient) is a formal immersion at $\infty$ in characteristic 2 (or 3);
    conclude: a rational point reducing to $\infty$ mod that prime *equals*
    $\infty$. Requires cotangent-space computations with q-expansions and Néron
    models. **L–XL** given D1–D6. [Mazur 1978 §4; Kamienny 1992; Rebolledo
    exposition — unverified]
20. **D8. Reduction step: a rational point of order ℓ ≥ 17 yields a non-cuspidal
    $x \in X_0(\ell)(\mathbb{Q})$ whose reduction mod 2 (resp. 3) is a cusp.**
    Uses: the curve $E$ acquires multiplicative or potentially-good reduction
    control from the ℓ-point being rational (Néron model of $E$, Tate curve at
    primes of multiplicative reduction, order-ℓ point cannot inject into small
    special fibres). **L.** [Mazur 1977 Ch. III / Snowden L20–L25 — unverified]
21. **D9. Assembly of Part D:** $Y_1(\ell)(\mathbb{Q}) = \emptyset$ for prime
    $\ell \ge 17$. **S–M** given D1–D8.
22. **W. Final assembly:** (W) from C1, C2, C3, C4, D9 (primes 5, 7 need the full
    2-torsion form; 11, 13, ≥17 use the stronger no-ℓ-torsion form). Then A5 gives
    `FreyPackage.mazur`, replacing the `knownin1980s` invocation at
    `FLT/FreyCurve/Mazur.lean:36` and retiring/replacing `Mazur_statement`. **S.**

Node count: **22** (A1–A5, B1–B3, C1–C4, D1–D9, W), of which 5 are XL-or-worse
(D1–D6 territory) and one (D6) is the singular research-scale wall.

---

## 3. Dependency edges

Internal edges (→ = "is used by"):

- A1 → B3, C1–C4, W (finiteness underlies every counting/sieve step)
- A2 → A3, A5 (need $E[\ell]$ 2-dimensional to talk about $\rho$, sub/quotient)
- A3 → A4 → A5;  A5 + W-statement → `FreyPackage.mazur`
- B1 → B3, D8;  B2 (or B3's per-curve descents) → C1, C2, C3;  B2-genus-2 variant → C4
- C1, C2, C3, C4, D9 → W
- D1 → D2, D3, D5, D7, D8;  D2 → D5, D6a, D7, D8;  D3 → D4, D6, D7
- D4 → D6a, D7, D8;  D5 → D6a, D6b;  D6 (a or b) → D7 → D9;  D8 → D9

External needs (other FLT-deferred chapters / repo):

- **ch03 Frey-curve nodes** (not part of this chapter, but `FreyPackage.mazur`
  consumes them): `frey_curve_unramified`, `frey_curve_at_2`,
  `Frey_curve_mod_ell_rep_at_ell`, `Frey_characters_*`,
  `Frey_curve_reducible_structure` (`ch03freyold.tex:303-388`) — the
  unramified-character and Minkowski steps. Minkowski's "no unramified extension of
  ℚ" is itself a deferred input (discriminant bounds; cf. `FLT/Assumptions/Odlyzko.lean`
  for the repo's pattern of assuming such bounds).
- **`FLT/EllipticCurve/Torsion.lean`** (Angdinata): `n_torsion_finite`,
  `n_torsion_card`, `n_torsion_dimension`, `galoisRep` — currently sorried; A2
  depends on this landing.
- **Tate curve / multiplicative reduction theory**: shared with ch03's
  `Frey_characters_at_ell` (Tate curve, canonical subgroup); D8 needs it too.
- **Finite flat group schemes over $\mathbb{Z}$** (D6a): the FLT project is
  developing group-scheme material for other chapters; heavy overlap, coordinate.
- **Mathlib**: everything in §4.

---

## 4. Mathlib coverage check (per major ingredient)

| Ingredient | Status | Namespace / evidence |
|---|---|---|
| Weierstrass/elliptic curves, group law (any char, affine + projective) | **exists** | `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point`, `…​.Projective.Point` (Angdinata–Xu, ITP 2023) |
| $E[n]$ structure, division polynomials, torsion finiteness | **partial** | sorried in FLT repo `FLT/EllipticCurve/Torsion.lean`; division polynomials partially in `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial` (extent unverified); Galois action scaffolding in FLT repo |
| Reduction mod p of elliptic curves, formal groups, torsion injection (B1) | **absent** | no Néron/minimal models, no reduction maps; formal group basics minimal |
| Mordell–Weil / rank-0 descent (B2) | **absent** | discussed on Zulip as a multi-year goal; nothing formalized |
| Nagell–Lutz | **absent** | no trace in Mathlib4 docs |
| Isogenies / quotient $E/C$, Vélu (A3) | **absent** | no isogeny theory beyond scalar multiplication |
| Modular forms, Eisenstein series, q-expansions | **partial** | `Mathlib.NumberTheory.ModularForms.*` (spaces, slash actions, `EisensteinSeries`, q-expansion basics); no Hecke operators, no Atkin–Lehner, no dimension formulas |
| Modular curves as $\mathbb{Q}$-schemes, cusps, moduli (D1–D2) | **absent** | only analytic $\mathbb{H}/\Gamma$-adjacent material (`Mathlib.NumberTheory.Modular`); no algebraic model, no Deligne–Rapoport |
| Jacobians of curves / abelian varieties (D3) | **absent** | `Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian` is *Jacobian coordinates*, not Jacobian varieties; no abelian-variety theory |
| Néron models, group schemes over Dedekind bases, Raynaud (D4, D6a) | **absent** | blueprint bestiary (`chtopbestiary.tex:240-242`) states Lean AG cannot yet state Mazur's first sentence; FLT repo is building finite flat group schemes, not yet in Mathlib |
| Étale cohomology | **absent** | sites/sheaves/derived categories exist (`Mathlib.CategoryTheory.Sites.*`, derived cats formalized); étale cohomology itself not defined (Banff cohomology blog post, 2023, still current as far as searches show) |
| L-functions of modular forms; Kolyvagin–Logachev / Gross–Zagier (D6b) | **absent** | only Dirichlet/`LSeries` analytic machinery (`Mathlib.NumberTheory.LSeries.*`) |
| Number-field basics for the descents (class groups, S-units, Minkowski bound) | **exists** | `Mathlib.NumberTheory.NumberField.ClassNumber`, `…​.Units`, Minkowski/discriminant bounds — supports B2/B3 and the ch03 Minkowski step |

Sources consulted: [Mathlib4 docs (EllipticCurve.Projective)](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Basic.html), [Angdinata–Xu ITP 2023](https://arxiv.org/abs/2302.10640), [Zulip "thoughts on elliptic curves"](https://leanprover-community.github.io/archive/stream/116395-maths/topic/thoughts.20on.20elliptic.20curves.html), [Lean community cohomology blog](https://leanprover-community.github.io/blog/posts/banff-cohomology/), [FLT project blog](https://leanprover-community.github.io/blog/posts/FLT-announcement/).

---

## 5. Route risks

- **R1 — The D-core is a research-scale wall with no Mathlib on-ramp.** Algebraic
  modular curves, Jacobians, Néron models and finite flat group schemes over ℤ are
  all absent; the blueprint itself concedes Lean cannot yet *state* Mazur's opening
  sentence. Any credible plan must treat D1–D4 as a multi-year prerequisite program
  shared with other FLT chapters (Shimura curves need much of the same), not as
  chapter-local work.
- **R2 — Fork in the road at D6, both prongs expensive.** Mazur's Eisenstein-quotient
  descent (D6a) is self-contained but is precisely the 150-page Grothendieck-school
  argument; Merel's winding quotient (D6b) is conceptually lighter but smuggles in
  Eichler–Shimura L-function theory plus Kolyvagin–Logachev (1989 — barely inside
  the repo's pre-1990 rule) and, transitively, Heegner-point/Gross–Zagier material.
  Choosing wrong late is the single biggest schedule risk; a decision spike (paper
  audit of both, before formalizing) is warranted.
- **R3 — Cheapening via already-formalized FLT cases.** The Frey package has
  $p \ge 5$ prime. FLT for the regular primes 5, 7 and 13 is already fully
  formalized in Lean (FLT-regular-primes project, arXiv:2410.01466). Rerouting the
  top-level reduction to dispose of $p \in \{5, 7, 13\}$ by citation would delete
  nodes C1, C2, C4 (the fiddly $X_1(2,10)$, $X_1(2,14)$, genus-2 $X_1(13)$ cases)
  and shrink (W) to "no rational point of prime order $\ell \ge 11$, $\ell \ne 13$"
  — with ℓ = 11 a genuinely small classical descent (C3). The XL core for
  $\ell \ge 17$ is untouched (irregular primes are unavoidable), but the surface
  area and the full-2-torsion bookkeeping disappear. Recommended.
- **R4 — Axiom-statement mismatch inside the repo.** `Mazur_statement` (torsion
  ≤ 16, with the `ncard`-junk "or infinite" reading) is currently dead code, and
  `FreyPackage.mazur` is proved by the universal `knownin1980s` axiom. Proving (W)
  does not literally discharge either; the chapter must include the Lean re-wiring
  (A5) and a decision with upstream (KMB) on replacing the axiom's statement —
  otherwise a formally proven (W) leaves the repo's assumption count unchanged.
- **R5 — Hidden cost in the "easy" glue.** A2 (torsion structure, division
  polynomials — currently sorried), A3 (quotient isogeny, which the blueprint
  itself flags as "a no-go right now"), and B1 (reduction/injection, needing
  minimal models and formal groups) are prerequisites for *every* branch including
  the cheapened one, and none exist in Mathlib. Budget for these first; they are
  also the highest-leverage upstreamable pieces.

---

## 6. Bibliography (route-level)

- B. Mazur, *Modular curves and the Eisenstein ideal*, Publ. Math. IHÉS 47 (1977)
  33–186. (Repo bib key `mazur-torsion`, `blueprint/src/FLT.bib:337`.)
- B. Mazur, *Rational isogenies of prime degree*, Invent. Math. 44 (1978) 129–162.
- J.-P. Serre, *Sur les représentations modulaires de degré 2 de
  Gal(Q̄/Q)*, Duke Math. J. 54 (1987) 179–230. (Repo bib key `serreconj`;
  irreducibility deduction at §4.1 Prop. 6 [unverified].)
- D. Kubert, *Universal bounds on the torsion of elliptic curves*, Proc. LMS (3) 33
  (1976) 193–237; sequel Compositio 38 (1979) 121–128.
- G. Billing, K. Mahler, J. LMS 15 (1940) 32–43 (order 11).
- B. Mazur, J. Tate, Invent. Math. 22 (1973) 41–49 (order 13).
- L. Merel, *Bornes pour la torsion des courbes elliptiques sur les corps de
  nombres*, Invent. Math. 124 (1996) 437–449.
- M. Rebolledo, *Merel's theorem on the boundedness of the torsion of elliptic
  curves*, Clay Math. Proc. (exposition of the winding-quotient method).
- H. Darmon, *Rational points on modular curves* (Clay summer school notes) —
  modern presentation of Mazur-via-winding-quotient.
- P. Michaud-Jacobs, *Mazur's isogeny theorem*, arXiv:2209.03153 — compact modern
  overview of the isogeny-side argument.
- A. Snowden, *A course on Mazur's theorem* (Math 679, Michigan, 2013) — the most
  formalization-friendly end-to-end exposition of the torsion theorem;
  lecture-by-lecture notes at umich.edu, consolidated PDF by N. Achenjang (MIT).
- N. Freitas, S. Siksek et al., *Criteria for irreducibility of mod p
  representations of Frey curves*, J. Théor. Nombres Bordeaux 27 (2015) 67–76
  (arXiv:1309.4748) — the $X_0(2\ell)$/$X_0(4\ell)$ packaging of (W).
