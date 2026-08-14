# Moret-Bailly (points on curves with prescribed local behavior) — cartography pass B

Bead: hub-lsb1u.8.2 (second independent pass). Sources: FLT repo working tree at
/Users/kas/FLT (blueprint LaTeX + Lean), Moret-Bailly 1989, Snowden's seminar notes,
Buzzard's survey, web-verified as noted. This pass did NOT read `cartography/`,
`cartography-b/` (pre-existing content), or any cartography/panel branches.

---

## 1. Where it lives in the repo (evidence)

**Blueprint statement** — `/Users/kas/FLT/blueprint/src/chapter/chtopbestiary.tex:253-271`:

> line 253: `We also need Moret-Bailly's theorem from~\cite{moret-bailly}:`
> line 255: `\begin{theorem}\label{moret-bailly}\notready Let $K^{\avoid}/K$ be a Galois extension of number fields. Suppose also`
> …local Galois extensions $L_v/K_v$ for $v\in S$ finite set of places; $T/K$ a smooth,
> geometrically connected curve; nonempty $\Gal(L_v/K_v)$-invariant open
> $\Omega_v\subseteq (L_v)$ [sic]; conclusion: finite Galois $L/K$ linearly disjoint from
> $K^{\avoid}$, with $L_w/K_v \cong L_v/K_v$ for $w\mid v\in S$, and a point
> $P\in T(L)$ with $P\in\Omega_v$.
> line 271: `Note that we do not even have the definition of a curve over a field in Lean.`

Two **blueprint typos** worth reporting upstream: line 258 has `$\Omega_v\subseteq (L_v)$`
(should be `T(L_v)`), and line 262 has a literal Unicode `∈` inside math mode
(`P ∈ T (L)`); line 263 `$\Omega_v\subseteq T (L_v) \cong (L_w)$` should end `T(L_w)`.

**Blueprint usage** — `/Users/kas/FLT/blueprint/src/chapter/ch04overview.tex`:

- line 27-28: `\item Moret--Bailly's result~\cite{moret-bailly} on points on curves with prescribed local behaviour;` (first item in the machinery list for potential modularity).
- line 71: label `moret-bailly` appears in the `\uses{...}` of `\label{modularity_lifting_theorem}` (lines 66-77). Note this is arguably a mis-attribution of the edge: MB is used in the *potential-modularity* step (line 93), not in the lifting theorem's proof itself; the blueprint currently has no separate node for potential modularity, so MB is hung off the lifting theorem.
- line 93: `the strategy to show potential modularity of $\rho$ is to use Moret--Bailly to find an appropriate totally real field $F$, an auxiliary prime $p$, and an auxiliary elliptic curve over $F$ whose mod $\ell$ Galois representation is $\rho$ and whose` (line 94) `mod $p$ Galois representation is induced from a character.`

**Commented-out edge** — `/Users/kas/FLT/blueprint/src/chapter/ch02reductions.tex:202`:
`%  \uses{modularity_lifting_theorem,frey_curve_hardly_ramified,moret-bailly}` (inside the
proof of `Wiles_Frey` = Lean `FLT.Bosses.B4_proof`).

**Bibliography** — `/Users/kas/FLT/blueprint/src/FLT.bib:64-79`: Moret-Bailly,
*Groupes de Picard et problèmes de Skolem. I, II*, Ann. Sci. ENS (4) 22 (1989), no. 2,
161-179 and 181-194. URL in bib verified live:
http://www.numdam.org/item?id=ASENS_1989_4_22_2_161_0 (confirmed: Part I, pp. 161-179,
DOI 10.24033/asens.1581; Part II pp. 181-194 linked from same page).

**Lean sources**: `grep -rni moret FLT/ *.lean` → **zero hits** outside the blueprint.
There is no Lean statement, stub, or assumption for MB anywhere.
- `/Users/kas/FLT/FLT/Proof.lean:98-99`: `theorem B4_proof : B4 := sorry` — the sorry
  under which the entire Wiles/Taylor-Wiles chain (including MB) currently sits.
- `/Users/kas/FLT/FLT/Assumptions/` contains only `KnownIn1980s.lean`, `Mazur.lean`,
  `Odlyzko.lean` — no MB assumption yet. `Assumptions/KnownIn1980s.lean` defines the
  `knownin1980s` tactic; its header (lines ~30-55) says phase 1 allows liberal use for
  any pre-1990 result, phase 2 shrinks to "perhaps around ten" explicitly stated
  assumptions. MB 1989 squeaks in under the pre-1990 bar and is an obvious member of
  that final list.

---

## 2. Weakest sufficient statement

Four candidate strengths, strongest to weakest:

- **MB-A (full Moret-Bailly 1989, Thm 1.3 of Skolem II)**: arbitrary smooth geometrically
  irreducible quasi-projective varieties (curves suffice by slicing) over a number field,
  full prescribed-local-extension conclusion. Overkill.
- **MB-B (blueprint bestiary form = Taylor's variant)**: smooth geometrically connected
  **curve** $T$ over a number field $K$; finite set $S$ of places **including archimedean
  ones** (essential: totally-realness of $L$ is imposed by taking $L_v=K_v=\mathbb R$,
  $\Omega_v \subseteq T(\mathbb R)$ at real places); prescribed finite Galois $L_v/K_v$
  at $v \in S$; Galois-invariant nonempty open $\Omega_v \subseteq T(L_v)$; conclusion
  gives Galois $L/K$ with prescribed local behavior, linearly disjoint from a fixed
  $K^{\mathrm{avoid}}$, and $P \in T(L)$ landing in every $\Omega_v$. This is the form in
  Taylor's *Remarks on a conjecture of Fontaine and Mazur* (J. Inst. Math. Jussieu 1
  (2002)), Prop. 2.1 [citation not URL-verified; paywalled].
- **MB-C (Snowden's split form)**: Snowden, *Potential modularity and applications*,
  Stanford modularity lifting seminar (2009-10), **Theorem 9** — URL verified and read:
  http://virtualmath1.stanford.edu/~conrad/modseminar/pdf/L26.pdf . Statement: $X$ smooth
  geometrically irreducible variety over number field $F$, finite $S$, finite Galois
  $L_v/F_v$, nonempty open $U_v \subseteq X(F_v)$ [for the $v$-adic topology on
  $X(L_v)$]; there exists finite Galois $F'/F$ which **splits over each $L_v$** and
  $x \in X(F')$ landing in $U_v$ under any map $F' \to L_v$. Weaker conclusion than MB-B
  (splitting rather than local isomorphism type; linear-disjointness obtained by adding
  auxiliary split places to $S$, cf. Snowden's proof of his Prop. 10, last paragraph).
  This suffices for the whole potential-modularity argument.
- **MB-D (application-shaped corollary, curve-free interface)**: Snowden **Prop. 10 /
  Thm. 14** shape, specialized to the FLT blueprint's use (ch04overview.tex:93-98):
  *Given the hardly-ramified irreducible $\bar\rho: G_{\mathbb Q}\to\GL_2(\mathbb Z/\ell)$
  (cyclotomic determinant), a fixed finite extension $K^{\mathrm{avoid}}$ to avoid, and an
  auxiliary prime $p$, there exist a totally real $F$ (even degree, Galois over
  $\mathbb Q$, unramified at $\ell$, linearly disjoint from $K^{\mathrm{avoid}}$) and an
  elliptic curve $E/F$ with $E[\ell] \cong \bar\rho|_{G_F}$, $E[p]$ induced from a
  character (dihedral), and $E$ ordinary with good reduction at places above $\ell$ and
  $p$.* This hides the twisted modular curve $Y(\bar\rho_\ell,\bar\rho_p)$, its geometric
  connectedness (Weil-pairing twist of a component of $Y(\ell p)$), and the openness of
  the good-ordinary locus **inside the opaque node**, along with MB itself.

**Verdict on weakest sufficient**: for the *campaign interface*, MB-D is the weakest
statement that discharges the blueprint's only use of MB. For a *reusable bestiary node*
(what `\label{moret-bailly}` is), MB-C over curves with archimedean places allowed and an
avoidance field is the weakest honest form; MB-B as currently written in the bestiary is
fine and equivalent in practice. Fields: number fields $K$ (applied with
$K=\mathbb Q$ or a preliminary totally real $F$); curves: smooth geometrically connected
quasi-projective curves (the only instance needed is one twisted modular curve per
$(\bar\rho, \ell, p)$); local conditions: real places (force totally real + oddness
compatibility), places over $\ell$ and $p$ (good ordinary reduction opens, unramifiedness
/prescribed splitting), finitely many auxiliary split places (linear disjointness).

References for the modern expositions (URL-verified):
- Snowden, *Potential modularity and applications* (Thm 9, Prop 10, Thm 14, Thm 15):
  http://virtualmath1.stanford.edu/~conrad/modseminar/pdf/L26.pdf ✓ fetched, read.
- Buzzard, *Potential modularity — a survey*, arXiv:1101.0097 ✓ abstract page fetched
  (title/author confirmed; recommends Snowden's write-up).
- Taylor's 2018 Stanford course notes (by T. Feng), cited at ch04overview.tex:82:
  https://math.berkeley.edu/~fengt/249A_2018.pdf ✓ URL live (428KB PDF downloads;
  contents not page-verified in this pass).
- Moret-Bailly I/II on Numdam ✓ (above).
- NOT verified: Taylor, J. Inst. Math. Jussieu 1 (2002); Green-Pop-Roquette,
  *On Rumely's local-global principle*, Jahresber. DMV 97 (1995) (alternative proof
  route via "large fields"); Harris-Shepherd-Barron-Taylor Ann. of Math. 171 (2010)
  (another standard home of the MB variant, their Prop. 2.1).

---

## 3. Numbered node inventory

Sizes: S (≤ 1 wk), M (≤ 1 person-month), L (≤ 6 person-months), XL (> 6 person-months /
research-level formalization). Status against Mathlib as of the repo's pin
(lake-manifest.json: mathlib rev `bc06ce9f87cda9bf825ecab192b115685e629898`).

**Statement-side infrastructure**

1. **MB0 — Curves over a field**: smooth, quasi-projective/proper, geometrically
   connected curve over $K$; base change; function field. Mathlib has schemes, smooth
   morphisms (`AlgebraicGeometry.Smooth`, `SmoothOfRelativeDimension` in
   `Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean` — verified via code search) and
   `FunctionField` (`Mathlib/NumberTheory/FunctionField.lean` — docs verified), but no
   usable "curve over K" API (divisors, genus, properness bookkeeping for curves).
   Blueprint itself flags this (chtopbestiary.tex:271). **Size: L** (statement-grade
   subset: M).
2. **MB1 — $v$-adic topology on $T(L_v)$ and local points**: $T(L_v)$ as a topological
   space / analytic manifold over a local field; smoothness ⟹ implicit-function-theorem
   /Hensel openness; nonemptiness statements for opens. Repo has Henselian rings
   (`/Users/kas/FLT/FLT/HenselianLocalRing/`) and completions
   (`/Users/kas/FLT/FLT/NumberField/Completion/`). **Size: M-L.**
3. **MB2 — Statement node** (bestiary `moret-bailly`, form MB-B or MB-C): formalizable
   once MB0+MB1 exist. **Size: M** (statement only, given infrastructure).

**Proof-side (only if MB is ever proved, not just assumed)**

4. **MB3 — Weak approximation** for finitely many inequivalent places of $K$. **In
   Mathlib**: `AbsoluteValue.denseRange_algebraMap_pi` ("the abstract weak approximation
   theorem") and the separating lemma `AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv`
   in `Mathlib/Analysis/AbsoluteValue/Equivalence.lean`, plus
   `NumberField.InfinitePlace.denseRange_algebraMap_pi` — verified against mathlib4 docs.
   **Size: S** (glue only).
5. **MB4 — Krasner / continuity of roots**: nearby algebraic points generate the
   prescribed local extensions. **In Mathlib**: `IsKrasner` in
   `Mathlib/Analysis/Normed/Field/Krasner.lean` (verified via code search). **Size: M**
   (the transfer lemma "point close $v$-adically ⟹ same completion type" still needs
   assembling).
6. **MB5 — Linear disjointness + Chebotarev-flavored avoidance**: choose auxiliary split
   places so $L$ avoids $K^{\mathrm{avoid}}$ (Snowden's Prop. 10 endgame uses
   Frobenius elements generating $\Gal(M/F)$). Mathlib has `LinearDisjoint`
   (`Mathlib/FieldTheory/LinearDisjoint.lean`, `Mathlib/RingTheory/DedekindDomain/LinearDisjoint.lean`
   — verified); **Chebotarev density is not in Mathlib** (FLT's CFT track is adjacent but
   not sufficient). **Size: L** (Chebotarev alone is L).
7. **MB6 — Heart of MB 1989**: arithmetic models of $T$ over $\mathcal O_K$, Picard
   groups of arithmetic surfaces, ample line bundles, sections with prescribed
   avoidance (Skolem problems I §1-2, II Thm 1.3); alternatively the Green-Pop-Roquette
   "large fields"/Rumely local-global route. Either way this is research-level
   arithmetic geometry with no Mathlib substrate (no models over Dedekind bases, no
   Riemann-Roch for curves, no capacity theory). **Size: XL.**
8. **MB7 — Assembly** of MB2 from MB3-MB6. **Size: M.**

**Consumer-side (between MB and potential modularity — for edge accounting)**

9. **MB8 — Twisted modular curve $Y(\bar\rho_\ell, \bar\rho_p)$**: moduli of elliptic
   curves with prescribed mod-$\ell$ and mod-$p$ torsion + Weil-pairing compatibility;
   representability, smoothness, geometric connectedness (twist of a geometrically
   connected component of $Y(\ell p)$ — Snowden's Prop. 10 proof, ¶2). Repo groundwork:
   `/Users/kas/FLT/FLT/KnownIn1980s/EllipticCurves/WeilPairing.lean`, `Torsion.lean`.
   **Size: XL** (modular-curve geometry; overlaps the Shimura-variety debt at
   chtopbestiary.tex:246-251).
10. **MB9 — Good-ordinary locus is open and nonempty** in $Y(\overline F_v)$
    ($j$-invariant integrality/continuity argument, Snowden p. 4). **Size: M**, given
    MB8 and Tate curves (repo: `/Users/kas/FLT/FLT/TateCurve/`,
    `KnownIn1980s/EllipticCurves/TateCurve*.lean`, `GoodReduction.lean`).
11. **MB10 — Potential modularity assembly** (Snowden Prop. 10 → Thm 14/15; blueprint
    ch04overview.tex:93-98): consumes MB2 (or directly MB-D), MB8, MB9, plus the
    modularity lifting theorem, dihedral/CM modularity, Jacquet-Langlands. Out of scope
    for this bead except as the sole consumer edge.

**Node count: 11** (MB0-MB10; 3 statement-side, 5 proof-side, 3 consumer-side).

---

## 4. Dependency edges

```
MB2 (statement) ─── needs ──→ MB0 (curves), MB1 (v-adic points)
MB7 (proof)     ─── needs ──→ MB2, MB3 (weak approx), MB4 (Krasner), MB5 (disjointness/Chebotarev), MB6 (MB-1989 heart)
MB-D (corollary interface) ── needs ──→ MB2 + MB8 + MB9   [or is itself the opaque node]
MB10 (potential modularity) ─ needs ──→ MB-D, modularity_lifting_theorem, JL, CM-modularity
blueprint: modularity_lifting_theorem \uses moret-bailly   (ch04overview.tex:71 — edge is
  really MB → potential modularity; flag for blueprint graph hygiene)
Wiles_Frey (B4_proof, Proof.lean:98) ⟵ ultimately ── MB10  (commented edge ch02reductions.tex:202)
```

Mathlib-anchored leaves (exist today): MB3 (whole), MB4 (core), MB5 (LinearDisjoint
half). Missing substrate: curve API (MB0), Chebotarev (MB5), everything in MB6, MB8.

---

## 5. Mathlib anchors (verified this pass)

| Need | Anchor | Status |
|---|---|---|
| Weak approximation | `AbsoluteValue.denseRange_algebraMap_pi`, `AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv`, `NumberField.InfinitePlace.denseRange_algebraMap_pi` (`Mathlib/Analysis/AbsoluteValue/Equivalence.lean`) | present ✓ |
| Krasner | `IsKrasner` (`Mathlib/Analysis/Normed/Field/Krasner.lean`) | present ✓ |
| Linear disjointness | `Mathlib/FieldTheory/LinearDisjoint.lean`, `Mathlib/RingTheory/DedekindDomain/LinearDisjoint.lean` | present ✓ |
| Smooth morphisms of schemes | `AlgebraicGeometry.Smooth`, `SmoothOfRelativeDimension` (`Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean`) | present ✓ |
| Function fields | `FunctionField` (`Mathlib/NumberTheory/FunctionField.lean`) | present ✓ (one-variable, not curve-linked) |
| Adeles/completions | `IsDedekindDomain.FiniteAdeleRing` (used at ch04overview.tex:69); repo `FLT/NumberField/AdeleRing.lean` | present ✓ |
| Curves over K (proper smooth, geom. connected, divisors, RR) | — | **absent** |
| Models over $\mathcal O_K$ / arithmetic surfaces / Picard | — | **absent** |
| Chebotarev density | — | **absent** |
| Modular curves with level structure | — | **absent** (repo has Weil pairing / torsion groundwork under `FLT/KnownIn1980s/EllipticCurves/`) |

---

## 6. Risks and size verdict

- **Overall size (full formalization of MB-B/MB-C with proof): XL.** MB6 alone is
  research-level (arithmetic surfaces + Picard-group Skolem machinery, or GPR large
  fields — neither has any Mathlib substrate). MB8 (the consumer's twisted modular
  curve) is a second, independent XL. This matches the expected XL verdict.
- **Statement-only cost is not small**: L-ish, because the honest statement quantifies
  over smooth geometrically connected curves and $v$-adic topologies on $T(L_v)$ (MB0 +
  MB1), which don't exist in Lean — the blueprint concedes this at
  chtopbestiary.tex:271. An opaque assumption is only as cheap as its statement.
- **Interface-shape risk**: an opaque MB-B node forces formalizing schemes-level curve
  API *just to state the assumption*, and then MB8/MB9 (XL again) must still be built to
  *use* it. An opaque MB-D node (auxiliary totally real field + elliptic curve with
  prescribed $\ell$- and $p$-torsion behavior) needs only objects already in or near the
  repo: elliptic curves over fields, torsion Galois reps
  (`FLT/EllipticCurve/Torsion.lean`), good/ordinary reduction
  (`FLT/KnownIn1980s/EllipticCurves/GoodReduction.lean`, `Flat.lean`), totally real
  fields, linear disjointness. Statement cost drops to S-M and it swallows MB6+MB8+MB9
  in one opaque bite.
- **Blueprint-graph risk**: the `moret-bailly` label is consumed only via the
  `\uses` of `modularity_lifting_theorem` (ch04overview.tex:71), which mislocates the
  dependency; when a potential-modularity node is added to the blueprint the edge should
  move there.
- **Precision risk**: bestiary statement has the `$\Omega_v\subseteq (L_v)$` typo and is
  silent on whether $S$ may contain archimedean places (it must, or totally-realness of
  $L$ is unobtainable) and on quasi-projectivity/properness of $T$. Any Lean statement
  should resolve these; Snowden Thm 9 is the cleanest template.
- **Attribution risk (low)**: MB 1989 is pre-1990, so the `knownin1980s` posture
  (`FLT/Assumptions/KnownIn1980s.lean`) covers it, and the *variant* with avoidance
  is standard-expert material (Taylor 2002; HSBT 2010) — acceptable under the repo's
  phase-1 rules, but the phase-2 "final ten assumptions" list should cite MB 1989
  Thm 1.3 (Skolem II) plus Taylor's Prop. 2.1 explicitly.

### Posture recommendation

**Yes to an opaque-assumption interface, but at the MB-D altitude, with MB2 (statement M,
the bestiary MB-B/MB-C form) kept as a blueprint-only node for now.** Concretely:

1. Phase 1 (now): state **MB-D** in Lean under `FLT/Assumptions/` (or discharge with
   `knownin1980s` + literature comments citing Moret-Bailly 1989 I/II, Taylor 2002,
   Snowden's notes, Buzzard's survey). This is the weakest statement sufficient for
   ch04overview.tex:93-98 and is statable with ≤ M effort today.
2. Keep the bestiary `moret-bailly` node (MB2) as the mathematically honest reusable
   statement in LaTeX; do not attempt to state it in Lean until a curve API lands
   (tracked by MB0). Fix the two typos and the archimedean-places ambiguity.
3. Treat MB6 and MB8 as permanently-out-of-scope XL beads for this campaign unless the
   Shimura-variety track (chtopbestiary.tex:246-251) independently builds modular-curve
   geometry, in which case MB8/MB9 can be revisited and MB-D refined toward MB2 + proof
   of the reduction.

This matches the repo's own two-phase doctrine (Assumptions/KnownIn1980s.lean): liberal
opaque use now, a small explicit assumption list later — MB-D is the right shape for
membership in that final list; full MB-B with proof is a separate multi-year project.
