# Cyclic base change for GL(2) — second independent cartography pass

Bead: hub-lsb1u.5.2 (FLT-on-Lean campaign). Pass B, written independently of any
prior cartography output; sources: repo main working tree at /Users/kas/FLT,
literature via web verification (URLs checked 2026-08-14).

## 1. Grep evidence (repo main, quoted file:line)

Blueprint LaTeX:

- `blueprint/src/chapter/ch01introduction.tex:50-51` — "we will assume Langlands' cyclic base
  change theorem for $\GL_2$" (listed among the pre-1990 assumed inputs).
- `blueprint/src/chapter/ch04overview.tex:86-88` — "First one uses the Skinner--Wiles trick to
  reduce to the ``minimal case'', and this needs cyclic base change for $\GL(2)$ and also a
  characterisation of the image of the base change construction; this seems to need a
  multiplicity one result, which (because of our definition of ``modular'') will need
  Jacquet--Langlands as well."
- `blueprint/src/chapter/chtopbestiary.tex:212-214` — "The theorems I need are:
  Jacquet-Langlands for inner forms of $\GL_2$ over totally real fields, and multiplicity 1 for
  these inner forms. We also need cyclic base change plus classification of image, all for
  totally definite quaternion algebras, and we need automorphic induction from $\GL_1(K)$ to
  $\GL_2(F)$ when $K/F$ is a degree 2 totally imaginary extension."
- `blueprint/src/chapter/chtopbestiary.tex:91-97` — the consumer of solvability:
  `\begin{theorem}\label{Skinner_Wiles_CFT_trick}\uses{global_class_field_theory}` — existence of
  a **finite solvable Galois extension** $L/K$ realizing prescribed local extensions at a finite
  set of places, linearly disjoint from a given $K^{avoid}$.
- `blueprint/src/chapter/chtopbestiary.tex:214` — caveat: "There seems to be little point
  formalising the statements of the theorems if we cannot yet even formalise the definition of
  an automorphic representation properly."

Lean sources:

- `FLT/Assumptions/KnownIn1980s.lean:39` and `:69` — "Langlands on cyclic base change" is cited
  (twice) as a canonical example of what the `knownin1980s` axiom
  (`FLT/Assumptions/KnownIn1980s.lean:80`, `axiom knownin1980s {P : Prop} : P`) will cover; the
  file says the axiom is later to be replaced by "a much smaller list of mathematical statements
  (perhaps around ten)" — cyclic base change is clearly slated to be one of them.
- No Lean statement of automorphic base change exists anywhere. All `baseChange` hits are ring/
  module/adele-level: `FLT/Deformations/RepresentationTheory/GaloisRep.lean:213`
  (`GaloisRep.baseChange`, coefficient base change of Galois reps — a different notion),
  `FLT/DedekindDomain/FiniteAdeleRing/BaseChange.lean`, `FLT/DedekindDomain/Completion/BaseChange.lean`,
  `FLT/NumberField/AdeleRing.lean` / `FLT/NumberField/InfiniteAdeleRing.lean` (the
  `𝔸_K ⊗_K L ≅ 𝔸_L` machinery of `blueprint/src/chapter/AdeleMiniproject.tex:106` ff.),
  `FLT/KnownIn1980s/EllipticCurves/{ReductionBaseChange,TateCurveBaseChange}.lean` (elliptic
  curves). These are *infrastructure*, not the theorem.
- `FLT/AutomorphicForm/QuaternionAlgebra/Basic.lean` — the object the theorem must be stated
  about: `WeightTwoAutomorphicForm F D R` (locally constant `φ : Dˣ\(D ⊗ 𝔸_F^∞)ˣ → R`, trivial
  central character), plus `LevelStruct` (level `U`, character `χ`). One `knownin1980s` use at
  `:499` (finiteness of `[Δ_g : Fˣ]`, Voight 17.7.13).
- No occurrence of "trace formula", "Saito", "Shintani", "Arthur", or "Clozel" anywhere in
  blueprint or Lean sources — the analytic machinery is entirely absent from the repo.

## 2. Weakest sufficient statement

The repo needs base change only inside the Skinner–Wiles reduction to the minimal case, plus
one automorphic induction input for the 3-5 switch/potential-modularity leg. The weakest
statement that suffices:

> **(CBC-min)** Let $F$ be a totally real number field, $E/F$ a **totally real cyclic extension
> of prime degree** $\ell$ (arbitrary prime, including $\ell = 2$). Let $\pi$ be a cuspidal
> automorphic representation of $\GL_2/F$ that is **weight-2 discrete series at every infinite
> place** (equivalently, in repo terms after Jacquet–Langlands: an eigenform in
> `WeightTwoAutomorphicForm F D ℂ` for a/any totally definite quaternion algebra $D/F$). Then:
> (a) **existence**: there is a cuspidal-or-Eisenstein automorphic representation $\Pi = \mathrm{BC}_{E/F}(\pi)$
> of $\GL_2/E$, weight-2 at infinity, with $\mathrm{Satake}_w(\Pi)$ determined by
> $\mathrm{Satake}_v(\pi)$ via the norm map at every place $w \mid v$ unramified for both
> ($\alpha_w = \alpha_v^{f(w/v)}$); $\Pi$ is cuspidal unless $\pi$ is induced from a character
> of $E$.
> (b) **image characterisation (descent)**: a cuspidal weight-2 $\Pi$ on $\GL_2/E$ with
> $\Pi^\sigma \cong \Pi$ for a generator $\sigma$ of $\mathrm{Gal}(E/F)$ is $\mathrm{BC}_{E/F}(\pi)$
> for some $\pi$ on $\GL_2/F$ (unique up to twist by characters of $\mathrm{Gal}(E/F)$).

Notes on minimality:

- **Prime-cyclic only suffices.** The Skinner–Wiles trick consumes a *solvable* totally real
  extension (`Skinner_Wiles_CFT_trick`, chtopbestiary.tex:91); solvable = tower of prime-cyclic
  steps, and both existence and descent iterate up the tower. The gluing step (node 10 below)
  is soft. No non-prime cyclic degree is ever needed as a primitive.
- **Totally real fields only.** Every field in the modularity-lifting leg is totally real
  (ch04overview.tex:93 chooses $F$ totally real via Moret-Bailly). CM/imaginary base change is
  never needed.
- **Local conditions**: only Satake compatibility at unramified places is load-bearing for the
  "modular of level $\Gamma_1(S)$" bookkeeping in ch04overview Theorem (lines 75-77); full
  local base change at ramified places (Shintani local lifting) can be *omitted from the
  statement* if levels are tracked via "unramified outside $S$" — this is the main statement-
  slimming opportunity. Local-global at ramified places would force formalising local base
  change, a large extra cost.
- **Character/central-character twists**: trivial central character (fixed by the repo's
  `WeightTwoAutomorphicForm` definition) removes the Grössencharakter bookkeeping of the
  general statement.
- Because of the bestiary caveat (chtopbestiary.tex:214) the statement should be phrased on the
  **totally definite quaternion algebra side** (bestiary line 213 literally asks for "cyclic
  base change ... for totally definite quaternion algebras"), i.e. about Hecke eigensystems in
  `LevelStruct.form`, not about abstract automorphic representations — this is the only object
  the repo can currently express.

Separate, adjacent minimal input (same chapter, distinct node):

> **(AI-quad)** Automorphic induction $\GL_1(K) \to \GL_2(F)$ for $K/F$ degree-2 totally
> imaginary (chtopbestiary.tex:213-214): a Hecke character of $K$ with suitable infinity type
> induces a weight-2 cuspidal $\pi$ on $\GL_2/F$ with the expected Satake parameters.
> This is classical theta-series (Hecke 1926 / Jacquet–Langlands Ch. 12), *not* trace-formula
> machinery, and should be inventoried here but costed independently.

## 3. Node inventory

Route A (the only realistic proof route) is Langlands' twisted-trace-formula argument
([Langlands, *Base Change for GL(2)*, Ann. of Math. Studies 96, 1980, full text at IAS](https://publications.ias.edu/sites/default/files/book-ps.pdf);
also [UBC digital archive](https://www.sunsite.ubc.ca/DigitalMathArchive/Langlands/pdf/book-ps.pdf)),
with the Hilbert-modular special case done earlier by Saito (1975, twisted trace formula for
Hilbert modular forms) and Shintani (1979, local lifting); modern general-$n$ reference
[Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace Formula*, AM-120, 1989](https://www.degruyterbrill.com/document/doi/10.1515/9781400882403/html)
(prime-degree cyclic BC and automorphic induction for $\GL_n$); survey: Jacquet, "On the base
change problem: after J. Arthur and L. Clozel" (Oslo 1987). For the campaign the *statement* is
what gets formalized (as one of the ~10 post-`knownin1980s` axioms); the proof nodes are listed
for completeness and costed as if formalized.

Sizes: S ≲ 1 person-week, M ≲ 1 person-month, L ≲ 6 person-months, XL = multi-year.

1. **N1. Hecke eigensystem / "automorphic rep" on totally definite quaternion algebras** —
   Hecke operators on `LevelStruct.form`, eigencharacters, Satake parameter at unramified $v$.
   Statement-bearing substrate; partially exists (`FLT/AutomorphicForm/QuaternionAlgebra/Basic.lean`),
   Hecke action still to be built. **M**. [shared with JL and Galois-rep chapters]
2. **N2. Norm map on Satake parameters** — for $w \mid v$ unramified in cyclic $E/F$, the map
   $\alpha_v \mapsto \alpha_v^{f(w/v)}$ on unramified local parameters; pure bookkeeping once N1
   exists. **S**.
3. **N3. Statement node CBC-min(a) (existence of the lift)** — as in §2, on the quaternionic
   substrate; to be an axiom/`knownin1980s` successor with reference Langlands 1980 / Saito
   1975. Statement only. **S–M** given N1, N2 (M if cuspidal-vs-Eisenstein dichotomy is stated
   carefully, which requires expressing "induced from a quadratic character", i.e. depends on N9).
4. **N4. Statement node CBC-min(b) (descent / image characterisation)** — $\sigma$-invariance
   descent, uniqueness up to $\mathrm{Gal}(E/F)$-twist. Needs strong multiplicity one to even be
   well-posed on eigensystems. **S–M** given N1 and N7.
5. **N5. Local cyclic base change / Shintani lifting** (character identities, norm map on
   conjugacy classes $N: \GL_2(E_w) \to \GL_2(F_v)$) — needed only if ramified local-global
   compatibility is put in the statement; omitted under the slim statement of §2. **L** (proof
   XL-adjacent). *Recommend: exclude.*
6. **N6. Twisted trace formula for $\GL(2)$ + comparison** (elliptic/weighted/spectral terms,
   the analytic heart of Langlands 1980 chs. 6-11 / Saito 1975) — proof-only node. **XL**.
   [trace-formula core shared with Jacquet–Langlands — see §4]
7. **N7. Multiplicity one and strong multiplicity one for $\GL(2)$ / its inner forms** —
   explicitly demanded at ch04overview.tex:87 and chtopbestiary.tex:213. Statement M, proof
   (Whittaker/Kirillov theory, JL Prop. 11.1.1 + Casselman) L. **M/L**.
   [shared external node with JL chapter — bead hub-lsb1u.4]
8. **N8. Jacquet–Langlands transfer conjugation** — CBC is *stated* on quaternion algebras but
   *proved* on $\GL_2$; transporting the theorem across JL (both directions, level/eigensystem
   bookkeeping) is its own edge-node. **M** given JL. [shared: bead hub-lsb1u.4]
9. **N9. Automorphic induction AI-quad** ($\GL_1(K) \to \GL_2(F)$, $K/F$ quadratic totally
   imaginary; theta series route, Hecke/JL ch. 12; also the $n=1$ prime-cyclic case in
   Arthur–Clozel) — statement M; proof (Weil representation/theta or converse theorem) L–XL.
   **M** as statement node. [consumed by the potential-modularity leg — bead hub-lsb1u.9]
10. **N10. Solvable-from-prime-cyclic gluing** — iterate N3/N4 up a solvable tower; group
    theory (chief series of solvable groups have prime-cyclic quotients) + induction. Mathlib
    has the group theory. **S**.
11. **N11. Skinner–Wiles solvable-extension existence** (`Skinner_Wiles_CFT_trick`,
    chtopbestiary.tex:91) — the CFT-side consumer; blueprint node exists, `\notready`, depends
    on `global_class_field_theory`. **M** (given GCFT, itself a separate XL-track).
    [bead hub-lsb1u.10 for the CFT chapter edge]
12. **N12. Base-change compatibility with attached Galois representations** — the lifting-
    theorem application needs $\rho_{\mathrm{BC}(\pi)} \cong \rho_\pi|_{G_E}$; with Satake-level
    statements this is Chebotarev + compatible-family uniqueness against
    `compatible_family` (chtopbestiary.tex:222, formalised per chtopbestiary.tex:218-220,
    Farabella/Glasheen). **M**. [edge to Galois-representations chapter — bead hub-lsb1u.9]

Statement-only package (the realistic 2029 deliverable): N1, N2, N3, N4, N9-statement, N10,
N12 — with N6 and N5 axiomatised away and N7/N8/N11 imported from neighbouring beads.

## 4. Dependency edges

```
N1 ──> N2 ──> N3(CBC-a) ──> N10(solvable) ──> [Skinner–Wiles minimal-case reduction, ch04overview.tex:86]
N1 ──> N4(CBC-b) ──────────────┘
N7(mult one) ──> N4                     [shared external: JL bead hub-lsb1u.4]
N8(JL transfer) ──> N3, N4              [shared external: JL bead hub-lsb1u.4]
N6(twisted TF) ──> N3, N4 (proof only)  [trace-formula infra shared with JL's TF proof:
                                         orbital integrals, Selberg/Arthur truncation,
                                         local harmonic analysis on GL_2 — if either chapter
                                         ever proves its theorem, these are common XL subnodes]
N5(local BC) ──> N3 (only under fat statement — recommend cutting this edge)
N9(AI-quad) ──> [potential modularity / converse-theorem leg, ch04overview.tex:93-96]
                                        [cross-chapter: bead hub-lsb1u.9]
N11(SW CFT trick) ──> minimal-case reduction   [cross-chapter to CFT: bead hub-lsb1u.10]
N12 ──> [modularity-lifting bookkeeping]       [cross-chapter: bead hub-lsb1u.9]
```

Trace-formula overlap with Jacquet–Langlands: JL for inner forms (chtopbestiary.tex:212) and
CBC (Langlands 1980) both run on the Selberg/twisted trace formula for $\GL_2$; the shared
external nodes are (i) local orbital-integral theory and transfer, (ii) the coarse trace
formula for $\GL_2$ over a number field, (iii) mult-one input N7. These should be owned once,
JL-side (hub-lsb1u.4), with CBC consuming; under the statement-only plan neither chapter
instantiates them and the sharing is moot but must be recorded to avoid double-counting XL cost.

## 5. Mathlib / repo anchors (from inspection)

- Substrate: `FLT/AutomorphicForm/QuaternionAlgebra/Basic.lean` (`WeightTwoAutomorphicForm`,
  `LevelStruct`, `LocalLevelStruct`, double-coset machinery, `knownin1980s` at :499).
- Adele base change $\mathbb{A}_F \otimes_F E \cong \mathbb{A}_E$ — needed to even write the
  map on adelic points: `FLT/DedekindDomain/FiniteAdeleRing/BaseChange.lean`,
  `FLT/DedekindDomain/Completion/BaseChange.lean`, `FLT/NumberField/AdeleRing.lean`,
  `FLT/NumberField/InfiniteAdeleRing.lean`; blueprint
  `AdeleMiniproject.tex:106` ff. (largely done — genuine head start).
- Galois-side base change (restriction of Galois reps to $G_E$) already exists as
  `GaloisRep.baseChange`/`map` machinery: `FLT/Deformations/RepresentationTheory/GaloisRep.lean:213,244`.
- Compatible families: formalised per chtopbestiary.tex:218-220 (`compatible_family`, :222) —
  anchor for N12.
- Axiom mechanism: `FLT/Assumptions/KnownIn1980s.lean:80` (`axiom knownin1980s`), with CBC
  named at :39/:69 as a headline intended use.
- Mathlib: solvable-group chief-series/prime-cyclic-quotient material exists
  (`IsSolvable`, derived series; cf. repo's own `FLT/Mathlib/FieldTheory/Galois/Basic.lean:45-46`
  using `Algebra.IsQuadraticExtension.isCyclic`); nothing automorphic-representation-shaped in
  Mathlib at all.

## 6. Risks

1. **Definition debt (highest)** — chtopbestiary.tex:214 says it explicitly: the statement
   cannot be written until Hecke eigensystems/Satake parameters on the quaternionic forms exist
   (N1). CBC is blocked behind that, as are JL and Galois-rep-attachment; slippage in N1 hits
   three chapters at once.
2. **Statement over-fattening** — importing the full Langlands/Arthur–Clozel statement (local
   BC at all places, central-character twists, general weight) drags in N5 and turns an M
   deliverable into L+. The slim CBC-min of §2 must be checked *now* against the exact
   Skinner–Wiles usage in the eventual Lean proof of the ch04 lifting theorem, or a mid-project
   restatement is likely.
3. **Descent well-posedness** — CBC-min(b) on eigensystems silently requires strong
   multiplicity one (N7); if the JL bead descopes mult-one, this bead inherits an L node.
4. **Cuspidal/Eisenstein edge case** — $\pi$ induced from a character of $E$ base-changes to a
   non-cuspidal $\Pi$; the repo's cuspidal-only quaternionic substrate (totally definite $D$
   sees only cuspidal) partly hides this, but the descent direction must exclude/handle
   $\sigma$-invariant Eisenstein data. Easy to state wrongly.
5. **Proof horizon** — if the post-2029 phase ever demands proofs, N6 is a genuine multi-year
   XL (twisted trace formula) with no Mathlib precursor; no alternative proof route exists
   (Galois-side arguments are circular here). Plan on permanent-axiom status with an unusually
   careful paper reference (Langlands 1980 §§6-11 or Saito 1975 + Shintani 1979 for exactly the
   Hilbert case; Arthur–Clozel 1989 Ch. 3 for the modern write-up).

## 7. Size verdict

- **Statement-only (the campaign-relevant deliverable): M** — dominated by N1 (Hecke/Satake
  substrate, itself M and shared); CBC-specific increment on top of N1 is S–M (N2, N3, N4, N10,
  N12), plus M for AI-quad's statement (N9).
- **With ramified local-global compatibility in the statement: L** (adds N5 statement layer).
- **Full proof: XL** (N6; multi-year, no realistic path, keep as terminal axiom).

Recommendation: one axiom for CBC-min(a)+(b) phrased on quaternionic weight-2 eigensystems over
totally real fields, prime-cyclic totally-real extensions only, unramified-Satake compatibility
only; a second independent axiom for AI-quad; solvable case derived, not assumed.
